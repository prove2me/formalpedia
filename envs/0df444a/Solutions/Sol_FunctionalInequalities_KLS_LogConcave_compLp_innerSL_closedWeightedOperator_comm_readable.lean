-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.compLp_innerSL_closedWeightedOperator_comm_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:24:31.030607+00:00
-- url     : https://prove2.me/submissions/b8b16365-6b73-4126-b0e2-c6f17aa20268

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Hessian
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_convexOn_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_seq_smooth_tendsto_weakHessian_readable

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
universe u
section Hessian
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The bilinear second Fréchet derivative of a `C²` real-valued function is symmetric. -/
theorem FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_symm {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (x v w : E) :
    bilinearIteratedFDerivTwo ℝ f x v w =
      bilinearIteratedFDerivTwo ℝ f x w v := by
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).iteratedFDeriv_cons
end Hessian
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Directional
/-- Mixed directional derivatives of a `C²` function commute (in directional form). -/
theorem FunctionalInequalities.Analysis.BakryEmery.fderiv_apply_comm {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fun y => fderiv ℝ f y v) x w := by
  rw [← bilinearIteratedFDerivTwo_eq_fderiv_apply hf, ← bilinearIteratedFDerivTwo_eq_fderiv_apply hf]
  exact bilinearIteratedFDerivTwo_symm hf x v w
end Directional
end DifferentialTools
end
end
end

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
section Hessian
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
/-- `⟪v, T̄ [f]⟫ = [∂ᵥ f]` for smooth compactly supported `f`. -/
private theorem FunctionalInequalities.KLS.LogConcave.compLp_innerSL_closedWeightedOperator_toLp {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (v : V) :
    (innerSL ℝ v).compLp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
        ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩) =
      (memLp_of_contDiff_hasCompactSupport ν (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hf v)
        (hfc.fderiv_apply ℝ v)).toLp (fun y => fderiv ℝ f y v) := by
  rw [hν.closedWeightedOperator_toLp_eq m hi hf hfc]
  refine Lp.ext ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLp (innerSL ℝ v)
      ((memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) hf hfc).toLp (gradient f)),
    (memLp_gradient_of_contDiff_hasCompactSupport (ν := ν) hf hfc).coeFn_toLp,
    (memLp_of_contDiff_hasCompactSupport ν (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty hf v)
        (hfc.fderiv_apply ℝ v)).coeFn_toLp] with x h1 h2 h3
  rw [h1, h2, h3, innerSL_apply_apply, real_inner_comm, inner_gradient_left]
omit [CompleteSpace V] in
include hν in
/-- The curvature bound `∇²U ≥ 0` of a log-concave tilted law with a `C²` potential. -/
private theorem FunctionalInequalities.KLS.LogConcave.zero_mul_le_bilinearIteratedFDerivTwo (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 2 U) (x v : V) :
    0 * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v := by
  rw [zero_mul]
  exact bilinearIteratedFDerivTwo_nonneg_of_convexOn hU
    (convexOn_of_eq_tilted_readable m hν hνU hU.continuous) x v
/-- **the weak Hessian estimate, symmetry of the weak Hessian.** Under the hypotheses of
`compLp_innerSL_mem_closedWeightedOperator_domain`, `⟪eⱼ, T̄ ∂ᵢ F⟫ = ⟪eᵢ, T̄ ∂ⱼ F⟫` in `L²(ν)`. -/
theorem solution
    (hνU : (ν : Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (F : (FunctionalInequalities.Analysis.Semigroup.adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (hD : ∀ i, (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (i j : Fin (Module.finrank ℝ V)) :
    (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hD i⟩) =
      (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hD j⟩) := by
  have hU2 : ContDiff ℝ 2 U := hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨fn, hfn, hfnc, -, -, hlim⟩ := FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_weakHessian_readable m hν hi hνU hUt
    (hU2.of_le (by norm_num)) hexp (FunctionalInequalities.KLS.LogConcave.zero_mul_le_bilinearIteratedFDerivTwo m hν hνU hU2) F
  have hc : ∀ (k : Fin (Module.finrank ℝ V)) {a : Lp V 2 (ν : Measure V)}
      {s : ℕ → Lp V 2 (ν : Measure V)}, Tendsto s atTop (𝓝 a) →
      Tendsto (fun n => (innerSL ℝ (stdOrthonormalBasis ℝ V k)).compLp (s n)) atTop
        (𝓝 ((innerSL ℝ (stdOrthonormalBasis ℝ V k)).compLp a)) := fun k a _ hs =>
    ((((innerSL ℝ (stdOrthonormalBasis ℝ V k)).compLpL 2
      (ν : Measure V))).continuous.tendsto a).comp hs
  have h1 := hc j (hlim i).2
  have h2 := hc i (hlim j).2
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  have hf2 : ContDiff ℝ 2 (fn n) := (hfn n).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [FunctionalInequalities.KLS.LogConcave.compLp_innerSL_closedWeightedOperator_toLp m hν hi
      (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty (hfn n) _) ((hfnc n).fderiv_apply ℝ _),
    FunctionalInequalities.KLS.LogConcave.compLp_innerSL_closedWeightedOperator_toLp m hν hi
      (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty (hfn n) _) ((hfnc n).fderiv_apply ℝ _)]
  exact MemLp.toLp_congr _ _ (Eventually.of_forall fun y =>
    FunctionalInequalities.Analysis.BakryEmery.fderiv_apply_comm hf2 y (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V j))
