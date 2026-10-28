-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:04.176329+00:00
-- url     : https://prove2.me/submissions/fac8ba59-940f-463e-a2ff-b5194ab6453b

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Theorems.Thm_FunctionalInequalities_Analysis_inner_iteratedFDeriv_gradient_apply_readable
import Theorems.Thm_FunctionalInequalities_Analysis_iteratedFDeriv_sub_const_of_pos_readable

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section CompactSupport
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
/-- A law with compact support has every exponential moment. -/
theorem FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_exp (μ : Measure F) [IsFiniteMeasure μ]
    (hc : IsCompact μ.support) (r : ℝ) : Integrable (fun x => Real.exp (r * ‖x‖)) μ := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : F)
  refine (integrable_const (Real.exp (|r| * max R 0))).mono' (by fun_prop) ?_
  filter_upwards [μ.support_mem_ae] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    r * ‖x‖ ≤ |r| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |r| * max R 0 := by
      gcongr
      exact (by simpa using hR hx : ‖x‖ ≤ R).trans (le_max_left _ _)
end CompactSupport
section GradientJets
omit [BorelSpace E] in
/-- Literal scalar-cumulant meaning of `cumulantVector`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.cumulantVector_inner (μ : Measure E) (hs : List E) (w : E) :
    ⟪cumulantVector μ hs, w⟫ =
      cumulant μ (hs.length + 1) (Fin.snoc (fun i => hs.get i) w) := by
  rw [cumulantVector, InnerProductSpace.toDual_symm_apply,
    ContinuousMultilinearMap.curryRight_apply]
/-- **Jets of the centred CGF gradient are the cumulant Riesz vectors**: for `r ≥ 1`,
`Dʳ(∇Λ − ∇Λ(0))(0)[h] = cumulantVector μ (List.ofFn h)`, i.e. `⟪Dʳv(0)[h], w⟫ = κ_{r+1}(h, w)`. -/
theorem solution (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (r : ℕ) (hr : 1 ≤ r) (h : Fin r → E) :
    iteratedFDeriv ℝ r (fun z : E =>
      gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) z - gradient (FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)) 0) 0 h =
      FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) (List.ofFn h) := by
    have : CompleteSpace E := FiniteDimensional.complete ℝ E
    let Λ : E → ℝ := FunctionalInequalities.Analysis.BakryEmery.logLaplace (μ : Measure E)
    have hΛ : ContDiff ℝ ∞ Λ := by
      dsimp [Λ]
      exact FunctionalInequalities.Analysis.BakryEmery.contDiff_logLaplace _ (FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_exp _ hc)
    have hg : ContDiff ℝ ∞ (gradient Λ) := by
      change ContDiff ℝ ∞
        ((InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ Λ)
      exact
        (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.contDiff.comp
          (hΛ.fderiv_right (by simp))
    change
      iteratedFDeriv ℝ r
          (fun z : E => gradient Λ z - gradient Λ 0) 0 h =
        FunctionalInequalities.Analysis.BakryEmery.cumulantVector (μ : Measure E) (List.ofFn h)
    rw [FunctionalInequalities.Analysis.iteratedFDeriv_sub_const_of_pos_readable hg (gradient Λ 0) hr 0]
    apply ext_inner_right ℝ
    intro w
    rw [FunctionalInequalities.Analysis.inner_iteratedFDeriv_gradient_apply_readable hΛ r 0 h w,
      FunctionalInequalities.Analysis.BakryEmery.cumulantVector_inner]
    have haux :
        ∀ (n : ℕ) (hn : n = r) (g : Fin n → E),
          (∀ i, g i = h (Fin.cast hn i)) →
            FunctionalInequalities.Analysis.BakryEmery.cumulant (μ : Measure E) (n + 1) (Fin.snoc g w) =
              iteratedFDeriv ℝ (r + 1) Λ 0 (Fin.snoc h w) := by
      intro n hn g hg'
      subst n
      have hgeq : g = h := by
        funext i
        simpa using hg' i
      unfold FunctionalInequalities.Analysis.BakryEmery.cumulant
      dsimp [Λ]
      rw [hgeq]
    symm
    exact
      haux (List.ofFn h).length List.length_ofFn
        (fun i => (List.ofFn h).get i)
        (fun i => by
          simpa using (List.get_ofFn h i))
