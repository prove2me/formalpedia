-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.taylorTensor_gen_apply_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:25:22.958537+00:00
-- url     : https://prove2.me/submissions/94987965-6a1d-46c9-a046-5c40eaf4565c

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Tensor
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Domain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Tilt
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_contDiff_tiltAverage_of_memLp_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_expTilt_of_memLp_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_taylorTensor_succ_of_eq_inner_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_tiltAverage_adjointComp_eq_readable

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section Lp
section ScalarLp
omit [CompleteSpace E] [FiniteDimensional ℝ E]
section NormedSpace
variable {G : Type*}
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
section CompleteSpace
variable [CompleteSpace G]
omit [BorelSpace E] in
/-- Tilt averages only see the `μ`-class of a function: every tilt `μ_z` is absolutely
continuous with respect to `μ`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.tiltAverage_congr_ae (μ : Measure E) {f g : E → G} (hfg : f =ᵐ[μ] g) (z : E) :
    tiltAverage μ f z = tiltAverage μ g z := by
  unfold tiltAverage expTilt
  exact integral_congr_ae ((tilted_absolutelyContinuous μ _).ae_le hfg)
omit [BorelSpace E] in
/-- Taylor tensors only see the `μ`-class of a function. -/
theorem FunctionalInequalities.Analysis.BakryEmery.taylorTensor_congr_ae (μ : Measure E) {f g : E → G} (hfg : f =ᵐ[μ] g) (d : ℕ) :
    taylorTensor μ f d = taylorTensor μ g d := by
  unfold taylorTensor
  rw [show tiltAverage μ f = tiltAverage μ g from funext (tiltAverage_congr_ae μ hfg)]
end CompleteSpace
end NormedSpace
end ScalarLp
omit [FiniteDimensional ℝ E] in
/-- Pairing the tilt average of a vector class `G ∈ L²(μ; E)` with `w` is the tilt average of the
scalar class `⟪w, G⟫`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.inner_tiltAverage_Lp (μ : Measure E) [IsFiniteMeasure μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (G : Lp E 2 μ) (w z : E) :
    ⟪w, tiltAverage μ (⇑G) z⟫ = tiltAverage μ (⇑((innerSL ℝ w).compLpL 2 μ G)) z := by
  rw [tiltAverage_congr_ae μ ((innerSL ℝ w).coeFn_compLpL G) z]
  unfold tiltAverage
  simp only [innerSL_apply_apply]
  exact (integral_inner (integrable_expTilt_of_memLp_readable μ hexp (Lp.memLp G) z) w).symm
/-- The tilt average of a vector class `G ∈ L²(μ; E)` is smooth. -/
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_tiltAverage_Lp (μ : Measure E) [IsFiniteMeasure μ] [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) (G : Lp E 2 μ) :
    ContDiff ℝ ∞ (tiltAverage μ (⇑G)) := by
  let b := stdOrthonormalBasis ℝ E
  have h : tiltAverage μ (⇑G) =
      fun z => ∑ i, tiltAverage μ (⇑((innerSL ℝ (b i)).compLpL 2 μ G)) z • b i := by
    funext z
    simp_rw [← inner_tiltAverage_Lp μ hexp G _ z]
    exact (b.sum_repr' _).symm
  rw [h]
  exact ContDiff.sum fun i _ =>
    (contDiff_tiltAverage_of_memLp_readable μ hexp (Lp.memLp _)).smul contDiff_const
end Lp
end
end
end

section
noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
section NormedSpace
variable {G : Type*}
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
section NormedSpace
variable {G H : Type*}
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] [NormedAddCommGroup H]
variable [NormedSpace ℝ H] [CompleteSpace H]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Tilt averages commute with continuous linear maps (for integrable functions). -/
theorem FunctionalInequalities.Analysis.BakryEmery.clm_apply_tiltAverage (μ : Measure E)
    {g : E → G} (hg : ∀ z, Integrable g (expTilt μ z)) (L : G →L[ℝ] H) :
    (fun z => L (tiltAverage μ g z)) = tiltAverage μ (fun x => L (g x)) := by
    funext z
    unfold tiltAverage
    exact (L.integral_comp_comm (hg z)).symm
omit [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Taylor tensors commute with continuous linear maps. -/
theorem FunctionalInequalities.Analysis.BakryEmery.clm_comp_taylorTensor (μ : Measure E)
    {g : E → G} (hg : ∀ z, Integrable g (expTilt μ z)) (hF : ContDiff ℝ ∞ (tiltAverage μ g))
    (L : G →L[ℝ] H) (d : ℕ) :
    L.compContinuousMultilinearMap (taylorTensor μ g d) = taylorTensor μ (fun x => L (g x)) d := by
  have heq := clm_apply_tiltAverage μ hg L
  have hd : iteratedFDeriv ℝ d (fun z => L (tiltAverage μ g z)) 0 =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ d (tiltAverage μ g) 0) :=
    L.iteratedFDeriv_comp_left hF.contDiffAt
      (show (d : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  rw [heq] at hd
  ext v
  simp [taylorTensor, hd]
end NormedSpace
end NormedSpace
end
end
end

section
noncomputable section
open scoped LinearPMap
section
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
/-- Points of the domain of `T†T` are points of the domain of `T`. -/
theorem FunctionalInequalities.Analysis.Semigroup.mem_domain_of_mem_adjointComp_domain (T : H₀ →ₗ.[ℝ] H₁) (x : (adjointComp T).domain) :
    (x : H₀) ∈ T.domain :=
  x.2.2
end
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace
section General
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
variable {ν : MeasureTheory.ProbabilityMeasure V} (T : MeasureTheory.Lp ℝ 2 (ν : MeasureTheory.Measure V) →ₗ.[ℝ] MeasureTheory.Lp V 2 (ν : MeasureTheory.Measure V))
/-- The total gradient agrees with `T` on its domain. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_of_mem {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ T.domain) :
    weakGrad T u = T ⟨u, hu⟩ :=
  dif_pos hu
/-- The total generator agrees with `T†T` on its domain. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_of_mem {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain) :
    gen T u = adjointComp T ⟨u, hu⟩ :=
  dif_pos hu
variable [FiniteDimensional ℝ V]
end General
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped ContDiff RealInnerProductSpace ENNReal
section Generator
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
/-- **BKL Lemma 3.6 on the generator domain**: for `ν = m.tilted (-U)` with `U ∈ C¹` and all
exponential moments, and `F ∈ D(A)`, `T_{d+1}(A F) = S_{d+1} T_d(T̄ F)` for every `d`, the
original index of `T_d(T̄ F)` placed after its `d` Taylor indices. -/
theorem FunctionalInequalities.KLS.LogConcave.taylorTensor_adjointComp_eq (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 1 U)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (d : ℕ) :
    taylorTensor (ν : Measure V)
        (⇑(adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F))
        (d + 1) =
      symmetrizeML (appendInner (taylorTensor (ν : Measure V)
        (⇑(hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) d)) :=
  taylorTensor_succ_of_eq_inner_readable (ν : Measure V) (contDiff_tiltAverage_Lp _ hexp _)
    (funext fun z => tiltAverage_adjointComp_eq_readable m hν hi hνU hU hexp F z) d
end Generator
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
section Generic
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
/-- Pairing the vector Taylor tensor of `G ∈ L²(ν; V)` with `w` is the Taylor tensor of the scalar
class `⟪w, G⟫`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.innerSL_comp_taylorTensor_Lp
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (G : Lp V 2 (ν : Measure V)) (w : V) (d : ℕ) :
    (innerSL ℝ w).compContinuousMultilinearMap (taylorTensor (ν : Measure V) (⇑G) d) =
      taylorTensor (ν : Measure V) (⇑((innerSL ℝ w).compLp G)) d := by
  rw [taylorTensor_congr_ae _ ((innerSL ℝ w).coeFn_compLp G) d]
  exact clm_comp_taylorTensor _ (integrable_expTilt_of_memLp_readable _ hexp (Lp.memLp G))
    (contDiff_tiltAverage_Lp _ hexp G) (innerSL ℝ w) d
end Generic
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
include hνU hU hexp in
/-- **BKL Lemma 3.6 in coordinates**: for `u ∈ D(A)`, the entry of `T_{d+1}(A u)` at the basis
vectors `e_{i_0}, …, e_{i_d}` is the average over the permutations `τ` of `d + 1` positions of the
entry of `T_d(∂_{i_{τ d}} u)` at `e_{i_{τ 0}}, …, e_{i_{τ (d-1)}}`. -/
theorem solution {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T̄).domain)
    (d : ℕ) (i : Fin (d + 1) → Fin (Module.finrank ℝ V)) :
    FunctionalInequalities.Analysis.BakryEmery.taylorTensor (ν : Measure V) (⇑(FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ u)) (d + 1) (fun p => stdOrthonormalBasis ℝ V (i p)) =
      ((d + 1).factorial : ℝ)⁻¹ * ∑ τ : Equiv.Perm (Fin (d + 1)),
        FunctionalInequalities.Analysis.BakryEmery.taylorTensor (ν : Measure V) (⇑(FunctionalInequalities.KLS.LogConcave.PoissonIterate.partialDeriv T̄ (i (τ (Fin.last d))) u)) d
          (fun p => stdOrthonormalBasis ℝ V (i (τ (Fin.castSucc p)))) := by
  rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_of_mem _ hu, FunctionalInequalities.KLS.LogConcave.taylorTensor_adjointComp_eq m hν hi hνU (hU.of_le (by norm_num)) hexp
    ⟨u, hu⟩ d]
  simp only [FunctionalInequalities.Analysis.Tensor.symmetrizeML, smul_apply, sum_apply, ContinuousMultilinearMap.domDomCongr_apply,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.partialDeriv, FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_of_mem _ (FunctionalInequalities.Analysis.Semigroup.mem_domain_of_mem_adjointComp_domain _ ⟨u, hu⟩),
    ← FunctionalInequalities.KLS.LogConcave.PoissonIterate.innerSL_comp_taylorTensor_Lp hexp]
  simp only [FunctionalInequalities.Analysis.Tensor.appendInner, ContinuousMultilinearMap.uncurryRight_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  exact real_inner_comm _ _
