-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.exists_symm_normSq_grad0_step_sub_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:31:08.756244+00:00
-- url     : https://prove2.me/submissions/b6783feb-4ac6-4807-b6b1-11fcc052d2a7

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Domain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Defect
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_gradField_gradField_comp_swap_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_inv_le_scale_sq_step_readable
import Theorems.Thm_FunctionalInequalities_L2_inner_center_center_readable
import Theorems.Thm_FunctionalInequalities_L2_sum_norm_sq_compLp_innerSL_readable

section
noncomputable section
open MeasureTheory
section
variable {α : Type*} [MeasurableSpace α]
/-- Embedding constants into `L²` preserves addition. -/
@[simp]
theorem FunctionalInequalities.L2.const_add (μ : ProbabilityMeasure α) (c d : ℝ) :
    const μ (c + d) = const μ c + const μ d :=
  map_add (Lp.const 2 (μ : Measure α)) c d
/-- The mean preserves addition. -/
@[simp]
theorem FunctionalInequalities.L2.mean_add (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    mean μ (f + g) = mean μ f + mean μ g := by
  rw [mean, inner_add_left]
  rfl
/-- The mean preserves real scalar multiplication. -/
@[simp]
theorem FunctionalInequalities.L2.mean_smul (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (c • f) = c * mean μ f := by
  rw [mean, inner_smul_left]
  rfl
/-- Centering preserves addition. -/
@[simp]
theorem FunctionalInequalities.L2.center_add (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    center μ (f + g) = center μ f + center μ g := by
  simp only [center, mean_add, const_add]
  abel
/-- Centering commutes with real scalar multiplication. -/
@[simp]
theorem FunctionalInequalities.L2.center_smul (μ : ProbabilityMeasure α) (c : ℝ) (f : Lp ℝ 2 (μ : Measure α)) :
    center μ (c • f) = c • center μ f := by
  simp only [center, mean_smul, const_smul, smul_sub]
end
end
end

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace Classical
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ν : MeasureTheory.ProbabilityMeasure V} (T : MeasureTheory.Lp ℝ 2 (ν : MeasureTheory.Measure V) →ₗ.[ℝ] MeasureTheory.Lp V 2 (ν : MeasureTheory.Measure V))
omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- `normSq` is nonnegative. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_nonneg {k : ℕ} (u : Field ν k) : 0 ≤ normSq u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
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
/-- The total gradient of `0` is `0`. -/
@[simp]
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_zero : weakGrad T 0 = 0 := by
  rw [weakGrad_of_mem T T.domain.zero_mem]
  exact LinearPMap.map_zero T
/-- The total gradient is homogeneous, on and off the domain of `T`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_smul (c : ℝ) (u : Lp ℝ 2 (ν : Measure V)) :
    weakGrad T (c • u) = c • weakGrad T u := by
  by_cases hu : u ∈ T.domain
  · rw [weakGrad_of_mem T (T.domain.smul_mem c hu), weakGrad_of_mem T hu]
    exact LinearPMap.map_smul T c ⟨u, hu⟩
  · by_cases hc : c = 0
    · subst hc
      simp
    · have hcu : c • u ∉ T.domain := fun h => hu (by
        simpa [smul_smul, hc] using T.domain.smul_mem c⁻¹ h)
      simp [weakGrad, hu, hcu]
/-- `normSq` is quadratic: `‖c u‖² = c² ‖u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_smul {k : ℕ} (c : ℝ) (u : Field ν k) : normSq (c • u) = c ^ 2 * normSq u := by
  unfold normSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
variable [FiniteDimensional ℝ V]
/-- Parseval for the weak partial derivatives: `Σ_j ‖∂_j u‖² = ‖∇u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_norm_sq_partialDeriv (u : Lp ℝ 2 (ν : Measure V)) :
    ∑ j, ‖partialDeriv T j u‖ ^ 2 = ‖weakGrad T u‖ ^ 2 :=
  L2.sum_norm_sq_compLp_innerSL_readable (stdOrthonormalBasis ℝ V) (weakGrad T u)
/-- The energy of a field is the sum of the squared gradient norms of its components. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_eq_sum {k : ℕ} (u : Field ν k) :
    energy T u = ∑ I, ‖weakGrad T (u I)‖ ^ 2 := by
  unfold energy normSq gradField
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin (Module.finrank ℝ V)).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [Fin.consEquiv_apply, Fin.cons_zero]
  exact sum_norm_sq_partialDeriv T (u I)
/-- The energy is quadratic: `‖∇(c u)‖² = c² ‖∇u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_smul {k : ℕ} (c : ℝ) (u : Field ν k) : energy T (c • u) = c ^ 2 * energy T u := by
  rw [energy_eq_sum, energy_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Pi.smul_apply, weakGrad_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
end General
end
end

noncomputable section
open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace
section General
variable {α : Type*} [MeasurableSpace α] {ν : MeasureTheory.ProbabilityMeasure α}
/-- Centering does not increase the `L²` norm: `‖u - ∫u‖² ≤ ‖u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_center_sq_le (u : Lp ℝ 2 (ν : Measure α)) :
    ‖L2.center ν u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, L2.inner_center_center_readable]
  nlinarith [sq_nonneg (L2.mean ν u)]
/-- Centering is linear: `center (x - c y) = center x - c center y`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.center_sub_smul (x y : Lp ℝ 2 (ν : Measure α)) (c : ℝ) :
    L2.center ν (x - c • y) = L2.center ν x - c • L2.center ν y := by
  rw [sub_eq_add_neg, ← neg_smul, L2.center_add, L2.center_smul, neg_smul, ← sub_eq_add_neg]
end General
section Scale
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
  (T : MeasureTheory.Lp ℝ 2 (ν : MeasureTheory.Measure V) →ₗ.[ℝ] MeasureTheory.Lp V 2 (ν : MeasureTheory.Measure V))
/-- The normalizing coefficient `α` is nonnegative. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale_nonneg {k : ℕ} (h : Field ν k) : 0 ≤ scale T h := by
  unfold scale
  split_ifs
  exacts [le_rfl, Real.sqrt_nonneg _]
end Scale
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
  {C : NNReal} (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- A potential of temperate growth is `C²`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.contDiff_two (hUt : U.HasTemperateGrowth) : ContDiff ℝ 2 U :=
  hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)
/-- Centering componentwise is a contraction of `normSq`: for `α = scale h`,
`‖∇₀h' - α⁻¹ center ∇²h‖² ≤ ‖∇h' - α⁻¹ ∇²h‖²`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_step_sub_le {k : ℕ} (h : Field ν k) :
    normSq (grad0 T̄ (step T̄ h) -
        fun J => (scale T̄ h)⁻¹ • L2.center ν (gradField T̄ (gradField T̄ h) J)) ≤
      normSq (gradField T̄ (step T̄ h) - (scale T̄ h)⁻¹ • gradField T̄ (gradField T̄ h)) := by
  unfold normSq
  refine Finset.sum_le_sum fun J _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, grad0]
  rw [← center_sub_smul]
  exact norm_center_sq_le _
include hνU hUt hexp hC in
/-- **BKL Lemma 3.2 for one step**, with `λ = 1/C`. For a field `h` with components in `D(A)`,
`h' = α (-L)⁻¹ ∇₀h` is within `C χ` of a field symmetric in its first two index positions:
`S = α⁻¹ (∇²h - ∫∇²h)` (and `S = 0` when `α = 0`) satisfies `‖∇₀h' - S‖² ≤ C χ`. -/
theorem solution (hCpos : 0 < C) {k : ℕ} (h : FunctionalInequalities.KLS.LogConcave.PoissonIterate.Field ν k)
    (hh : ∀ I, h I ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T̄).domain) :
    ∃ S : FunctionalInequalities.KLS.LogConcave.PoissonIterate.Field ν (k + 2), (∀ J, S (J ∘ Equiv.swap 0 1) = S J) ∧
      FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h) - S) ≤ (C : ℝ) * FunctionalInequalities.KLS.LogConcave.PoissonIterate.defect T̄ h := by
  have hU := FunctionalInequalities.KLS.LogConcave.PoissonIterate.contDiff_two hUt
  refine ⟨fun J => (FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h)⁻¹ • FunctionalInequalities.L2.center ν (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ h) J),
    fun J => ?_, (FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_step_sub_le m hν hi h).trans ?_⟩
  · simp only [FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField_gradField_comp_swap_readable m hν hi hνU hUt hexp h hh J]
  have hdef : 0 ≤ FunctionalInequalities.KLS.LogConcave.PoissonIterate.defect T̄ h := FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_nonneg _
  rcases (FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale_nonneg (T̄) h).eq_or_lt with h0 | hpos
  · rw [← h0, inv_zero, zero_smul, sub_zero,
      show FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h)) = FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h) from rfl, FunctionalInequalities.KLS.LogConcave.PoissonIterate.step, FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_smul,
      ← h0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    exact mul_nonneg C.2 hdef
  · have e : FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h) - (FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h)⁻¹ • FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ h) =
        (-(FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h)⁻¹) •
          (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ h) - FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h • FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h)) := by
      rw [smul_sub, smul_smul, neg_mul, inv_mul_cancel₀ hpos.ne', neg_smul, neg_smul, one_smul]
      abel
    have hinv : (FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h ^ 2)⁻¹ ≤ (C : ℝ) :=
      inv_le_of_inv_le₀ (NNReal.coe_pos.mpr hCpos)
        (FunctionalInequalities.KLS.LogConcave.PoissonIterate.inv_le_scale_sq_step_readable m hν hi hνU hU hC hCpos h hpos)
    rw [e, FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_smul, neg_sq, inv_pow]
    exact mul_le_mul_of_nonneg_right hinv hdef
