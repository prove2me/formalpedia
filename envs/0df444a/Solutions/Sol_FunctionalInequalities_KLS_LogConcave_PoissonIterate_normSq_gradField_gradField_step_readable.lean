-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_gradField_gradField_step_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:28:12.092982+00:00
-- url     : https://prove2.me/submissions/8fb58cb9-eeb2-4225-a8d2-e6bea05aa021

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Domain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Hessian
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Defect
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_id_gap_of_literature_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_convexOn_of_eq_tilted_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_existsUnique_centered_adjointComp_eq_readable
import Theorems.Thm_FunctionalInequalities_L2_inner_center_center_readable
import Theorems.Thm_FunctionalInequalities_L2_sum_norm_sq_compLp_innerSL_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_seq_smooth_tendsto_weakHessian_readable

section
noncomputable section
open MeasureTheory
section
variable {α : Type*} [MeasurableSpace α]
/-- The zero constant is the zero element of `L²`. -/
@[simp]
theorem FunctionalInequalities.L2.const_zero (μ : ProbabilityMeasure α) : const μ 0 = 0 :=
  map_zero (Lp.const 2 (μ : Measure α))
/-- The Hilbert-space mean agrees with the integral of any representative supplied by `Lp`. -/
theorem FunctionalInequalities.L2.mean_eq_integral (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ f = ∫ x, f x ∂(μ : Measure α) := by
  rw [mean, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [const_coeFn μ 1] with x hx
  simp [hx]
/-- Probability normalization makes the mean of a constant equal to that constant. -/
@[simp]
theorem FunctionalInequalities.L2.mean_const (μ : ProbabilityMeasure α) (c : ℝ) : mean μ (const μ c) = c := by
  rw [mean_eq_integral]
  calc
    (∫ x, const μ c x ∂(μ : Measure α)) = ∫ _ : α, c ∂(μ : Measure α) :=
      integral_congr_ae (const_coeFn μ c)
    _ = c := by simp
/-- The mean of zero is zero. -/
@[simp]
theorem FunctionalInequalities.L2.mean_zero (μ : ProbabilityMeasure α) : mean μ 0 = 0 := by
  simp [mean]
/-- The mean preserves subtraction. -/
@[simp]
theorem FunctionalInequalities.L2.mean_sub (μ : ProbabilityMeasure α) (f g : Lp ℝ 2 (μ : Measure α)) :
    mean μ (f - g) = mean μ f - mean μ g := by
  rw [mean, inner_sub_left]
  rfl
/-- A centered `L²` element has mean zero. -/
@[simp]
theorem FunctionalInequalities.L2.mean_center (μ : ProbabilityMeasure α) (f : Lp ℝ 2 (μ : Measure α)) :
    mean μ (center μ f) = 0 := by
  simp [center]
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
/-- The total generator agrees with `T†T` on its domain. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_of_mem {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain) :
    gen T u = adjointComp T ⟨u, hu⟩ :=
  dif_pos hu
/-- The total gradient of `0` is `0`. -/
@[simp]
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad_zero : weakGrad T 0 = 0 := by
  rw [weakGrad_of_mem T T.domain.zero_mem]
  exact LinearPMap.map_zero T
/-- The total generator of `0` is `0`. -/
@[simp]
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_zero : gen T 0 = 0 := by
  rw [gen_of_mem T (adjointComp T).domain.zero_mem]
  exact LinearPMap.map_zero (adjointComp T)
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
/-- The total generator is homogeneous on the domain of `T†T`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_smul (c : ℝ) {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T).domain) :
    gen T (c • u) = c • gen T u := by
  rw [gen_of_mem T ((adjointComp T).domain.smul_mem c hu), gen_of_mem T hu]
  exact LinearPMap.map_smul (adjointComp T) c ⟨u, hu⟩
/-- The centered inverse is always centered (it is `0` when no centered preimage exists). -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.mean_centeredInv (g : Lp ℝ 2 (ν : Measure V)) : L2.mean ν (centeredInv T g) = 0 := by
  unfold centeredInv
  split_ifs with h
  · exact h.choose_spec.1
  · exact L2.mean_zero ν
/-- If a centered preimage of `g` under `T†T` exists, the centered inverse is one. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.centeredInv_spec_of_exists {g : Lp ℝ 2 (ν : Measure V)}
    (h : ∃ u : (adjointComp T).domain,
      L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0 ∧ adjointComp T u = g) :
    ∃ hu : centeredInv T g ∈ (adjointComp T).domain, adjointComp T ⟨_, hu⟩ = g := by
  have hc : centeredInv T g = (h.choose : Lp ℝ 2 (ν : Measure V)) := by
    unfold centeredInv
    rw [dif_pos h]
  rw [hc]
  exact ⟨h.choose.2, h.choose_spec.2⟩
/-- `normSq` is quadratic: `‖c u‖² = c² ‖u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_smul {k : ℕ} (c : ℝ) (u : Field ν k) : normSq (c • u) = c ^ 2 * normSq u := by
  unfold normSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
/-- `normSq u = 0` exactly when every component vanishes. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_eq_zero_iff {k : ℕ} (u : Field ν k) : normSq u = 0 ↔ ∀ I, u I = 0 := by
  unfold normSq
  rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _]
  simp
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
/-- The energy is nonnegative. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_nonneg {k : ℕ} (u : Field ν k) : 0 ≤ energy T u :=
  normSq_nonneg _
/-- The energy is quadratic: `‖∇(c u)‖² = c² ‖∇u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_smul {k : ℕ} (c : ℝ) (u : Field ν k) : energy T (c • u) = c ^ 2 * energy T u := by
  rw [energy_eq_sum, energy_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Pi.smul_apply, weakGrad_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
/-- The components of `∇₀h` are centered. -/
@[simp]
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.mean_grad0 {k : ℕ} (h : Field ν k) (J : Fin (k + 1) → Fin (Module.finrank ℝ V)) :
    L2.mean ν (grad0 T h J) = 0 :=
  L2.mean_center ν _
end General
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  {C : NNReal} (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
include hC in
/-- The Poincaré gap for a centered `u ∈ D(T̄)`: `‖u‖² ≤ C ‖∇u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_sq_le_weakGrad {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (T̄).domain)
    (hmean : L2.mean ν u = 0) : ‖u‖ ^ 2 ≤ (C : ℝ) * ‖weakGrad T̄ u‖ ^ 2 := by
  have h := hν.closedWeightedOperator_id_gap_of_literature_le_readable m hi C hC ⟨u, hu⟩
  have hcenter : L2.center ν u = u := by simp [L2.center, hmean]
  rw [weakGrad_of_mem _ hu]
  simpa [hcenter] using h
include hνU hU hC in
/-- **BKL Lemma 2.1 for the total centered inverse.** For centered `g`, `centeredInv T̄ g` lies in
`D(A)` and solves `A u = g`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.centeredInv_spec {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    ∃ hu : centeredInv T̄ g ∈ (adjointComp T̄).domain, adjointComp T̄ ⟨_, hu⟩ = g :=
  centeredInv_spec_of_exists _
    (existsUnique_centered_adjointComp_eq_readable m hν hi hνU hU hC g hg).exists
include hνU hU hC in
/-- For centered `g`, `(-L)⁻¹ g ∈ D(A)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.centeredInv_mem_domain {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    centeredInv T̄ g ∈ (adjointComp T̄).domain :=
  (centeredInv_spec m hν hi hνU hU hC hg).1
include hνU hU hC in
/-- For centered `g`, `-L (-L)⁻¹ g = g`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen_centeredInv {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    gen T̄ (centeredInv T̄ g) = g := by
  obtain ⟨hu, hAu⟩ := centeredInv_spec m hν hi hνU hU hC hg
  rw [gen_of_mem _ hu, hAu]
include hνU hU hC in
/-- The components of one step lie in `D(A)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.step_mem_domain {k : ℕ} (h : Field ν k) (J : Fin (k + 1) → Fin (Module.finrank ℝ V)) :
    step T̄ h J ∈ (adjointComp T̄).domain :=
  (adjointComp T̄).domain.smul_mem _
    (centeredInv_mem_domain m hν hi hνU hU hC (mean_grad0 (T̄) h J))
include hνU hU hC in
/-- **BKL (30)** for one step: `-L (α (-L)⁻¹ ∇₀h) = α ∇₀h`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.genField_step {k : ℕ} (h : Field ν k) :
    genField T̄ (step T̄ h) = scale T̄ h • grad0 T̄ h := by
  funext J
  rw [genField, step, Pi.smul_apply, Pi.smul_apply, invField,
    gen_smul _ _ (centeredInv_mem_domain m hν hi hνU hU hC (mean_grad0 (T̄) h J)),
    gen_centeredInv m hν hi hνU hU hC (mean_grad0 (T̄) h J)]
include hνU hU hC in
/-- If `∇(-L)⁻¹∇₀h = 0` then `∇₀h = 0`: the centered `w_J` with `∇w_J = 0` vanish by the Poincaré
gap, so `∇₀h_J = A w_J = 0`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_eq_zero_of_energy_eq_zero {k : ℕ} (h : Field ν k)
    (h0 : energy T̄ (invField T̄ (grad0 T̄ h)) = 0) : normSq (grad0 T̄ h) = 0 := by
  rw [normSq_eq_zero_iff]
  intro J
  have hJ : ‖weakGrad T̄ (invField T̄ (grad0 T̄ h) J)‖ ^ 2 = 0 := by
    rw [energy_eq_sum, Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at h0
    exact h0 J (Finset.mem_univ J)
  have hmem := centeredInv_mem_domain m hν hi hνU hU hC (mean_grad0 (T̄) h J)
  have hgap := norm_sq_le_weakGrad m hν hi hC hmem.2 (mean_centeredInv (T̄) _)
  rw [invField] at hJ
  rw [hJ, mul_zero] at hgap
  have hw : centeredInv T̄ (grad0 T̄ h J) = 0 := by
    have hn := norm_nonneg (centeredInv T̄ (grad0 T̄ h J))
    have : ‖centeredInv T̄ (grad0 T̄ h J)‖ = 0 := by nlinarith
    exact norm_eq_zero.mp this
  rw [← gen_centeredInv m hν hi hνU hU hC (mean_grad0 (T̄) h J), hw, gen_zero]
include hνU hU hC in
/-- **BKL (33)** for one step: `‖∇(α (-L)⁻¹∇₀h)‖² = ‖∇₀h‖²`, also when `∇₀h = 0`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_step {k : ℕ} (h : Field ν k) :
    energy T̄ (step T̄ h) = normSq (grad0 T̄ h) := by
  rw [step, energy_smul]
  by_cases h0 : energy T̄ (invField T̄ (grad0 T̄ h)) = 0
  · rw [h0, mul_zero, normSq_grad0_eq_zero_of_energy_eq_zero m hν hi hνU hU hC h h0]
  · have hs : scale T̄ h = Real.sqrt (normSq (grad0 T̄ h) /
        energy T̄ (invField T̄ (grad0 T̄ h))) := if_neg h0
    rw [hs, Real.sq_sqrt (div_nonneg (normSq_nonneg _) (energy_nonneg _ _)),
      div_mul_cancel₀ _ h0]
include hνU hU hC in
/-- **BKL (46)** for one step: `‖L h'‖² = α² ‖∇h'‖²` for `h' = α (-L)⁻¹∇₀h`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_genField_step {k : ℕ} (h : Field ν k) :
    normSq (genField T̄ (step T̄ h)) = scale T̄ h ^ 2 * energy T̄ (step T̄ h) := by
  rw [genField_step m hν hi hνU hU hC, normSq_smul, energy_step m hν hi hνU hU hC]
end HeatModel
end
end

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
section
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
section Hessian
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
omit [CompleteSpace V] in
include hν in
/-- The curvature bound `∇²U ≥ 0` of a log-concave tilted law with a `C²` potential. -/
private theorem FunctionalInequalities.KLS.LogConcave.zero_mul_le_bilinearIteratedFDerivTwo (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ 2 U) (x v : V) :
    0 * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v := by
  rw [zero_mul]
  exact bilinearIteratedFDerivTwo_nonneg_of_convexOn hU
    (convexOn_of_eq_tilted_readable m hν hνU hU.continuous) x v
/-- **the weak Hessian estimate, weak first derivatives in the form domain.** For `ν = m.tilted (-U)` log-concave,
with `U` of temperate growth and all exponential moments, and `F ∈ D(A)`, every weak first
derivative `∂ᵢ F = ⟪eᵢ, T̄ F⟫` (standard orthonormal basis) lies in `D(T̄)`. No curvature bound
beyond the convexity of `U` implied by log-concavity is assumed. -/
theorem FunctionalInequalities.KLS.LogConcave.compLp_innerSL_mem_closedWeightedOperator_domain
    (hνU : (ν : Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V))
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
    (i : Fin (Module.finrank ℝ V)) :
    (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
      (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := by
  have hU2 : ContDiff ℝ 2 U := hUt.1.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨_, _, _, -, -, hD⟩ := exists_seq_smooth_tendsto_weakHessian_readable m hν hi hνU hUt
    (hU2.of_le (by norm_num)) hexp (zero_mul_le_bilinearIteratedFDerivTwo m hν hνU hU2) F
  exact (hD i).1
end Hessian
end
end
end

noncomputable section
open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace
section General
/-- Splitting off the first index position: `Σ_{J'} F J' = Σ_J Σ_j F (j, J)`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_cons {n k : ℕ} {M : Type*} [AddCommMonoid M]
    (F : (Fin (k + 1) → Fin n) → M) :
    ∑ J, F J = ∑ J, ∑ j, F (Fin.cons j J) := by
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin n).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl
variable {α : Type*} [MeasurableSpace α] {ν : MeasureTheory.ProbabilityMeasure α}
/-- Pairing with the centered part: `⟪u - ∫u, u⟫ = ‖u - ∫u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.inner_center_self (u : Lp ℝ 2 (ν : Measure α)) :
    ⟪L2.center ν u, u⟫ = ‖L2.center ν u‖ ^ 2 := by
  have hc : ⟪L2.const ν (L2.mean ν u), u⟫ = L2.mean ν u * L2.mean ν u := by
    rw [← mul_one (L2.mean ν u), L2.const_smul, real_inner_smul_left, real_inner_comm, mul_one]
    rfl
  rw [← real_inner_self_eq_norm_sq, L2.inner_center_center_readable, L2.center, inner_sub_left, hc]
end General
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
/-- A weak partial derivative on `D(T̄)` in terms of `T̄`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.partialDeriv_eq {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (T̄).domain)
    (j : Fin (Module.finrank ℝ V)) :
    partialDeriv T̄ j u = (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp (T̄ ⟨u, hu⟩) := by
  rw [partialDeriv, weakGrad_of_mem _ hu]
include hνU hUt hexp in
/-- **Weak first derivatives of `D(A)` lie in `D(T̄)`**: for `u ∈ D(A)`, `∂_j u ∈ D(T̄)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.partialDeriv_mem_domain {u : Lp ℝ 2 (ν : Measure V)}
    (hu : u ∈ (adjointComp T̄).domain) (j : Fin (Module.finrank ℝ V)) :
    partialDeriv T̄ j u ∈ (T̄).domain := by
  rw [partialDeriv_eq m hν hi hu.2]
  exact compLp_innerSL_mem_closedWeightedOperator_domain m hν hi hνU hUt hexp ⟨u, hu⟩ j
/-- The norm expansion behind (47) for one component: for `u ∈ D(T̄)` and `w ∈ D(A)`,
`Σ_j ‖∂_j u - α ∂_j w‖² = ‖∇u‖² - 2α ⟪A w, u⟫ + α² ‖∇w‖²`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_norm_sq_partialDeriv_sub_smul {u w : Lp ℝ 2 (ν : Measure V)}
    (hu : u ∈ (T̄).domain) (hw : w ∈ (adjointComp T̄).domain) (α : ℝ) :
    ∑ j, ‖partialDeriv T̄ j u - α • partialDeriv T̄ j w‖ ^ 2 =
      ‖weakGrad T̄ u‖ ^ 2 - 2 * α * ⟪gen T̄ w, u⟫ + α ^ 2 * ‖weakGrad T̄ w‖ ^ 2 := by
  have hlin : ∀ j, partialDeriv T̄ j u - α • partialDeriv T̄ j w =
      (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp (weakGrad T̄ u - α • weakGrad T̄ w) := by
    intro j
    have h1 := ((innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLpₗ 2 (ν : Measure V)).map_sub
      (weakGrad T̄ u) (α • weakGrad T̄ w)
    have h2 := ((innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLpₗ 2 (ν : Measure V)).map_smul
      α (weakGrad T̄ w)
    simp only [ContinuousLinearMap.compLpₗ_apply] at h1 h2
    rw [h1, h2]
    rfl
  have hinner : ⟪gen T̄ w, u⟫ = ⟪weakGrad T̄ u, weakGrad T̄ w⟫ := by
    rw [gen_of_mem _ hw, inner_adjointComp
      (dense_domain_closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hν hi) ⟨w, hw⟩ hu,
      weakGrad_of_mem _ hu, weakGrad_of_mem _ hw.2, real_inner_comm]
  simp_rw [hlin]
  rw [L2.sum_norm_sq_compLp_innerSL_readable (stdOrthonormalBasis ℝ V), norm_sub_sq_real, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_right, hinner]
  ring
include hνU hUt hexp hC in
/-- **BKL (47) for one step.** For a field `h` with components in `D(A)`, `h' = α (-L)⁻¹ ∇₀h` and
`α = scale h`: `‖∇²h‖² = ‖L h'‖² + ‖∇²h - α ∇h'‖²`. -/
theorem solution {k : ℕ} (h : FunctionalInequalities.KLS.LogConcave.PoissonIterate.Field ν k)
    (hh : ∀ I, h I ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T̄).domain) :
    FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ h)) = FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (FunctionalInequalities.KLS.LogConcave.PoissonIterate.genField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h)) + FunctionalInequalities.KLS.LogConcave.PoissonIterate.defect T̄ h := by
  have hU := FunctionalInequalities.KLS.LogConcave.PoissonIterate.contDiff_two hUt
  set α := FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ h
  have hu : ∀ J, FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ h J ∈ (T̄).domain := fun J =>
    FunctionalInequalities.KLS.LogConcave.PoissonIterate.partialDeriv_mem_domain m hν hi hνU hUt hexp (hh _) _
  have hw : ∀ J, FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h J ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T̄).domain := FunctionalInequalities.KLS.LogConcave.PoissonIterate.step_mem_domain m hν hi hνU hU hC h
  have hgen : ∀ J, FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h J) = α • FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ h J := fun J =>
    congrFun (FunctionalInequalities.KLS.LogConcave.PoissonIterate.genField_step m hν hi hνU hU hC h) J
  have hdef : FunctionalInequalities.KLS.LogConcave.PoissonIterate.defect T̄ h = ∑ J, (‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ h J)‖ ^ 2 -
      2 * α * ⟪FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h J), FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ h J⟫ +
        α ^ 2 * ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h J)‖ ^ 2) := by
    rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.defect, FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq, FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_cons]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_norm_sq_partialDeriv_sub_smul m hν hi (hu J) (hw J)]
    rfl
  have hH : FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ h)) =
      ∑ J, ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ h J)‖ ^ 2 :=
    FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_eq_sum _ _
  have hE : ∑ J, ‖FunctionalInequalities.KLS.LogConcave.PoissonIterate.weakGrad T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h J)‖ ^ 2 = FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ h) := by
    rw [← FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_eq_sum, FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_step m hν hi hνU hU hC]
  have hP : ∑ J, ⟪FunctionalInequalities.KLS.LogConcave.PoissonIterate.gen T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.step T̄ h J), FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField T̄ h J⟫ = α * FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ h) := by
    rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [hgen, real_inner_smul_left, FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0, FunctionalInequalities.KLS.LogConcave.PoissonIterate.inner_center_self]
  rw [FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_genField_step m hν hi hνU hU hC, FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_step m hν hi hνU hU hC, hdef,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hP, hE,
    ← hH]
  ring
