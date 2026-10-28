-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_iter_sub_symField_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:33:02.274788+00:00
-- url     : https://prove2.me/submissions/fcdd3874-9dcb-400b-9f63-5d7bab1e5f43

import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Domain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Defect
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Permutation
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Symmetry
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_exists_symm_normSq_grad0_step_sub_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_grad0_step_sub_permField_succ_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_normSq_sub_symField_le_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_centered_adjointComp_bounds_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_existsUnique_centered_adjointComp_eq_readable
import Theorems.Thm_FunctionalInequalities_L2_inner_center_center_readable
import Theorems.Thm_FunctionalInequalities_L2_sum_norm_sq_compLp_innerSL_readable

section
noncomputable section
open MeasureTheory
section
variable {α : Type*} [MeasurableSpace α]
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
omit [FiniteDimensional ℝ V] in
/-- Centering the components removes the squared means: `‖u‖² - ‖u - ∫u‖² = Σ_J (∫u_J)²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_sub_normSq_center {k : ℕ} (u : Field ν k) :
    normSq u - normSq (fun J => L2.center ν (u J)) = ∑ J, L2.mean ν (u J) ^ 2 := by
  unfold normSq
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  have h := L2.inner_center_center_readable ν (u J) (u J)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [h]
  ring
/-- The energy drop of BKL (35) in the form `‖∇h‖² - ‖∇₀h‖² = |∫∇h|²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.energy_sub_normSq_grad0 {k : ℕ} (h : Field ν k) :
    energy T h - normSq (grad0 T h) = meanGradSq T h :=
  normSq_sub_normSq_center (gradField T h)
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
/-- **BKL (20)** for the total centered inverse: for centered `g`,
`‖∇(-L)⁻¹g‖² = ⟪g, (-L)⁻¹g⟫ ≤ C ‖g‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.norm_weakGrad_centeredInv_sq_le {g : Lp ℝ 2 (ν : Measure V)} (hg : L2.mean ν g = 0) :
    ‖weakGrad T̄ (centeredInv T̄ g)‖ ^ 2 = ⟪g, centeredInv T̄ g⟫ ∧
      ⟪g, centeredInv T̄ g⟫ ≤ (C : ℝ) * ‖g‖ ^ 2 := by
  obtain ⟨hu, hAu⟩ := centeredInv_spec m hν hi hνU hU hC hg
  obtain ⟨-, h₂, h₃, -⟩ :=
    centered_adjointComp_bounds_readable m hν hi hνU hU hC ⟨_, hu⟩ (mean_centeredInv (T̄) g)
  rw [hAu] at h₂ h₃
  rw [weakGrad_of_mem _ hu.2]
  exact ⟨h₂, h₃⟩
include hνU hU hC in
/-- The components of one step lie in `D(A)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.step_mem_domain {k : ℕ} (h : Field ν k) (J : Fin (k + 1) → Fin (Module.finrank ℝ V)) :
    step T̄ h J ∈ (adjointComp T̄).domain :=
  (adjointComp T̄).domain.smul_mem _
    (centeredInv_mem_domain m hν hi hνU hU hC (mean_grad0 (T̄) h J))
include hνU hU hC in
/-- **The iterates lie in `D(A)`.** Every component of `h_{k+1} = iter T̄ f k` lies in `D(A)`, for
`f ∈ D(A)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter_mem_adjointComp_domain {f : Lp ℝ 2 (ν : Measure V)}
    (hf : f ∈ (adjointComp T̄).domain) (k : ℕ) (I : Fin k → Fin (Module.finrank ℝ V)) :
    iter T̄ f k I ∈ (adjointComp T̄).domain := by
  cases k with
  | zero => exact hf
  | succ k => exact step_mem_domain m hν hi hνU hU hC _ I
end HeatModel
end
end

section
noncomputable section
open MeasureTheory Filter Topology
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace
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
include hνU hUt hexp hC in
/-- **BKL Lemma 3.2**, with `λ = 1/C`. For `f ∈ D(A)`, `∇₀h_{k+2}` is within `C χ_{k+1}` of a
field symmetric in its first two index positions. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.exists_symm_normSq_grad0_iter_succ_sub_le (hCpos : 0 < C)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) (k : ℕ) :
    ∃ S : Field ν (k + 2), (∀ J, S (J ∘ Equiv.swap 0 1) = S J) ∧
      normSq (grad0 T̄ (iter T̄ f (k + 1)) - S) ≤ (C : ℝ) * defect T̄ (iter T̄ f k) :=
  exists_symm_normSq_grad0_step_sub_le_readable m hν hi hνU hUt hexp hC hCpos _
    (iter_mem_adjointComp_domain m hν hi hνU (contDiff_two hUt) hC hf k)
end HeatModel
end
end

section
noncomputable section
open MeasureTheory Finset
open FunctionalInequalities.Analysis.Tensor
open scoped Classical
section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  {ν : MeasureTheory.ProbabilityMeasure V} {k : ℕ}
/-- `permField σ` commutes with subtraction. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField_sub (σ : Equiv.Perm (Fin k)) (u v : Field ν k) :
    permField σ (u - v) = permField σ u - permField σ v := rfl
/-- `normSq u` is the squared norm of `u` in `PiLp 2`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_eq_norm_toLp_sq (u : Field ν k) :
    normSq u = ‖(WithLp.toLp 2 u :
      PiLp 2 fun _ : Fin k → Fin (Module.finrank ℝ V) => Lp ℝ 2 (ν : Measure V))‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl
/-- The Hilbert–Schmidt norm `√(normSq u)` is the norm of `u` in `PiLp 2`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_eq (u : Field ν k) :
    √(normSq u) = ‖(WithLp.toLp 2 u :
      PiLp 2 fun _ : Fin k → Fin (Module.finrank ℝ V) => Lp ℝ 2 (ν : Measure V))‖ := by
  rw [normSq_eq_norm_toLp_sq, Real.sqrt_sq (norm_nonneg _)]
/-- The triangle inequality for the Hilbert–Schmidt norm `√(normSq ·)`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sqrt_normSq_add_le (u v : Field ν k) :
    √(normSq (u + v)) ≤ √(normSq u) + √(normSq v) := by
  simp only [sqrt_normSq_eq, WithLp.toLp_add]
  exact norm_add_le _ _
/-- `normSq` is invariant under negation. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_neg (u : Field ν k) : normSq (-u) = normSq u := by
  simp [normSq]
/-- `permField σ` preserves the squared Hilbert–Schmidt norm. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_permField (σ : Equiv.Perm (Fin k)) (u : Field ν k) :
    normSq (permField σ u) = normSq u := by
  unfold normSq
  exact (Equiv.arrowCongr σ.symm (Equiv.refl (Fin (Module.finrank ℝ V)))).sum_comp
    fun J => ‖u J‖ ^ 2
end
end
end

noncomputable section
open MeasureTheory Finset
open FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace
section Positions
/-- `τ₀` is the transposition of the first two positions. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.swap_zero_finRotate {k : ℕ} :
    Equiv.swap (0 : Fin (k + 2)) (finRotate (k + 2) 0) = Equiv.swap 0 1 := by
  rw [finRotate_apply_zero]
end Positions
section General
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
  (T : MeasureTheory.Lp ℝ 2 (ν : MeasureTheory.Measure V) →ₗ.[ℝ] MeasureTheory.Lp V 2 (ν : MeasureTheory.Measure V))
/-- Centering the gradient only lowers the norm: `‖∇₀u‖² ≤ ‖∇u‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_le_energy {k : ℕ} (u : Field ν k) : normSq (grad0 T u) ≤ energy T u := by
  have h := energy_sub_normSq_grad0 T u
  have hp : 0 ≤ meanGradSq T u := sum_nonneg fun _ _ => sq_nonneg _
  linarith
end General
section HeatModel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  {C : NNReal} (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
include hνU hU hC in
/-- **BKL (20)/(24) for fields.** For a field `g` with centered components,
`‖∇₀(-L)⁻¹g‖² ≤ C ‖g‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_invField_le {k : ℕ} {g : Field ν k} (hg : ∀ I, L2.mean ν (g I) = 0) :
    normSq (grad0 T̄ (invField T̄ g)) ≤ (C : ℝ) * normSq g := by
  refine (normSq_grad0_le_energy _ _).trans ?_
  rw [energy_eq_sum, normSq, mul_sum]
  refine sum_le_sum fun I _ => ?_
  obtain ⟨h1, h2⟩ := norm_weakGrad_centeredInv_sq_le m hν hi hνU hU hC (hg I)
  rw [invField, h1]
  exact h2
include hνU hU hC in
/-- **BKL (42), norm form.** `‖∇₀h' - τ_{ℓ+1} ∇₀h'‖² ≤ α² C ‖∇₀h - τ_ℓ ∇₀h‖²`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_step_sub_permField_succ_le {k : ℕ} (h : Field ν k) (ℓ : Fin (k + 1))
    (hℓ : ℓ.val + 1 < k + 1) :
    normSq (grad0 T̄ (step T̄ h) -
        permField (Equiv.swap ℓ.succ (finRotate (k + 2) ℓ.succ)) (grad0 T̄ (step T̄ h))) ≤
      scale T̄ h ^ 2 * (C : ℝ) *
        normSq (grad0 T̄ h - permField (Equiv.swap ℓ (finRotate (k + 1) ℓ)) (grad0 T̄ h)) := by
  rw [grad0_step_sub_permField_succ_readable m hν hi hνU hU hC h ℓ hℓ, normSq_smul, mul_assoc]
  refine mul_le_mul_of_nonneg_left (normSq_grad0_invField_le m hν hi hνU hU hC fun I => ?_)
    (sq_nonneg _)
  simp only [Pi.sub_apply, permField, L2.mean_sub, mean_grad0, sub_zero]
end HeatModel
section Iterates
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
  {C : NNReal} (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
omit [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- If `σ` fixes `S`, then `‖u - σ u‖² ≤ 4 ‖u - S‖²`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_sub_permField_le_of_fixed {k : ℕ} (σ : Equiv.Perm (Fin k))
    {S : Field ν k} (hS : permField σ S = S) (u : Field ν k) :
    normSq (u - permField σ u) ≤ 4 * normSq (u - S) := by
  have e : u - permField σ u = (u - S) + -permField σ (u - S) := by
    rw [permField_sub, hS]
    abel
  have h : √(normSq (u - permField σ u)) ≤ 2 * √(normSq (u - S)) := by
    rw [e]
    refine (sqrt_normSq_add_le _ _).trans ?_
    rw [normSq_neg, normSq_permField]
    linarith
  have h' := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt (normSq_nonneg _), mul_pow, Real.sq_sqrt (normSq_nonneg _)] at h'
  norm_num at h'
  linarith
include hνU hUt hexp hC in
/-- **The first transposition**, from Lemma 3.2: `‖∇₀h_{k+2} - τ₀ ∇₀h_{k+2}‖² ≤ 4 C χ_{k+1}`. -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_iter_succ_sub_permField_swap_le (hCpos : 0 < C)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) (k : ℕ) :
    normSq (grad0 T̄ (iter T̄ f (k + 1)) -
        permField (Equiv.swap 0 1) (grad0 T̄ (iter T̄ f (k + 1)))) ≤
      4 * (C : ℝ) * defect T̄ (iter T̄ f k) := by
  obtain ⟨S, hS, hle⟩ :=
    exists_symm_normSq_grad0_iter_succ_sub_le m hν hi hνU hUt hexp hC hCpos hf k
  refine (normSq_sub_permField_le_of_fixed _ (funext hS) _).trans ?_
  linarith
include hνU hUt hexp hC in
/-- The induction behind (43), by the number `n` of applications of (42). -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_iter_sub_permField_le_aux (hCpos : 0 < C)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) {β : ℝ} (n : ℕ) :
    ∀ (k : ℕ) (ℓ : Fin (k + 1)), ℓ.val = n → n < k →
      (∀ j, k - n ≤ j → j < k → scale T̄ (iter T̄ f j) ^ 2 ≤ β / C) →
      normSq (grad0 T̄ (iter T̄ f k) -
          permField (Equiv.swap ℓ (finRotate (k + 1) ℓ)) (grad0 T̄ (iter T̄ f k))) ≤
        max 1 β ^ n * (4 * (C : ℝ) * defect T̄ (iter T̄ f (k - n - 1))) := by
  have hU := contDiff_two hUt
  have hC0 : (0 : ℝ) < C := NNReal.coe_pos.mpr hCpos
  induction n with
  | zero =>
    intro k ℓ hℓ hk _
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain rfl : ℓ = 0 := Fin.ext hℓ
    rw [swap_zero_finRotate, pow_zero, one_mul, show k' + 1 - 0 - 1 = k' by omega]
    exact normSq_grad0_iter_succ_sub_permField_swap_le m hν hi hνU hUt hexp hC hCpos hf k'
  | succ n ih =>
    intro k ℓ hℓ hk hα
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨ℓ₀, rfl⟩ : ∃ ℓ₀ : Fin (k' + 1), ℓ₀.succ = ℓ :=
      Fin.exists_succ_eq.mpr fun h => by simp [h] at hℓ
    have hℓ₀ : ℓ₀.val = n := by simpa using hℓ
    have hstep := normSq_grad0_step_sub_permField_succ_le m hν hi hνU hU hC (iter T̄ f k') ℓ₀
      (by omega)
    have hIH := ih k' ℓ₀ hℓ₀ (by omega) fun j hj hj' => hα j (by omega) (by omega)
    have hαk : scale T̄ (iter T̄ f k') ^ 2 * (C : ℝ) ≤ max 1 β :=
      ((le_div_iff₀ hC0).mp (hα k' (by omega) (by omega))).trans (le_max_right _ _)
    rw [show k' + 1 - (n + 1) - 1 = k' - n - 1 by omega, pow_succ', mul_assoc]
    refine hstep.trans ?_
    exact mul_le_mul hαk hIH (normSq_nonneg _) (zero_le_one.trans (le_max_left _ _))
include hνU hUt hexp hC in
/-- **BKL (43).** For `ℓ < k` and `α_j² ≤ β/C` for `k - ℓ ≤ j < k`:
`‖∇₀h_{k+1} - τ_ℓ ∇₀h_{k+1}‖² ≤ max(1, β)^ℓ · 4 C χ_{k-ℓ}` (the defect of `iter (k - ℓ - 1)`). -/
theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_iter_sub_permField_le (hCpos : 0 < C)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) {β : ℝ} {k : ℕ}
    (ℓ : Fin (k + 1)) (hℓ : ℓ.val < k)
    (hα : ∀ j, k - ℓ.val ≤ j → j < k → scale T̄ (iter T̄ f j) ^ 2 ≤ β / C) :
    normSq (grad0 T̄ (iter T̄ f k) -
        permField (Equiv.swap ℓ (finRotate (k + 1) ℓ)) (grad0 T̄ (iter T̄ f k))) ≤
      max 1 β ^ ℓ.val * (4 * (C : ℝ) * defect T̄ (iter T̄ f (k - ℓ.val - 1))) :=
  normSq_grad0_iter_sub_permField_le_aux m hν hi hνU hUt hexp hC hCpos hf ℓ.val k ℓ rfl hℓ hα
/-- Reindexing the defects: `Σ_{ℓ+1<q} F (k - ℓ - 1) = Σ_{k+1-q ≤ j < k} F j`. -/
private theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_filter_eq_sum_Ico {k q : ℕ} (hq : q ≤ k + 1) (F : ℕ → ℝ) :
    ∑ ℓ ∈ univ.filter (fun ℓ : Fin (k + 1) => ℓ.val + 1 < q), F (k - ℓ.val - 1) =
      ∑ j ∈ Ico (k + 1 - q) k, F j := by
  refine sum_bij' (fun ℓ _ => k - ℓ.val - 1) (fun j _ => ⟨k - 1 - j, by omega⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro ℓ hℓ
    simp only [mem_filter, mem_univ, true_and] at hℓ
    simp only [mem_Ico]
    omega
  · intro j hj
    simp only [mem_Ico] at hj
    simp only [mem_filter, mem_univ, true_and]
    omega
  · intro ℓ hℓ
    simp only [mem_filter, mem_univ, true_and] at hℓ
    ext
    simp only
    omega
  · intro j hj
    simp only [mem_Ico] at hj
    simp only
    omega
  · intro ℓ _
    rfl
include hνU hUt hexp hC in
/-- **BKL Lemma 3.3**, for every `q` with `2 ≤ q ≤ k + 1`, under `0 < α_j² ≤ β/C` for
`k + 1 - q ≤ j < k`: `∇₀h_{k+1}` is close to its symmetrization `S_q` over the first `q` index
positions, `‖∇₀h_{k+1} - S_q ∇₀h_{k+1}‖² ≤ 4 q⁴ max(1, β)^q C Σ_{k+1-q ≤ j < k} χ_j`. -/
theorem solution (hCpos : 0 < C)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (FunctionalInequalities.Analysis.Semigroup.adjointComp T̄).domain) {β : ℝ} (k q : ℕ)
    (hq : 2 ≤ q) (hqk : q ≤ k + 1)
    (hα : ∀ j, k + 1 - q ≤ j → j < k →
      0 < FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f j) ∧ FunctionalInequalities.KLS.LogConcave.PoissonIterate.scale T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f j) ^ 2 ≤ β / C) :
    FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k) - FunctionalInequalities.KLS.LogConcave.PoissonIterate.symField q (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k))) ≤
      4 * (q : ℝ) ^ 4 * max 1 β ^ q * C *
        ∑ j ∈ Finset.Ico (k + 1 - q) k, FunctionalInequalities.KLS.LogConcave.PoissonIterate.defect T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f j) := by
  have hC0 : (0 : ℝ) ≤ C := C.2
  have hmax : (1 : ℝ) ≤ max 1 β := le_max_left _ _
  refine (FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_sub_symField_le_readable hqk _).trans ?_
  rw [← FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_filter_eq_sum_Ico hqk, mul_sum, mul_sum]
  refine sum_le_sum fun ℓ hℓ => ?_
  simp only [mem_filter, mem_univ, true_and] at hℓ
  have h := FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_iter_sub_permField_le m hν hi hνU hUt hexp hC hCpos hf ℓ (by omega)
    fun j hj hj' => (hα j (by omega) hj').2
  have hpow : max 1 β ^ ℓ.val ≤ max 1 β ^ q := pow_le_pow_right₀ hmax (by omega)
  have hdef : 0 ≤ FunctionalInequalities.KLS.LogConcave.PoissonIterate.defect T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f (k - ℓ.val - 1)) := FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_nonneg _
  have hq4 : (0 : ℝ) ≤ (q : ℝ) ^ 4 := by positivity
  calc (q : ℝ) ^ 4 * FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k) -
        FunctionalInequalities.KLS.LogConcave.PoissonIterate.permField (Equiv.swap ℓ (finRotate (k + 1) ℓ)) (FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0 T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f k)))
      ≤ (q : ℝ) ^ 4 * (max 1 β ^ q * (4 * (C : ℝ) * FunctionalInequalities.KLS.LogConcave.PoissonIterate.defect T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f (k - ℓ.val - 1)))) :=
        mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right hpow (by positivity)))
          hq4
    _ = 4 * (q : ℝ) ^ 4 * max 1 β ^ q * C * FunctionalInequalities.KLS.LogConcave.PoissonIterate.defect T̄ (FunctionalInequalities.KLS.LogConcave.PoissonIterate.iter T̄ f (k - ℓ.val - 1)) := by ring
