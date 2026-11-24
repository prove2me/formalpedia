-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.nearestPlane_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:51:15.539793+00:00
-- url     : https://prove2.me/submissions/8de7b2bf-6fc6-4933-b100-dccc3b2c7e5c

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_TransvectionIsometry
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_ExistsSumOfMemSpanImage
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_exists_orth_split
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.LatticeBaseChangeAlt
open Finset
section aux
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
private theorem exists_sum_repr_of_mem_span_image {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (v : ι → M) (T : Finset ι) (x : M) (hx : x ∈ Submodule.span R (v '' (T : Set ι))) :
    ∃ r : ι → R, x = ∑ i ∈ T, r i • v i := by
  classical
  let S : Submodule R M :=
    { carrier := {y | ∃ r : ι → R, y = ∑ i ∈ T, r i • v i}
      add_mem' := by
        rintro y₁ y₂ ⟨r₁, rfl⟩ ⟨r₂, rfl⟩
        exact ⟨r₁ + r₂, by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c y ⟨r, rfl⟩
        exact ⟨c • r, by simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]⟩ }
  have hle : Submodule.span R (v '' (T : Set ι)) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    show ∃ r : ι → R, v j = ∑ i ∈ T, r i • v i
    refine ⟨fun i => if i = j then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · intro hjT
      exact absurd (Finset.mem_coe.mp hj) hjT
  exact hle hx
end aux
end Formalism.LatticeBaseChangeAlt
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Finset
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution {ι : Type*} [DecidableEq ι] (v : ι → V) (T : Finset ι) :
    ∀ x ∈ Submodule.span ℝ (v '' (T : Set ι)),
      ∃ c : ι → ℤ, ‖x - ∑ i ∈ T, (c i : ℝ) • v i‖ ^ 2 ≤ (1 / 4) * ∑ i ∈ T, ‖v i‖ ^ 2 := by
  refine Finset.induction_on T ?_ ?_
  · intro x hx
    refine ⟨0, ?_⟩
    simp at hx
    subst hx
    simp
  · intro a s ha ih x hx
    obtain ⟨r, hr⟩ := exists_sum_repr_of_mem_span_image v (insert a s) x hx
    rw [Finset.sum_insert ha] at hr
    obtain ⟨w, hw, z, hz, hwz, hzle⟩ := exists_orth_split v s (v a)
    have hyK : (∑ i ∈ s, r i • v i) ∈ Submodule.span ℝ (v '' (s : Set ι)) :=
      Submodule.sum_mem _ (fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩))
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = round (r a) := ⟨_, rfl⟩
    have hy'K : (∑ i ∈ s, r i • v i) + (r a - k) • w ∈ Submodule.span ℝ (v '' (s : Set ι)) :=
      Submodule.add_mem _ hyK (Submodule.smul_mem _ _ hw)
    obtain ⟨c', hc'⟩ := ih _ hy'K
    have hSK : (∑ i ∈ s, (c' i : ℝ) • v i) ∈ Submodule.span ℝ (v '' (s : Set ι)) :=
      Submodule.sum_mem _ (fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩))
    have heK := Submodule.sub_mem _ hy'K hSK
    refine ⟨fun i => if i = a then k else c' i, ?_⟩
    have hsum : ∑ i ∈ s, (((if i = a then k else c' i : ℤ)) : ℝ) • v i
        = ∑ i ∈ s, (c' i : ℝ) • v i := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hia : i ≠ a := fun h => ha (by rw [← h]; exact hi)
      rw [if_neg hia]
    show ‖x - ∑ i ∈ insert a s, (((if i = a then k else c' i : ℤ)) : ℝ) • v i‖ ^ 2
      ≤ (1 / 4) * ∑ i ∈ insert a s, ‖v i‖ ^ 2
    rw [Finset.sum_insert ha, Finset.sum_insert ha, if_pos rfl, hsum]
    have hdecomp : x - ((k : ℝ) • v a + ∑ i ∈ s, (c' i : ℝ) • v i) =
        (r a - k) • z + ((∑ i ∈ s, r i • v i) + (r a - k) • w - ∑ i ∈ s, (c' i : ℝ) • v i) := by
      rw [hr, hwz]
      module
    have horth : inner ℝ ((r a - k) • z)
        ((∑ i ∈ s, r i • v i) + (r a - k) • w - ∑ i ∈ s, (c' i : ℝ) • v i) = 0 := by
      rw [real_inner_smul_left, real_inner_comm, hz _ heK, mul_zero]
    have hround : (r a - k) ^ 2 ≤ 1 / 4 := by
      have h1 : |r a - k| ≤ 1 / 2 := by
        rw [hk]
        exact abs_sub_round (r a)
      nlinarith [sq_abs (r a - k), abs_nonneg (r a - k),
        mul_le_mul_of_nonneg_left h1 (abs_nonneg (r a - k))]
    rw [hdecomp, norm_add_sq_real, horth, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h2 := mul_le_mul_of_nonneg_right hround (sq_nonneg ‖z‖)
    have h3 := mul_le_mul_of_nonneg_left hzle (by norm_num : (0 : ℝ) ≤ 1 / 4)
    linarith
end Formalism.LatticeBaseChangeAlt
