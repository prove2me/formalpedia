-- Prove2me | solution 1 for ExplicitExpanders.Attach.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T04:14:49.820235+00:00
-- url     : https://prove2.me/submissions/908895c1-c2fb-48e8-a616-5ee6ba14ae0a

import Mathlib
import Definitions.Def_ExplicitExpanders_Attach_IsNDLambda
import Definitions.Def_ExplicitExpanders_Attach_attachMatrix

set_option autoImplicit false

namespace C7e10efeAux

open Matrix ExplicitExpanders.Attach

theorem quad_eq {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} (W : Fin r → Finset V)
    (f : V ⊕ Fin r → ℝ) :
    f ⬝ᵥ (matR W *ᵥ f) = 2 * ∑ i, ∑ v ∈ W i, f (Sum.inr i) * f (Sum.inl v) := by
  simp only [dotProduct, mulVec, Fintype.sum_sum_type, matR, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, incidence, transpose_apply,
    of_apply, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, add_zero, ite_mul,
    one_mul]
  rw [two_mul]
  congr 1
  · simp_rw [Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter]
    exact Finset.sum_congr (by ext; simp) fun v _ => mul_comm _ _
  · simp_rw [Finset.mul_sum, mul_ite, mul_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter]
    exact Finset.sum_congr (by ext; simp) fun v _ => rfl

theorem amgm (a b x : ℝ) (hx : 0 < x) : 2 * |a * b| ≤ a ^ 2 / x + x * b ^ 2 := by
  have key : ∀ c : ℝ, 2 * (a * c) ≤ a ^ 2 / x + x * c ^ 2 := by
    intro c
    have h1 : 0 ≤ (a - x * c) ^ 2 / x := div_nonneg (sq_nonneg _) hx.le
    have h2 : (a - x * c) ^ 2 / x = a ^ 2 / x + x * c ^ 2 - 2 * (a * c) := by
      field_simp; ring
    linarith
  rcases abs_cases (a * b) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; exact key b
  · rw [h]; have := key (-b); nlinarith [this]

end C7e10efeAux

open Matrix ExplicitExpanders.Attach in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (p r : ℕ) (W : Fin r → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j)) (hcard : ∀ i, (W i).card = p + 2)
    (f : V ⊕ Fin r → ℝ) (x : ℝ) (hx : 0 < x) :
    f ⬝ᵥ (matR W *ᵥ f) = 2 * ∑ i, ∑ v ∈ W i, f (Sum.inr i) * f (Sum.inl v) ∧
      |f ⬝ᵥ (matR W *ᵥ f)| ≤
        ((p : ℝ) + 2) / x * ∑ i, f (Sum.inr i) ^ 2 +
          x * ∑ v ∈ attachedSet W, f (Sum.inl v) ^ 2 := by
  have hq := C7e10efeAux.quad_eq W f
  refine ⟨hq, ?_⟩
  rw [hq, abs_mul, abs_two]
  have hW : ∑ v ∈ attachedSet W, f (Sum.inl v) ^ 2
      = ∑ i, ∑ v ∈ W i, f (Sum.inl v) ^ 2 := by
    unfold attachedSet
    rw [Finset.sum_biUnion]
    intro i _ j _ hij
    exact hdisj i j hij
  rw [hW]
  calc 2 * |∑ i, ∑ v ∈ W i, f (Sum.inr i) * f (Sum.inl v)|
      ≤ 2 * ∑ i, ∑ v ∈ W i, |f (Sum.inr i) * f (Sum.inl v)| := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        gcongr with i _
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ v ∈ W i, 2 * |f (Sum.inr i) * f (Sum.inl v)| := by
        rw [Finset.mul_sum]; simp only [Finset.mul_sum]
    _ ≤ ∑ i, ∑ v ∈ W i, (f (Sum.inr i) ^ 2 / x + x * f (Sum.inl v) ^ 2) := by
        gcongr with i _ v _
        exact C7e10efeAux.amgm _ _ x hx
    _ = ((p : ℝ) + 2) / x * ∑ i, f (Sum.inr i) ^ 2 +
          x * ∑ i, ∑ v ∈ W i, f (Sum.inl v) ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul,
          Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast; ring
