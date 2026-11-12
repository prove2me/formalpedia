-- Prove2me | solution 1 for FiniteSampleDependence.Rigidity.row_cone_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:00:26.286674+00:00
-- url     : https://prove2.me/submissions/620bdd48-2d1f-4f51-8d9d-9ed4d6359ac6

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Theorems.Thm_FiniteSampleDependence_Rigidity_zero_row_vanishing
import Theorems.Thm_FiniteSampleDependence_Rigidity_nonnegativity_permutation_invariance

section
set_option autoImplicit false

namespace FiniteSampleDependence.Rigidity

open Matrix

lemma tau_mul {n m : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (hT : ∀ j, ∑ i, T i j = 1)
    (V : Matrix (Fin n) (Fin m) ℝ) : tau (T * V) = tau V := by
  unfold tau
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  calc ∑ α, ∑ i, ∑ k, T i k * V k α = ∑ α, ∑ k, ∑ i, T i k * V k α := by
        refine Finset.sum_congr rfl fun α _ => Finset.sum_comm
    _ = ∑ α, ∑ k, V k α := by
        refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_mul, hT k, one_mul]
    _ = ∑ i, ∑ α, V i α := by rw [Finset.sum_comm]

theorem chk_row_cone_vanishing {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (F : Matrix (Fin n) (Fin m) ℝ → ℝ) (hC1 : IsC1Extendable F) (hF : LFDPI F) (hIZ : IZ F)
    (U : Matrix (Fin n) (Fin m) ℝ) (hU : U ∈ simplex n m) (k : Fin n)
    (hcone : ∃ c : Fin n → ℝ, (∀ i, 0 ≤ c i) ∧
      ∀ α, U k α = ∑ i ∈ Finset.univ.erase k, c i * U i α) :
    F U = 0 := by
  obtain ⟨c, hc0, hck⟩ := hcone
  let U' : Matrix (Fin n) (Fin m) ℝ := Matrix.of fun i α => if i = k then 0 else (1 + c i) * U i α
  let T : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j =>
    if i = j then (if i = k then 1 else 1 / (1 + c i))
    else if i = k then c j / (1 + c j) else 0
  have hc1 : ∀ i, 0 < 1 + c i := fun i => by linarith [hc0 i]
  have hT : IsColumnStochastic T := by
    refine ⟨fun i j => ?_, fun j => ?_⟩
    · simp only [T, Matrix.of_apply]
      have := hc1 i
      have := hc1 j
      have := hc0 j
      split_ifs <;> positivity
    · by_cases hj : j = k
      · subst hj
        rw [Finset.sum_eq_single j]
        · simp [T]
        · intro i _ hi; simp [T, hi]
        · simp
      · rw [Finset.sum_eq_add_of_mem j k (Finset.mem_univ _) (Finset.mem_univ _) hj]
        · have := hc1 j
          simp [T, hj, Ne.symm hj]
          field_simp
        · intro i _ hi
          simp [T, hi.1, hi.2]
  have hTU : T * U' = U := by
    ext i α
    simp only [Matrix.mul_apply]
    by_cases hi : i = k
    · subst hi
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp only [U', Matrix.of_apply, if_true, mul_zero, zero_add]
      rw [hck α]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjk : j ≠ i := Finset.ne_of_mem_erase hj
      have := hc1 j
      simp [T, hjk, Ne.symm hjk]
      field_simp
    · rw [Finset.sum_eq_single i]
      · have := hc1 i
        simp [T, U', hi]
        field_simp
      · intro j _ hj
        simp [T, Ne.symm hj, hi]
      · simp
  have hU' : U' ∈ simplex n m := by
    refine ⟨fun i α => ?_, ?_⟩
    · simp only [U', Matrix.of_apply]
      have := hc1 i
      have := hU.1 i α
      split_ifs <;> positivity
    · rw [← tau_mul T hT.2 U', hTU]; exact hU.2
  have h0 : F U' = 0 :=
    zero_row_vanishing hn hm F hC1 hF hIZ U' hU' ⟨k, fun α => by simp [U']⟩
  have hle := hF U' hU' T hT
  rw [hTU, h0] at hle
  have hnn := (nonnegativity_permutation_invariance hn hm F).1 hF hIZ U hU
  exact le_antisymm hle hnn

end FiniteSampleDependence.Rigidity
end

theorem solution : type_of% @FiniteSampleDependence.Rigidity.chk_row_cone_vanishing := @FiniteSampleDependence.Rigidity.chk_row_cone_vanishing
