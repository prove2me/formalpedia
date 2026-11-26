-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.balance_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:55:50.52866+00:00
-- url     : https://prove2.me/submissions/4ea1f7f8-4339-4018-9dbb-44001f92a37f

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_lower_lt_upper
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_root_product
public import Theorems.Thm_CSeparatedNPComplete_SquarePartition_root_product


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution {n : ℕ} (a : Fin n → ℕ) (p q : Vec n) :
    dot (Fin.append p q) (values a) - dot (values a) 1 / 2 =
      ∑ i, ((p i + q i - 1) * (base a : ℝ) ^ (2 * n + 2 * i.val + 2) +
        (2 * (p i - q i) * (a i : ℝ) * (base a : ℝ) ^ (2 * n) +
          (p i + q i - 1) * (lower a i : ℝ) ^ 2)) := by
  simp only [dot, values, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    Pi.one_apply, mul_one]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hroot : (upper a i : ℝ) * (lower a i : ℝ) = (a i : ℝ) * (base a : ℝ) ^ (2 * n) := by
    exact_mod_cast root_product a i
  have hu : (upper a i : ℝ) ^ 2 = (base a : ℝ) ^ (2 * n + 2 * i.val + 2) := by
    simp only [upper, Nat.cast_pow, ← pow_mul]
    congr 1
    omega
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_add, Nat.cast_sub (lower_lt_upper a i).le]
  calc
    _ = (p i + q i - 1) * (upper a i : ℝ) ^ 2 +
        2 * (p i - q i) * ((upper a i : ℝ) * (lower a i : ℝ)) +
        (p i + q i - 1) * (lower a i : ℝ) ^ 2 := by ring
    _ = _ := by rw [hu, hroot]; ring
end CSeparatedNPComplete.SquareReduction
