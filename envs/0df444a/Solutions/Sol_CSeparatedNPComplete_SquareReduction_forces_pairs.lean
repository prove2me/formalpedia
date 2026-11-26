-- Prove2me | solution 1 for CSeparatedNPComplete.SquareReduction.forces_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:56:39.41051+00:00
-- url     : https://prove2.me/submissions/43fd5c4b-2722-4d58-a631-95087f1f6f41

module
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_base_ge_two
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_digits_vanish
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_balance_identity
public import Theorems.Thm_CSeparatedNPComplete_SquareReduction_lower_square_bound

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete CSeparatedNPComplete.SquareReduction
namespace CSeparatedNPComplete.SquareReduction
theorem _root_.solution {n : ℕ} (a : Fin n → ℕ) (p q : Vec n)
    (hp : is_binary p) (hq : is_binary q)
    (hbal : dot (Fin.append p q) (values a) = dot (values a) 1 / 2) :
    ∀ i, p i + q i = 1 := by
  let d : Fin n → ℝ := fun i => p i + q i - 1
  let C : ℝ := ∑ i, (2 * (a i : ℝ) + (a i : ℝ) ^ 2)
  let e : ℝ := ∑ i, (2 * (p i - q i) * (a i : ℝ) * (base a : ℝ) ^ (2 * n) +
    d i * (lower a i : ℝ) ^ 2)
  have hK : 1 ≤ (base a : ℝ) := by exact_mod_cast (show 1 ≤ base a by have := base_ge_two a; omega)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbase : (base a : ℝ) = 2 + n + C := by
    simp [base, C, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow,
      Finset.sum_add_distrib, Finset.mul_sum, add_assoc]
  have hlarge : (n : ℝ) + C < (base a : ℝ) ^ 2 := by nlinarith
  have hd (i : Fin n) : d i = -1 ∨ d i = 0 ∨ d i = 1 := by
    rcases hp i with h | h <;> rcases hq i with h' | h' <;> simp [d, h, h']
  have habsd (i : Fin n) : |d i| ≤ 1 := by
    rcases hd i with h | h | h <;> simp [h]
  have habspq (i : Fin n) : |p i - q i| ≤ 1 := by
    rcases hp i with h | h <;> rcases hq i with h' | h' <;> norm_num [h, h']
  have he : |e| ≤ C * (base a : ℝ) ^ (2 * n) := by
    dsimp [e, C]
    rw [Finset.sum_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ |2 * (p i - q i) * (a i : ℝ) * (base a : ℝ) ^ (2 * n)| +
          |d i * (lower a i : ℝ) ^ 2| := abs_add_le _ _
      _ ≤ 2 * (a i : ℝ) * (base a : ℝ) ^ (2 * n) +
          (a i : ℝ) ^ 2 * (base a : ℝ) ^ (2 * n) := by
        simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
          abs_of_nonneg (show 0 ≤ (a i : ℝ) by positivity), abs_of_nonneg (show 0 ≤ (base a : ℝ) ^ (2 * n) by positivity),
          abs_of_nonneg (sq_nonneg (lower a i : ℝ))]
        apply add_le_add
        · calc
            _ ≤ 2 * 1 * (a i : ℝ) * (base a : ℝ) ^ (2 * n) := by gcongr; exact habspq i
            _ = _ := by ring
        · calc
            _ ≤ 1 * (lower a i : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (habsd i) (sq_nonneg _)
            _ ≤ _ := by simpa using lower_square_bound a i
      _ = _ := by ring
  have hz : (∑ i, d i * (base a : ℝ) ^ (2 * n + 2 * i.val + 2)) + e = 0 := by
    have h := balance_identity a p q
    rw [hbal, sub_self] at h
    simpa only [d, e, Finset.sum_add_distrib] using h.symm
  have hv := digits_vanish (base a : ℝ) C hK hC hlarge d hd e he hz
  intro i
  have := hv i
  dsimp [d] at this
  linarith
end CSeparatedNPComplete.SquareReduction
