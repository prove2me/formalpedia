-- Prove2me | solution 1 for CatalyticTreeEval.Main.balanced_parameter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T02:59:07.795196+00:00
-- url     : https://prove2.me/submissions/a69144da-ea2c-4b8a-83de-e6d87884be42

import Definitions.Def_CatalyticTreeEval_BalancedParameters

set_option autoImplicit false


namespace CatalyticTreeEval.Main

private theorem balancedRoot_pos {t : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (w : ℕ) (hw : 0 < w) : 0 < balancedRoot p w := by
  have hm : 0 < modulus p := Finset.prod_pos (fun i _ => (hp.2.1 i).pos)
  apply Nat.lt_of_lt_of_le (by decide : 0 < 1)
  apply (Nat.le_nthRoot_iff hp.1.ne').2
  rw [one_pow]
  have hpositive : 0 < modulus p * w := Nat.mul_pos hm hw
  omega

private theorem balanced_primePower_le {t : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (w : ℕ) (hw : 0 < w) (i : Fin t) :
    p i ^ balancedExponents p w i ≤ balancedRoot p w :=
  Nat.pow_log_le_self _ (balancedRoot_pos p hp w hw).ne'

private theorem balanced_primePower_mul_gt {t : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (w : ℕ) (i : Fin t) :
    balancedRoot p w < p i * p i ^ balancedExponents p w i := by
  simpa [balancedExponents, pow_succ'] using
    Nat.lt_pow_succ_log_self (hp.2.1 i).one_lt (balancedRoot p w)

private theorem balanced_primePower_product_gt {t : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (w : ℕ) : w < ∏ i, p i ^ balancedExponents p w i := by
  have hm : 0 < modulus p := Finset.prod_pos (fun i _ => (hp.2.1 i).pos)
  have hprod : (balancedRoot p w + 1) ^ t ≤ ∏ i, p i * p i ^ balancedExponents p w i := by
    calc
      (balancedRoot p w + 1) ^ t = ∏ _i : Fin t, (balancedRoot p w + 1) := by simp
      _ ≤ ∏ i, p i * p i ^ balancedExponents p w i := by
        apply Finset.prod_le_prod'
        intro i hi
        exact Nat.succ_le_of_lt (balanced_primePower_mul_gt p hp w i)
  have hlt := (Nat.lt_pow_nthRoot_add_one hp.1.ne' (modulus p * w)).trans_le hprod
  rw [Finset.prod_mul_distrib] at hlt
  exact (Nat.mul_lt_mul_left hm).mp hlt

private theorem balanced_delta_le {t : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (w : ℕ) (hw : 0 < w) : delta p (balancedExponents p w) ≤ balancedRoot p w := by
  apply Finset.sup_le
  intro q hq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
  exact balanced_primePower_le p hp w hw i

private theorem balancedRoot_le_rpow {t : ℕ} (p : Fin t → ℕ) (hp : PrimeData p) (w : ℕ) :
    (balancedRoot p w : ℝ) ≤ ((modulus p * w : ℕ) : ℝ) ^ (1 / (t : ℝ)) := by
  rw [one_div]
  apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
    (by exact_mod_cast hp.1 : (0 : ℝ) < t)).2
  rw [Real.rpow_natCast]
  exact_mod_cast Nat.pow_nthRoot_le (a := modulus p * w) (Or.inl hp.1.ne')

private theorem balanced_delta_le_floor {t : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (w : ℕ) (hw : 0 < w) :
    delta p (balancedExponents p w) ≤
      ⌊((modulus p * w : ℕ) : ℝ) ^ (1 / (t : ℝ))⌋₊ := by
  apply (balanced_delta_le p hp w hw).trans
  exact (Nat.le_floor_iff (by positivity)).2 (balancedRoot_le_rpow p hp w)

private theorem binomialDimension_mono (H : ℕ) {a b : ℕ} (hab : a ≤ b) :
    binomialDimension H a ≤ binomialDimension H b := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
    (fun i hi hia => Nat.zero_le _)

private theorem balanced_dimension_le {t : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (w H : ℕ) (hw : 0 < w) :
    binomialDimension H (delta p (balancedExponents p w)) ≤
      binomialDimension H (⌊((modulus p * w : ℕ) : ℝ) ^ (1 / (t : ℝ))⌋₊ + 1) :=
  binomialDimension_mono H ((balanced_delta_le_floor p hp w hw).trans (Nat.le_succ _))

end CatalyticTreeEval.Main

open CatalyticTreeEval.Main

theorem solution {t : ℕ} (p : Fin t → ℕ) (hp : PrimeData p)
    (w H : ℕ) (hw : 0 < w) :
    w < ∏ i, p i ^ balancedExponents p w i ∧
    delta p (balancedExponents p w) ≤ ⌊((modulus p * w : ℕ) : ℝ) ^ (1 / (t : ℝ))⌋₊ ∧
    binomialDimension H (delta p (balancedExponents p w)) ≤
      binomialDimension H (⌊((modulus p * w : ℕ) : ℝ) ^ (1 / (t : ℝ))⌋₊ + 1) :=
  ⟨balanced_primePower_product_gt p hp w, balanced_delta_le_floor p hp w hw,
    balanced_dimension_le p hp w H hw⟩
