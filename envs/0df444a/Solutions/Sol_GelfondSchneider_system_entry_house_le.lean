-- Prove2me | solution 1 for GelfondSchneider.system_entry_house_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:06:19.670098+00:00
-- url     : https://prove2.me/submissions/28141bf1-21be-4c18-974e-93d4152b0277

import Mathlib

open NumberField

namespace GS_sysentry

section HouseBounds

variable {K : Type*} [Field K] [NumberField K]

/-- The house of a natural number is the number itself. -/
lemma house_natCast_eq (a : ℕ) : house (a : K) = a := by
  simpa using house_intCast (K := K) (a : ℤ)

/-- `house (a + b β) ≤ a + b · house β`. -/
lemma house_lin_le (a b : ℕ) (β : K) : house ((a : K) + (b : K) * β) ≤ a + b * house β := by
  calc house ((a : K) + (b : K) * β) ≤ house (a : K) + house ((b : K) * β) := house_add_le _ _
    _ = a + b * house β := by rw [house_natCast_eq, house_nat_mul]

/-- `house (a + b β) ≤ q (1 + house β)` when `a, b ≤ q`. -/
lemma house_lin_le_q (a b q : ℕ) (β : K) (haq : a ≤ q) (hbq : b ≤ q) :
    house ((a : K) + (b : K) * β) ≤ q * (1 + house β) := by
  have ha : (a : ℝ) ≤ q := by exact_mod_cast haq
  have hb : (b : ℝ) ≤ q := by exact_mod_cast hbq
  have hβ : 0 ≤ house β := house_nonneg β
  calc house ((a : K) + (b : K) * β) ≤ a + b * house β := house_lin_le a b β
    _ ≤ q + q * house β := add_le_add ha (mul_le_mul_of_nonneg_right hb hβ)
    _ = q * (1 + house β) := by ring

/-- Sub-multiplicativity for a product of three powers. -/
lemma house_prod3_le (x y z : K) (k e f : ℕ) :
    house (x ^ k * y ^ e * z ^ f) ≤ house x ^ k * house y ^ e * house z ^ f := by
  have h1 := house_mul_le (x ^ k * y ^ e) (z ^ f)
  have h2 := house_mul_le (x ^ k) (y ^ e)
  have h3 := house_pow_le x k
  have h4 := house_pow_le y e
  have h5 := house_pow_le z f
  have n2 := house_nonneg (y ^ e)
  have n3 := house_nonneg (z ^ f)
  have n4 : 0 ≤ house x ^ k := pow_nonneg (house_nonneg x) k
  have n5 : 0 ≤ house y ^ e := pow_nonneg (house_nonneg y) e
  calc house (x ^ k * y ^ e * z ^ f) ≤ house (x ^ k * y ^ e) * house (z ^ f) := h1
    _ ≤ (house (x ^ k) * house (y ^ e)) * house (z ^ f) := mul_le_mul_of_nonneg_right h2 n3
    _ ≤ (house x ^ k * house y ^ e) * house z ^ f :=
        mul_le_mul (mul_le_mul h3 h4 n2 n4) h5 n3 (mul_nonneg n4 n5)

/-- `house α ^ e ≤ (max 1 (house α)) ^ E` when `e ≤ E`. -/
lemma house_pow_le_max (α : K) (e E : ℕ) (h : e ≤ E) :
    house α ^ e ≤ (max 1 (house α)) ^ E :=
  (pow_le_pow_left₀ (house_nonneg α) (le_max_right _ _) e).trans
    (pow_le_pow_right₀ (le_max_left _ _) h)

/-- The house of a system entry, before using `q² = 2mn`. -/
lemma house_entry_le (α β γ : K) (a b j k q m : ℕ) (haq : a ≤ q) (hbq : b ≤ q) (hjm : j ≤ m) :
    house (((a : K) + (b : K) * β) ^ k * α ^ (a * j) * γ ^ (b * j)) ≤
      ((q : ℝ) * (1 + house β)) ^ k * (max 1 (house α) * max 1 (house γ)) ^ (q * m) := by
  have haj : a * j ≤ q * m := Nat.mul_le_mul haq hjm
  have hbj : b * j ≤ q * m := Nat.mul_le_mul hbq hjm
  have e1 : house ((a : K) + (b : K) * β) ^ k ≤ ((q : ℝ) * (1 + house β)) ^ k :=
    pow_le_pow_left₀ (house_nonneg _) (house_lin_le_q a b q β haq hbq) k
  have e2 := house_pow_le_max α (a * j) (q * m) haj
  have e3 := house_pow_le_max γ (b * j) (q * m) hbj
  have n2 : 0 ≤ house α ^ (a * j) := pow_nonneg (house_nonneg _) _
  have n3 : 0 ≤ house γ ^ (b * j) := pow_nonneg (house_nonneg _) _
  have hβ0 : 0 ≤ house β := house_nonneg β
  have n4 : 0 ≤ ((q : ℝ) * (1 + house β)) ^ k := by positivity
  have n5 : 0 ≤ (max 1 (house α)) ^ (q * m) :=
    pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  calc house (((a : K) + (b : K) * β) ^ k * α ^ (a * j) * γ ^ (b * j))
      ≤ house ((a : K) + (b : K) * β) ^ k * house α ^ (a * j) * house γ ^ (b * j) :=
        house_prod3_le _ _ _ _ _ _
    _ ≤ ((q : ℝ) * (1 + house β)) ^ k * (max 1 (house α)) ^ (q * m) *
          (max 1 (house γ)) ^ (q * m) :=
        mul_le_mul (mul_le_mul e1 e2 n2 n4) e3 n3 (mul_nonneg n4 n5)
    _ = ((q : ℝ) * (1 + house β)) ^ k * (max 1 (house α) * max 1 (house γ)) ^ (q * m) := by
        rw [mul_pow (max 1 (house α)) (max 1 (house γ)) (q * m), mul_assoc]

end HouseBounds

section RealBounds

/-- `√n ^ (n - 1) = n ^ ((n - 1) / 2)`, the right side being a real power. -/
lemma sqrt_pow_eq_rpow (n : ℕ) (hn : 0 < n) :
    Real.sqrt n ^ (n - 1) = (n : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne'), Nat.cast_one]
  congr 1
  ring

/-- From `q² = 2mn`: `q ≤ 2m √n`. -/
lemma q_le_two_m_sqrt (m n q : ℕ) (hm : 0 < m) (hq : q ^ 2 = 2 * m * n) :
    (q : ℝ) ≤ 2 * m * Real.sqrt n := by
  have h1 : (q : ℝ) ^ 2 = 2 * m * n := by exact_mod_cast hq
  have h2 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h3 : (2 * m * Real.sqrt n) ^ 2 = (2 * m) ^ 2 * (n : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have h4 : (2 * (m : ℝ)) * n ≤ (2 * m) ^ 2 * n := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
    nlinarith
  have h5 : (q : ℝ) ^ 2 ≤ (2 * m * Real.sqrt n) ^ 2 := by rw [h1, h3]; exact h4
  have h6 : 0 ≤ 2 * (m : ℝ) * Real.sqrt n := by positivity
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg q) h6 two_ne_zero).mp h5

/-- From `q² = 2mn`: `q m ≤ 2 m² n`. -/
lemma qm_le (m n q : ℕ) (hq : q ^ 2 = 2 * m * n) : q * m ≤ 2 * m ^ 2 * n := by
  have hq1 : q ≤ 2 * m * n := hq ▸ Nat.le_self_pow two_ne_zero q
  calc q * m ≤ 2 * m * n * m := Nat.mul_le_mul_right m hq1
    _ = 2 * m ^ 2 * n := by ring

/-- The constant is at least one. -/
lemma const_one_le (m : ℕ) (hm : 0 < m) (B X : ℝ) (hB : 1 ≤ B) (hX : 1 ≤ X) :
    1 ≤ 2 * (m : ℝ) * B * X ^ (2 * m ^ 2) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : (1 : ℝ) ≤ 2 * m := by linarith
  have hX' : 1 ≤ X ^ (2 * m ^ 2) := one_le_pow₀ hX
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h2 hB) hX'

/-- The purely real estimate. -/
lemma real_bound (m n q k : ℕ) (hm : 0 < m) (hn : 0 < n) (hq : q ^ 2 = 2 * m * n) (hk : k < n)
    (B X : ℝ) (hB : 1 ≤ B) (hX : 1 ≤ X) :
    ((q : ℝ) * B) ^ k * X ^ (q * m) ≤
      (2 * m * B * X ^ (2 * m ^ 2)) ^ n * (n : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hn1
  have hqle := q_le_two_m_sqrt m n q hm hq
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hD : 1 ≤ 2 * (m : ℝ) * B := by
    have h2 : (1 : ℝ) ≤ 2 * m := by linarith
    exact one_le_mul_of_one_le_of_one_le h2 hB
  have hT : 1 ≤ 2 * (m : ℝ) * B * Real.sqrt n := one_le_mul_of_one_le_of_one_le hD hs1
  -- the linear factor
  have e1 : ((q : ℝ) * B) ^ k ≤ (2 * (m : ℝ) * B * Real.sqrt n) ^ k := by
    apply pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg q) hB0)
    calc (q : ℝ) * B ≤ 2 * m * Real.sqrt n * B := mul_le_mul_of_nonneg_right hqle hB0
      _ = 2 * m * B * Real.sqrt n := by ring
  have e2 : (2 * (m : ℝ) * B * Real.sqrt n) ^ k ≤ (2 * (m : ℝ) * B * Real.sqrt n) ^ (n - 1) :=
    pow_le_pow_right₀ hT (by omega)
  have e3 : (2 * (m : ℝ) * B * Real.sqrt n) ^ (n - 1) ≤
      (2 * (m : ℝ) * B) ^ n * Real.sqrt n ^ (n - 1) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD (by omega)) (by positivity)
  -- the powers of α and γ
  have e4 : X ^ (q * m) ≤ (X ^ (2 * m ^ 2)) ^ n := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hX (qm_le m n q hq)
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have n2 : 0 ≤ X ^ (q * m) := pow_nonneg hX0 _
  have n3 : 0 ≤ (2 * (m : ℝ) * B) ^ n * Real.sqrt n ^ (n - 1) := by positivity
  calc ((q : ℝ) * B) ^ k * X ^ (q * m)
      ≤ ((2 * (m : ℝ) * B) ^ n * Real.sqrt n ^ (n - 1)) * (X ^ (2 * m ^ 2)) ^ n :=
        mul_le_mul (e1.trans (e2.trans e3)) e4 n2 n3
    _ = (2 * m * B * X ^ (2 * m ^ 2)) ^ n * Real.sqrt n ^ (n - 1) := by
        rw [mul_pow (2 * (m : ℝ) * B)]
        ring
    _ = (2 * m * B * X ^ (2 * m ^ 2)) ^ n * (n : ℝ) ^ (((n : ℝ) - 1) / 2) := by
        rw [sqrt_pow_eq_rpow n hn]

end RealBounds

end GS_sysentry

open GS_sysentry in
theorem solution (K : Type*) [Field K] [NumberField K] (α' β' γ' : K)
    (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n q a b j k : ℕ, 0 < n → q ^ 2 = 2 * m * n →
      1 ≤ a → a ≤ q → 1 ≤ b → b ≤ q → 1 ≤ j → j ≤ m → k < n →
      house (((a : K) + (b : K) * β') ^ k * α' ^ (a * j) * γ' ^ (b * j)) ≤
        C ^ n * (n : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  have hB : 1 ≤ 1 + house β' := le_add_of_nonneg_right (house_nonneg β')
  have hX : 1 ≤ max 1 (house α') * max 1 (house γ') :=
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
  refine ⟨2 * m * (1 + house β') * (max 1 (house α') * max 1 (house γ')) ^ (2 * m ^ 2),
    const_one_le m hm _ _ hB hX, ?_⟩
  intro n q a b j k hn hq _ haq _ hbq _ hjm hk
  exact (house_entry_le α' β' γ' a b j k q m haq hbq hjm).trans
    (real_bound m n q k hm hn hq hk _ _ hB hX)

#print axioms solution
