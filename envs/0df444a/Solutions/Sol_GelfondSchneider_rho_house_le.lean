-- Prove2me | solution 1 for GelfondSchneider.rho_house_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:06:28.477736+00:00
-- url     : https://prove2.me/submissions/9046536c-9f7a-4ccb-8531-fd38e36a9f8c

import Mathlib

open NumberField

namespace GS_rhohouse

section HouseLemmas

variable {K : Type*} [Field K] [NumberField K]

lemma house_one_eq : house (1 : K) = 1 := by
  have h := house_intCast (K := K) 1
  simpa using h

lemma house_natCast_eq (c : ℕ) : house (c : K) = c := by
  have h := house_nat_mul (1 : K) c
  rw [mul_one, house_one_eq, mul_one] at h
  exact h

/-- Submultiplicativity of the house on one term, with bounds for each factor. -/
lemma house_term_le (x X y z : K) (r e₁ e₂ : ℕ) (H P Y Z : ℝ)
    (hx : house x ≤ H) (hX : house X ≤ P) (hy : house y ^ e₁ ≤ Y) (hz : house z ^ e₂ ≤ Z) :
    house (x * X ^ r * y ^ e₁ * z ^ e₂) ≤ H * P ^ r * Y * Z := by
  have n1 := house_nonneg x
  have n2 := house_nonneg X
  have n3 := house_nonneg y
  have n4 := house_nonneg z
  have s1 : house (x * X ^ r * y ^ e₁ * z ^ e₂) ≤
      house x * house X ^ r * house y ^ e₁ * house z ^ e₂ := by
    calc house (x * X ^ r * y ^ e₁ * z ^ e₂)
        ≤ house (x * X ^ r * y ^ e₁) * house (z ^ e₂) := house_mul_le _ _
      _ ≤ (house (x * X ^ r) * house (y ^ e₁)) * house (z ^ e₂) :=
          mul_le_mul_of_nonneg_right (house_mul_le _ _) (house_nonneg _)
      _ ≤ (house x * house (X ^ r) * house (y ^ e₁)) * house (z ^ e₂) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (house_mul_le _ _) (house_nonneg _)) (house_nonneg _)
      _ ≤ house x * house X ^ r * house y ^ e₁ * house z ^ e₂ := by
          apply mul_le_mul _ (house_pow_le _ _) (house_nonneg _)
            (mul_nonneg (mul_nonneg n1 (pow_nonneg n2 _)) (pow_nonneg n3 _))
          apply mul_le_mul _ (house_pow_le _ _) (house_nonneg _)
            (mul_nonneg n1 (pow_nonneg n2 _))
          exact mul_le_mul_of_nonneg_left (house_pow_le _ _) n1
  refine s1.trans ?_
  have hH : 0 ≤ H := n1.trans hx
  have hP : 0 ≤ P := n2.trans hX
  have hPr : house X ^ r ≤ P ^ r := pow_le_pow_left₀ n2 hX r
  have hY : 0 ≤ Y := (pow_nonneg n3 _).trans hy
  apply mul_le_mul _ hz (pow_nonneg n4 _) (mul_nonneg (mul_nonneg hH (pow_nonneg hP _)) hY)
  apply mul_le_mul _ hy (pow_nonneg n3 _) (mul_nonneg hH (pow_nonneg hP _))
  exact mul_le_mul hx hPr (pow_nonneg n2 _) hH

lemma house_lin_le (β : K) (a b q : ℕ) (ha : a < q) (hb : b < q) :
    house (((a : K) + 1) + ((b : K) + 1) * β) ≤ (q : ℝ) * (1 + house β) := by
  have e₁ : ((a : K) + 1) = ((a + 1 : ℕ) : K) := by push_cast; ring
  have e₂ : ((b : K) + 1) = ((b + 1 : ℕ) : K) := by push_cast; ring
  rw [e₁, e₂]
  have h1 : ((a + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast ha
  have h2 : ((b + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast hb
  have h3 := house_nonneg β
  calc house (((a + 1 : ℕ) : K) + ((b + 1 : ℕ) : K) * β)
      ≤ house (((a + 1 : ℕ) : K)) + house (((b + 1 : ℕ) : K) * β) := house_add_le _ _
    _ = ((a + 1 : ℕ) : ℝ) + ((b + 1 : ℕ) : ℝ) * house β := by
        rw [house_nat_mul, house_natCast_eq]
    _ ≤ (q : ℝ) + (q : ℝ) * house β := by
        have := mul_le_mul_of_nonneg_right h2 h3
        linarith
    _ = (q : ℝ) * (1 + house β) := by ring

lemma house_pow_le_max (y : K) (e N : ℕ) (h : e ≤ N) :
    house y ^ e ≤ (max 1 (house y)) ^ N :=
  (pow_le_pow_left₀ (house_nonneg y) (le_max_right _ _) e).trans
    (pow_le_pow_right₀ (le_max_left _ _) h)

lemma house_double_sum_le {q : ℕ} (f : Fin q → Fin q → K) (T : ℝ)
    (hf : ∀ a b, house (f a b) ≤ T) :
    house (∑ a : Fin q, ∑ b : Fin q, f a b) ≤ (q : ℝ) * ((q : ℝ) * T) := by
  calc house (∑ a : Fin q, ∑ b : Fin q, f a b)
      ≤ ∑ a : Fin q, house (∑ b : Fin q, f a b) := house_sum_le_sum_house _ _
    _ ≤ ∑ a : Fin q, ∑ b : Fin q, house (f a b) :=
        Finset.sum_le_sum fun a _ => house_sum_le_sum_house _ _
    _ ≤ ∑ _a : Fin q, ∑ _b : Fin q, T :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hf a b
    _ = (q : ℝ) * ((q : ℝ) * T) := by simp

end HouseLemmas

section RealLemmas

lemma rpow_half_mono {n r : ℕ} (hn : 1 ≤ n) (hnr : n ≤ r) :
    (n : ℝ) ^ (((n : ℝ) + 1) / 2) ≤ (r : ℝ) ^ (((r : ℝ) + 1) / 2) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnr' : (n : ℝ) ≤ r := by exact_mod_cast hnr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (hn.trans hnr)
  have he : (0 : ℝ) ≤ ((n : ℝ) + 1) / 2 := by positivity
  have he' : ((n : ℝ) + 1) / 2 ≤ ((r : ℝ) + 1) / 2 := by linarith
  exact (Real.rpow_le_rpow hn0 hnr' he).trans (Real.rpow_le_rpow_of_exponent_le hr1 he')

lemma q_pow_le {q r : ℕ} {M : ℝ} (hM : 1 ≤ M) (hq : (q : ℝ) ^ 2 ≤ M * r) :
    (q : ℝ) ^ r ≤ M ^ r * (r : ℝ) ^ ((r : ℝ) / 2) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hr2 : (0 : ℝ) ≤ (r : ℝ) / 2 := by positivity
  have e₁ : ((q : ℝ) ^ 2) ^ ((r : ℝ) / 2) = (q : ℝ) ^ r := by
    rw [← Real.rpow_natCast (q : ℝ) 2, ← Real.rpow_mul hq0, ← Real.rpow_natCast (q : ℝ) r]
    congr 1
    push_cast
    ring
  have e₂ : M ^ ((r : ℝ) / 2) ≤ M ^ r := by
    rw [← Real.rpow_natCast M r]
    exact Real.rpow_le_rpow_of_exponent_le hM (by linarith)
  rw [← e₁]
  calc ((q : ℝ) ^ 2) ^ ((r : ℝ) / 2) ≤ (M * r) ^ ((r : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) hq hr2
    _ = M ^ ((r : ℝ) / 2) * (r : ℝ) ^ ((r : ℝ) / 2) := Real.mul_rpow hM0 hr0
    _ ≤ M ^ r * (r : ℝ) ^ ((r : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right e₂ (Real.rpow_nonneg hr0 _)

lemma rpow_split {r : ℕ} (hr : 1 ≤ r) :
    (r : ℝ) ^ ((r : ℝ) + 3 / 2) =
      (r : ℝ) * ((r : ℝ) ^ (((r : ℝ) + 1) / 2) * (r : ℝ) ^ ((r : ℝ) / 2)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have e : (r : ℝ) + 3 / 2 = 1 + ((((r : ℝ) + 1) / 2) + (r : ℝ) / 2) := by ring
  rw [e, Real.rpow_add hr0, Real.rpow_add hr0, Real.rpow_one]

/-- The purely algebraic collection step, over opaque real quantities. -/
lemma combine (q M R c0n pn pr S b1 Y Z X C₀ : ℝ) (r : ℕ)
    (hq0 : 0 ≤ q) (hM0 : 0 ≤ M) (hR : 0 ≤ R) (hc0n : 0 ≤ c0n) (hpn : 0 ≤ pn) (hS : 0 ≤ S)
    (hb1 : 0 ≤ b1) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hX : 0 ≤ X) (hC₀ : 0 ≤ C₀)
    (h1 : q ^ 2 ≤ M * R) (h2 : c0n ≤ C₀ ^ r) (h3 : pn ≤ pr) (h4 : q ^ r ≤ M ^ r * S)
    (h5 : Y * Z ≤ X ^ r) (h6 : M ≤ M ^ r) :
    q * (q * (c0n * pn * (q * b1) ^ r * Y * Z)) ≤
      (M ^ 2 * C₀ * b1 * X) ^ r * (R * (pr * S)) := by
  have hpr : 0 ≤ pr := hpn.trans h3
  have hC0r : 0 ≤ C₀ ^ r := pow_nonneg hC₀ r
  have hMR : 0 ≤ M * R := mul_nonneg hM0 hR
  have hMr : 0 ≤ M ^ r := pow_nonneg hM0 r
  have hb1r : 0 ≤ b1 ^ r := pow_nonneg hb1 r
  have hXr : 0 ≤ X ^ r := pow_nonneg hX r
  have hqr : 0 ≤ q ^ r := pow_nonneg hq0 r
  calc q * (q * (c0n * pn * (q * b1) ^ r * Y * Z))
      = q ^ 2 * (c0n * pn) * (q ^ r * b1 ^ r) * (Y * Z) := by ring
    _ ≤ (M * R) * (C₀ ^ r * pr) * ((M ^ r * S) * b1 ^ r) * X ^ r := by
        apply mul_le_mul _ h5 (mul_nonneg hY hZ)
          (mul_nonneg (mul_nonneg hMR (mul_nonneg hC0r hpr)) (mul_nonneg (mul_nonneg hMr hS) hb1r))
        apply mul_le_mul _ (mul_le_mul_of_nonneg_right h4 hb1r) (mul_nonneg hqr hb1r)
          (mul_nonneg hMR (mul_nonneg hC0r hpr))
        exact mul_le_mul h1 (mul_le_mul h2 h3 hpn hC0r) (mul_nonneg hc0n hpn) hMR
    _ = M * (M ^ r * C₀ ^ r * b1 ^ r * X ^ r) * (R * (pr * S)) := by ring
    _ ≤ M ^ r * (M ^ r * C₀ ^ r * b1 ^ r * X ^ r) * (R * (pr * S)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hR (mul_nonneg hpr hS))
        exact mul_le_mul_of_nonneg_right h6
          (mul_nonneg (mul_nonneg (mul_nonneg hMr hC0r) hb1r) hXr)
    _ = (M ^ 2 * C₀ * b1 * X) ^ r * (R * (pr * S)) := by ring

lemma const_one_le {m : ℕ} (hm : 0 < m) {C₀ B A G : ℝ} (hC₀ : 1 ≤ C₀) (hB : 0 ≤ B)
    (hA : 1 ≤ A) (hG : 1 ≤ G) :
    1 ≤ (2 * (m : ℝ)) ^ 2 * C₀ * (1 + B) * (A * G) ^ (2 * m ^ 2) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hM : (1 : ℝ) ≤ 2 * (m : ℝ) := by linarith
  have h1 : (1 : ℝ) ≤ (2 * (m : ℝ)) ^ 2 := one_le_pow₀ hM
  have h2 : (1 : ℝ) ≤ 1 + B := by linarith
  have h3 : (1 : ℝ) ≤ (A * G) ^ (2 * m ^ 2) := one_le_pow₀ (one_le_mul_of_one_le_of_one_le hA hG)
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 hC₀) h2) h3

lemma final_bound (m n q r : ℕ) (hm : 0 < m) (hn : 0 < n) (hq : q ^ 2 = 2 * m * n)
    (hnr : n ≤ r) (C₀ B A G : ℝ) (hC₀ : 1 ≤ C₀) (hB : 0 ≤ B) (hA : 1 ≤ A) (hG : 1 ≤ G) :
    (q : ℝ) * ((q : ℝ) * (C₀ ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2) * ((q : ℝ) * (1 + B)) ^ r *
        A ^ (q * m) * G ^ (q * m))) ≤
      ((2 * (m : ℝ)) ^ 2 * C₀ * (1 + B) * (A * G) ^ (2 * m ^ 2)) ^ r *
        (r : ℝ) ^ ((r : ℝ) + 3 / 2) := by
  have hr : 1 ≤ r := lt_of_lt_of_le hn hnr
  -- natural-number facts
  have hq2n : q ^ 2 ≤ 2 * m * r := hq ▸ Nat.mul_le_mul_left _ hnr
  have hqle : q ≤ 2 * m * r := (Nat.le_self_pow (by norm_num) q).trans hq2n
  have hexp : q * m ≤ 2 * m ^ 2 * r := by
    calc q * m ≤ (2 * m * r) * m := Nat.mul_le_mul_right m hqle
      _ = 2 * m ^ 2 * r := by ring
  -- real facts
  have hq2 : (q : ℝ) ^ 2 ≤ (2 * (m : ℝ)) * r := by exact_mod_cast hq2n
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hM : (1 : ℝ) ≤ 2 * (m : ℝ) := by linarith
  have hAG : (1 : ℝ) ≤ A * G := one_le_mul_of_one_le_of_one_le hA hG
  have h5 : A ^ (q * m) * G ^ (q * m) ≤ ((A * G) ^ (2 * m ^ 2)) ^ r := by
    rw [← mul_pow, ← pow_mul]
    exact pow_le_pow_right₀ hAG hexp
  have h6 : C₀ ^ n ≤ C₀ ^ r := pow_le_pow_right₀ hC₀ hnr
  have h7 := rpow_half_mono hn hnr
  have h8 := q_pow_le hM hq2
  have h9 : 2 * (m : ℝ) ≤ (2 * (m : ℝ)) ^ r := le_self_pow₀ hM (by omega)
  rw [rpow_split hr]
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  exact combine (q : ℝ) (2 * (m : ℝ)) (r : ℝ) (C₀ ^ n) ((n : ℝ) ^ (((n : ℝ) + 1) / 2))
    ((r : ℝ) ^ (((r : ℝ) + 1) / 2)) ((r : ℝ) ^ ((r : ℝ) / 2)) (1 + B) (A ^ (q * m))
    (G ^ (q * m)) ((A * G) ^ (2 * m ^ 2)) C₀ r (Nat.cast_nonneg q) (by linarith) hr0
    (pow_nonneg (by linarith) n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (Real.rpow_nonneg hr0 _) (by linarith) (pow_nonneg (by linarith) _)
    (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _) (by linarith)
    hq2 h6 h7 h8 h5 h9

end RealLemmas

end GS_rhohouse

open GS_rhohouse in
theorem solution (K : Type*) [Field K] [NumberField K] (α' β' γ' : K) (m : ℕ) (hm : 0 < m)
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n q r l₀ : ℕ) (η : Fin q → Fin q → 𝓞 K),
      0 < n → q ^ 2 = 2 * m * n → n ≤ r → 1 ≤ l₀ → l₀ ≤ m →
      (∀ a b, house (η a b : K) ≤ C₀ ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) →
      house (∑ a : Fin q, ∑ b : Fin q, (η a b : K) *
          (((a : ℕ) + 1 : K) + ((b : ℕ) + 1 : K) * β') ^ r *
          α' ^ (((a : ℕ) + 1) * l₀) * γ' ^ (((b : ℕ) + 1) * l₀)) ≤
        C ^ r * (r : ℝ) ^ ((r : ℝ) + 3 / 2) := by
  refine ⟨(2 * (m : ℝ)) ^ 2 * C₀ * (1 + house β') *
      (max 1 (house α') * max 1 (house γ')) ^ (2 * m ^ 2),
    const_one_le hm hC₀ (house_nonneg β') (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro n q r l₀ η hn hq hnr _hl₁ hlm hη
  refine (house_double_sum_le _
    (C₀ ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2) * ((q : ℝ) * (1 + house β')) ^ r *
      max 1 (house α') ^ (q * m) * max 1 (house γ') ^ (q * m)) ?_).trans
    (final_bound m n q r hm hn hq hnr C₀ (house β') _ _ hC₀ (house_nonneg β')
      (le_max_left _ _) (le_max_left _ _))
  intro a b
  exact house_term_le _ _ _ _ r _ _ _ _ _ _ (hη a b)
    (house_lin_le β' a b q a.isLt b.isLt)
    (house_pow_le_max α' _ _ (Nat.mul_le_mul (Nat.succ_le_of_lt a.isLt) hlm))
    (house_pow_le_max γ' _ _ (Nat.mul_le_mul (Nat.succ_le_of_lt b.isLt) hlm))

#print axioms solution
