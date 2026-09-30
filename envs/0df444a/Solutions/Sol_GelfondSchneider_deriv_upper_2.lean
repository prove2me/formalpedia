-- Prove2me | solution 2 for GelfondSchneider.deriv_upper
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T04:14:41.74513+00:00
-- url     : https://prove2.me/submissions/d6ebdcf3-0910-441f-a1ce-1eba118faf6f

import Mathlib
import Theorems.Thm_Transcendence_expPoly_grid_estimate

/-!
# `GelfondSchneider.deriv_upper` from `Transcendence.expPoly_grid_estimate`

Apply the grid estimate to `F(z) = E(z + 1)` on the one-dimensional grid `{0, …, m - 1}`
(`y = 1`, `t = A = m`, vanishing order `r`), at the target `l₀ - 1`, with `u = 2 + r/q` and
`Z = (m + 1)(u + 1)`. The shift turns the coefficients into `c_{ab} e^{ω_{ab}}`, of total mass at
most `q² B e^{Kq}`, where `K = (1 + ‖β‖)‖l‖`, `B = C₀ⁿ n^{(n+1)/2}` and `‖ω_{ab}‖ ≤ Kq`.
Then `1/(u - 1) = q/(q + r) ≤ q/r ≤ √(2m) r^{-1/2}`, and `r! ≤ r^r`, `q² ≤ 2mr`,
`n^{(n+1)/2} ≤ r^{(r+1)/2}` add up to the exponent `r - mr/2 + 1 + (r + 1)/2 = r(3 - m)/2 + 3/2`,
with `C = 4m · √(2m)^m · C₀ · e^{K((m+1)(6m+1)+2m)}`.
-/

namespace W5_derivUpper

/-- Arithmetic (reals only): the final combination of the grid bound. -/
lemma arith_combine (m : ℕ) (hm : 0 < m) (K : ℝ) (hK : 0 ≤ K) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n q r : ℕ, 0 < n → q ^ 2 = 2 * m * n → n ≤ r →
      ∀ u : ℝ, u = 2 + (r : ℝ) / q →
      (r.factorial : ℝ) * 2 * (1 / (u - 1)) ^ (m * r) *
        ((q : ℝ) ^ 2 * (C₀ ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2) * Real.exp (K * q)) *
          Real.exp (K * q * ((m + 1) * (u + 1))))
      ≤ C ^ r * (r : ℝ) ^ ((r : ℝ) * (3 - m) / 2 + 3 / 2) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set s : ℝ := Real.sqrt (2 * m) with hs
  have hs1 : 1 ≤ s := by rw [hs, Real.one_le_sqrt]; linarith
  set E₁ : ℝ := Real.exp (K * ((m + 1) * (6 * m + 1) + 2 * m)) with hE₁
  have hE₁1 : 1 ≤ E₁ := Real.one_le_exp (by positivity)
  refine ⟨4 * m * s ^ m * C₀ * E₁, ?_, ?_⟩
  · have h4 : (1 : ℝ) ≤ 4 * m := by linarith
    have h2 : (1 : ℝ) ≤ s ^ m := one_le_pow₀ hs1
    calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
      _ ≤ 4 * m * s ^ m * C₀ * E₁ := by gcongr
  intro n q r hn hq hnr u hu
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · exfalso
      subst h
      have h2 : 0 < 2 * m * n := by positivity
      simp at hq
      omega
    · exact h
  have hr1 : 1 ≤ r := le_trans hn hnr
  have hx1 : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hx0 : (0 : ℝ) < r := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hqpos : (0 : ℝ) < q := by linarith
  have hq2 : (q : ℝ) ^ 2 = 2 * m * n := by exact_mod_cast hq
  have hnx : (n : ℝ) ≤ r := by exact_mod_cast hnr
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq2x : (q : ℝ) ^ 2 ≤ 2 * m * r := by rw [hq2]; gcongr
  have hqx : (q : ℝ) ≤ 2 * m * r := by nlinarith
  -- P1 : r! ≤ r^r
  have P1 : (r.factorial : ℝ) ≤ (r : ℝ) ^ (r : ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast Nat.factorial_le_pow r
  -- P3 : the zero factor, `(1/(u-1))^(m r) ≤ (√(2m))^(m r) · r^(-m r/2)`
  have hu1 : u - 1 = (q + r) / q := by rw [hu]; field_simp; ring
  have hbase0 : 0 ≤ 1 / (u - 1) := by rw [hu1]; positivity
  have hb1 : 1 / (u - 1) ≤ q / r := by
    rw [hu1, one_div_div]
    exact div_le_div_of_nonneg_left hqpos.le hx0 (by linarith)
  have hqs : (q : ℝ) ≤ s * Real.sqrt r := by
    rw [hs, ← Real.sqrt_mul (show (0 : ℝ) ≤ 2 * m by positivity)]
    calc (q : ℝ) = Real.sqrt ((q : ℝ) ^ 2) := (Real.sqrt_sq hqpos.le).symm
      _ ≤ Real.sqrt (2 * m * r) := Real.sqrt_le_sqrt hq2x
  have hsqrt : Real.sqrt (r : ℝ) / r = (r : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub_one hx0.ne']
    norm_num
  have hb2 : 1 / (u - 1) ≤ s * (r : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc 1 / (u - 1) ≤ q / r := hb1
      _ ≤ s * Real.sqrt r / r := by gcongr
      _ = s * (r : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [mul_div_assoc, hsqrt]
  have P3 : (1 / (u - 1)) ^ (m * r) ≤ (s ^ m) ^ r * (r : ℝ) ^ (-((m : ℝ) * r) / 2) := by
    calc (1 / (u - 1)) ^ (m * r)
        ≤ (s * (r : ℝ) ^ (-(1 / 2 : ℝ))) ^ (m * r) := pow_le_pow_left₀ hbase0 hb2 _
      _ = (s ^ m) ^ r * (r : ℝ) ^ (-((m : ℝ) * r) / 2) := by
          rw [mul_pow, ← Real.rpow_mul_natCast hx0.le, pow_mul]
          congr 2
          push_cast; ring
  -- P5 : C₀^n ≤ C₀^r
  have P5 : C₀ ^ n ≤ C₀ ^ r := pow_le_pow_right₀ hC₀ hnr
  -- P6 : n^((n+1)/2) ≤ r^((r+1)/2)
  have P6 : (n : ℝ) ^ (((n : ℝ) + 1) / 2) ≤ (r : ℝ) ^ (((r : ℝ) + 1) / 2) := by
    calc (n : ℝ) ^ (((n : ℝ) + 1) / 2) ≤ (r : ℝ) ^ (((n : ℝ) + 1) / 2) :=
          Real.rpow_le_rpow (by positivity) hnx (by positivity)
      _ ≤ (r : ℝ) ^ (((r : ℝ) + 1) / 2) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  -- P7 : e^{Kq} e^{K q (m+1)(u+1)} ≤ E₁^r
  have P7 : Real.exp (K * q) * Real.exp (K * q * ((m + 1) * (u + 1))) ≤ E₁ ^ r := by
    rw [← Real.exp_add, hE₁, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hqu : (q : ℝ) * (u + 1) = 3 * q + r := by rw [hu]; field_simp; ring
    have h3 : (q : ℝ) + (m + 1) * (3 * q + r) ≤ ((m + 1) * (6 * m + 1) + 2 * m) * r := by
      nlinarith
    calc K * q + K * q * ((m + 1) * (u + 1)) = K * (q + (m + 1) * (q * (u + 1))) := by ring
      _ ≤ K * (((m + 1) * (6 * m + 1) + 2 * m) * r) := by rw [hqu]; gcongr
      _ = r * (K * ((m + 1) * (6 * m + 1) + 2 * m)) := by ring
  -- combine
  have hT : (r : ℝ) ^ (r : ℝ) * (r : ℝ) ^ (-((m : ℝ) * r) / 2) * (r : ℝ) ^ (1 : ℝ) *
      (r : ℝ) ^ (((r : ℝ) + 1) / 2) = (r : ℝ) ^ ((r : ℝ) * (3 - m) / 2 + 3 / 2) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1; ring
  have h4m : (4 * m : ℝ) ≤ (4 * m : ℝ) ^ r := le_self_pow₀ (by linarith) (by omega)
  have hA : (r.factorial : ℝ) * 2 * (1 / (u - 1)) ^ (m * r) ≤
      (r : ℝ) ^ (r : ℝ) * 2 * ((s ^ m) ^ r * (r : ℝ) ^ (-((m : ℝ) * r) / 2)) :=
    mul_le_mul (mul_le_mul_of_nonneg_right P1 (by norm_num)) P3 (pow_nonneg hbase0 _)
      (by positivity)
  have hB : (q : ℝ) ^ 2 * (C₀ ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2) * Real.exp (K * q)) *
        Real.exp (K * q * ((m + 1) * (u + 1)))
      ≤ (2 * m * r) * (C₀ ^ r * (r : ℝ) ^ (((r : ℝ) + 1) / 2)) * E₁ ^ r := by
    calc _ = (q : ℝ) ^ 2 * (C₀ ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) *
          (Real.exp (K * q) * Real.exp (K * q * ((m + 1) * (u + 1)))) := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul hq2x (mul_le_mul P5 P6 (by positivity) (by positivity))
          (by positivity) (by positivity)) P7 (by positivity) (by positivity)
  calc _ ≤ (r : ℝ) ^ (r : ℝ) * 2 * ((s ^ m) ^ r * (r : ℝ) ^ (-((m : ℝ) * r) / 2)) *
        ((2 * m * r) * (C₀ ^ r * (r : ℝ) ^ (((r : ℝ) + 1) / 2)) * E₁ ^ r) :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = (4 * m) * (s ^ m * C₀ * E₁) ^ r * ((r : ℝ) ^ (r : ℝ) * (r : ℝ) ^ (-((m : ℝ) * r) / 2) *
        (r : ℝ) ^ (1 : ℝ) * (r : ℝ) ^ (((r : ℝ) + 1) / 2)) := by
        rw [Real.rpow_one, mul_pow, mul_pow]; ring
    _ = (4 * m) * (s ^ m * C₀ * E₁) ^ r * (r : ℝ) ^ ((r : ℝ) * (3 - m) / 2 + 3 / 2) := by
        rw [hT]
    _ ≤ (4 * m) ^ r * (s ^ m * C₀ * E₁) ^ r * (r : ℝ) ^ ((r : ℝ) * (3 - m) / 2 + 3 / 2) := by
        gcongr
    _ = (4 * m * s ^ m * C₀ * E₁) ^ r * (r : ℝ) ^ ((r : ℝ) * (3 - m) / 2 + 3 / 2) := by
        rw [mul_pow, mul_pow, mul_pow, mul_pow]; ring

end W5_derivUpper

open W5_derivUpper in
theorem solution (l β : ℂ) (m : ℕ) (hm : 0 < m) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n q r l₀ : ℕ) (c : Fin q → Fin q → ℂ),
      0 < n → q ^ 2 = 2 * m * n → n ≤ r → 1 ≤ l₀ → l₀ ≤ m →
      (∀ a b, ‖c a b‖ ≤ C₀ ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) →
      (∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ k < r, iteratedDeriv k (fun z : ℂ => ∑ a : Fin q, ∑ b : Fin q,
          c a b * Complex.exp ((((a : ℕ) + 1 : ℂ) + ((b : ℕ) + 1 : ℂ) * β) * l * z)) (j : ℂ) = 0) →
      ‖iteratedDeriv r (fun z : ℂ => ∑ a : Fin q, ∑ b : Fin q,
          c a b * Complex.exp ((((a : ℕ) + 1 : ℂ) + ((b : ℕ) + 1 : ℂ) * β) * l * z)) (l₀ : ℂ)‖ ≤
        C ^ r * (r : ℝ) ^ ((r : ℝ) * (3 - m) / 2 + 3 / 2) := by
  set K : ℝ := (1 + ‖β‖) * ‖l‖ with hKdef
  obtain ⟨C, hC1, hC⟩ := arith_combine m hm K (by positivity) C₀ hC₀
  refine ⟨C, hC1, fun n q r l₀ c hn hq hnr hl₀1 hl₀m hc hvan => ?_⟩
  set E : ℂ → ℂ := fun z : ℂ => ∑ a : Fin q, ∑ b : Fin q,
    c a b * Complex.exp ((((a : ℕ) + 1 : ℂ) + ((b : ℕ) + 1 : ℂ) * β) * l * z) with hEdef
  set ω : Fin q × Fin q → ℂ := fun k => (((k.1 : ℕ) + 1 : ℂ) + ((k.2 : ℕ) + 1 : ℂ) * β) * l
    with hωdef
  set B : ℝ := C₀ ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2) with hBdef
  set u : ℝ := 2 + (r : ℝ) / q with hu
  have hu2 : 2 ≤ u := by rw [hu]; exact le_add_of_nonneg_right (by positivity)
  -- (1) the frequencies `ω_{ab}` have norm at most `K q`
  have hω : ∀ k ∈ (Finset.univ : Finset (Fin q × Fin q)), ‖ω k‖ ≤ K * q := fun k _ => by
    have ha : ((k.1 : ℕ) : ℝ) + 1 ≤ q := by exact_mod_cast k.1.isLt
    have hb : ((k.2 : ℕ) : ℝ) + 1 ≤ q := by exact_mod_cast k.2.isLt
    have h1 : ‖((k.1 : ℕ) + 1 : ℂ)‖ ≤ (k.1 : ℕ) + 1 := (norm_add_le _ _).trans (by simp)
    have h2 : ‖((k.2 : ℕ) + 1 : ℂ)‖ ≤ (k.2 : ℕ) + 1 := (norm_add_le _ _).trans (by simp)
    show ‖(((k.1 : ℕ) + 1 : ℂ) + ((k.2 : ℕ) + 1 : ℂ) * β) * l‖ ≤ (1 + ‖β‖) * ‖l‖ * q
    calc _ ≤ (q + q * ‖β‖) * ‖l‖ := by
          rw [norm_mul]; gcongr
          refine (norm_add_le _ _).trans (add_le_add (h1.trans ha) ?_)
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (h2.trans hb) (norm_nonneg _)
      _ = _ := by ring
  -- (2) after the shift `z ↦ z + 1` the coefficients are `c_{ab} e^{ω_{ab}}`
  have hF : ∀ z, E (z + 1) = ∑ k ∈ Finset.univ, c k.1 k.2 * Complex.exp (ω k) * z ^ 0 *
      Complex.exp (ω k * z) := fun z => by
    simp only [hEdef, hωdef, Fintype.sum_prod_type, pow_zero, mul_one]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_add, mul_one, Complex.exp_add]; ring
  have hcs : ∑ k ∈ Finset.univ, ‖c k.1 k.2 * Complex.exp (ω k)‖ ≤ q ^ 2 * (B * Real.exp (K * q)) := by
    refine (Finset.sum_le_card_nsmul _ _ (B * Real.exp (K * q)) fun k hk => ?_).trans_eq
      (by simp [sq])
    rw [norm_mul]
    exact mul_le_mul (hc _ _) ((Complex.norm_exp_le_exp_norm _).trans
      (Real.exp_le_exp.mpr (hω k hk))) (norm_nonneg _) (by positivity)
  -- (3) the grid estimate on `{0, …, m - 1}`, target `l₀ - 1`
  have key := Transcendence.expPoly_grid_estimate (fun _ : Unit => (1 : ℂ))
    (linearIndependent_unique_iff.mpr one_ne_zero) Finset.univ
    (fun k => c k.1 k.2 * Complex.exp (ω k)) ω (fun _ => 0) (fun z => E (z + 1)) hF (K * q) 0 hω
    (fun _ _ => le_rfl) (fun _ => m) (fun _ => m) (fun _ => le_rfl) r (fun j hj i hi => ?_) u
    ((m + 1) * (u + 1)) hu2 (by simp) (fun _ => l₀ - 1) (fun _ => by omega) r
  · rw [iteratedDeriv_comp_add_const] at key
    simp only [Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton, mul_one,
      pow_zero, Nat.cast_sub hl₀1, Nat.cast_one, sub_add_cancel] at key
    have hu0 : 0 ≤ 1 / (u - 1) := div_nonneg zero_le_one (by linarith)
    refine key.trans (le_trans ?_ (hC n q r hn hq hnr u hu))
    gcongr
  · rw [iteratedDeriv_comp_add_const]
    simpa using hvan (j () + 1) (by omega) (by have := hj (); omega) i hi
