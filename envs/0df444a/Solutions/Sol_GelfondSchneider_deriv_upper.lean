-- Prove2me | solution 1 for GelfondSchneider.deriv_upper
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:06:31.388874+00:00
-- url     : https://prove2.me/submissions/6ee7ad66-1914-4675-ab7b-ef6002a68176

import Mathlib
import Theorems.Thm_FourExp_cauchy_estimate_with_zeros

/-!
# Outline: `GelfondSchneider.deriv_upper` from `FourExp.cauchy_estimate_with_zeros`

Route: apply the Cauchy node with
* `F := E` (the exponential sum), `c := l₀`, `s := r`;
* `S := {1, …, m}` (as complex numbers), **including** `l₀`;
* `ρ := m - 1`, `R := 2m(1 + r/q)`;
* `M := q² · C₀ⁿ n^((n+1)/2) · exp((1+‖β‖)‖l‖ · q(m + R))`.
Every point of `S` has analytic order `≥ r` (finite unless `E ≡ 0`, a trivial case),
so `Σ orders ≥ m r` and the zero factor is `≤ (m/(R-m+1))^(m r) ≤ (q/(2r))^(m r)`.

Exponent accounting (`q² = 2mn ≤ 2mr`, `r! ≤ r^r`, `R/(R-1) ≤ 2`, `q R = 2mq + 2mr`):
`r^r · r^(-m r/2) · r^1 (from q²) · r^((r+1)/2) (from n^((n+1)/2)) = r^(r(3-m)/2 + 3/2)`,
with `C = 4m · √(2m)^m · C₀ · exp((1+‖β‖)‖l‖(6m² + 2m))`, independent of `n, q, r`.
Excluding `l₀` from `S` would only give `Σ orders ≥ (m-1) r`, i.e. exponent
`r(4-m)/2 + 3/2`: too weak by `r^(r/2)`.
The `+ 3/2` is slack: `r^(3/2) ≤ 4^r`, so `C^r · r^(r(3-m)/2)` is provable as well.

Every step in this file is proved, arithmetic lemmas included. The extra axiom reported by
`#print axioms solution` comes only from the imported stub `FourExp.cauchy_estimate_with_zeros`.
-/

namespace GS_upper

section Arith

/-- Arithmetic (reals only): the final combination of the Cauchy bound. -/
lemma arith_combine (m : ℕ) (hm : 0 < m) (K : ℝ) (hK : 0 ≤ K) (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n q r : ℕ, 0 < n → q ^ 2 = 2 * m * n → n ≤ r →
      ∀ R : ℝ, R = 2 * m * (1 + (r : ℝ) / q) →
      (r.factorial : ℝ) * (R / (R - 1)) * ((m : ℝ) / (R - ((m : ℝ) - 1))) ^ (m * r) *
        ((q : ℝ) ^ 2 * (C₀ ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) * Real.exp (K * (q * (m + R))))
      ≤ C ^ r * (r : ℝ) ^ ((r : ℝ) * (3 - m) / 2 + 3 / 2) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set s : ℝ := Real.sqrt (2 * m) with hs
  have hs1 : 1 ≤ s := by rw [hs, Real.one_le_sqrt]; linarith
  set E₁ : ℝ := Real.exp (K * (6 * m ^ 2 + 2 * m)) with hE₁
  have hE₁1 : 1 ≤ E₁ := Real.one_le_exp (by positivity)
  refine ⟨4 * m * s ^ m * C₀ * E₁, ?_, ?_⟩
  · have h4 : (1 : ℝ) ≤ 4 * m := by linarith
    have h2 : (1 : ℝ) ≤ s ^ m := one_le_pow₀ hs1
    calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
      _ ≤ 4 * m * s ^ m * C₀ * E₁ := by gcongr
  intro n q r hn hq hnr R hR
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
  have hqne : (q : ℝ) ≠ 0 := hqpos.ne'
  have hq2 : (q : ℝ) ^ 2 = 2 * m * n := by exact_mod_cast hq
  have hnx : (n : ℝ) ≤ r := by exact_mod_cast hnr
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq2x : (q : ℝ) ^ 2 ≤ 2 * m * r := by rw [hq2]; gcongr
  have hqx : (q : ℝ) ≤ 2 * m * r := by nlinarith
  have hrq : 0 ≤ (r : ℝ) / q := by positivity
  have hR2m : 2 * (m : ℝ) ≤ R := by rw [hR]; nlinarith
  have hqR : (q : ℝ) * R = 2 * m * q + 2 * m * r := by
    rw [hR]; field_simp
  -- P1 : r! ≤ r^r
  have P1 : (r.factorial : ℝ) ≤ (r : ℝ) ^ (r : ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast Nat.factorial_le_pow r
  -- P2 : R/(R-1) ≤ 2
  have P2 : R / (R - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have P2' : 0 ≤ R / (R - 1) := div_nonneg (by linarith) (by linarith)
  -- P3 : the zero factor, `(m/(R-ρ))^(m r) ≤ (√(2m))^(m r) · r^(-m r/2)`
  have hden : 0 < R - ((m : ℝ) - 1) := by linarith
  have hbase0 : 0 ≤ (m : ℝ) / (R - ((m : ℝ) - 1)) := by positivity
  have hb1 : (m : ℝ) / (R - ((m : ℝ) - 1)) ≤ q / (2 * r) := by
    rw [div_le_div_iff₀ hden (by positivity)]
    have h1 : (q : ℝ) * (R - ((m : ℝ) - 1)) = m * q + q + 2 * m * r := by
      linear_combination hqR
    have h2 : 0 ≤ (m : ℝ) * q + q := by positivity
    rw [h1]; linarith
  have hqs : (q : ℝ) ≤ s * Real.sqrt r := by
    rw [hs, ← Real.sqrt_mul (show (0 : ℝ) ≤ 2 * m by positivity)]
    calc (q : ℝ) = Real.sqrt ((q : ℝ) ^ 2) := (Real.sqrt_sq hqpos.le).symm
      _ ≤ Real.sqrt (2 * m * r) := Real.sqrt_le_sqrt hq2x
  have hsqrt : Real.sqrt (r : ℝ) / r = (r : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub_one hx0.ne']
    norm_num
  have hb2 : (m : ℝ) / (R - ((m : ℝ) - 1)) ≤ s * (r : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc (m : ℝ) / (R - ((m : ℝ) - 1)) ≤ q / (2 * r) := hb1
      _ ≤ q / r := by gcongr; linarith
      _ ≤ s * Real.sqrt r / r := by gcongr
      _ = s * (r : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [mul_div_assoc, hsqrt]
  have P3 : ((m : ℝ) / (R - ((m : ℝ) - 1))) ^ (m * r) ≤
      (s ^ m) ^ r * (r : ℝ) ^ (-((m : ℝ) * r) / 2) := by
    calc ((m : ℝ) / (R - ((m : ℝ) - 1))) ^ (m * r)
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
  -- P7 : exp(K q (m + R)) ≤ E₁^r
  have P7 : Real.exp (K * (q * (m + R))) ≤ E₁ ^ r := by
    rw [hE₁, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h3 : (q : ℝ) * (m + R) ≤ (6 * m ^ 2 + 2 * m) * r := by
      have h4 := mul_le_mul_of_nonneg_left hqx (show (0 : ℝ) ≤ 3 * m by positivity)
      nlinarith
    calc K * (q * (m + R)) ≤ K * ((6 * m ^ 2 + 2 * m) * r) := by gcongr
      _ = r * (K * (6 * m ^ 2 + 2 * m)) := by ring
  -- combine
  have hT : (r : ℝ) ^ (r : ℝ) * (r : ℝ) ^ (-((m : ℝ) * r) / 2) * (r : ℝ) ^ (1 : ℝ) *
      (r : ℝ) ^ (((r : ℝ) + 1) / 2) = (r : ℝ) ^ ((r : ℝ) * (3 - m) / 2 + 3 / 2) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1; ring
  have h4m : (4 * m : ℝ) ≤ (4 * m : ℝ) ^ r := le_self_pow₀ (by linarith) (by omega)
  have hA : (r.factorial : ℝ) * (R / (R - 1)) * ((m : ℝ) / (R - ((m : ℝ) - 1))) ^ (m * r) ≤
      (r : ℝ) ^ (r : ℝ) * 2 * ((s ^ m) ^ r * (r : ℝ) ^ (-((m : ℝ) * r) / 2)) :=
    mul_le_mul (mul_le_mul P1 P2 P2' (by positivity)) P3 (pow_nonneg hbase0 _) (by positivity)
  have hB : (q : ℝ) ^ 2 * (C₀ ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) * Real.exp (K * (q * (m + R)))
      ≤ (2 * m * r) * (C₀ ^ r * (r : ℝ) ^ (((r : ℝ) + 1) / 2)) * E₁ ^ r :=
    mul_le_mul (mul_le_mul hq2x (mul_le_mul P5 P6 (by positivity) (by positivity))
      (by positivity) (by positivity)) P7 (by positivity) (by positivity)
  calc (r.factorial : ℝ) * (R / (R - 1)) * ((m : ℝ) / (R - ((m : ℝ) - 1))) ^ (m * r) *
        ((q : ℝ) ^ 2 * (C₀ ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) * Real.exp (K * (q * (m + R))))
      ≤ (r : ℝ) ^ (r : ℝ) * 2 * ((s ^ m) ^ r * (r : ℝ) ^ (-((m : ℝ) * r) / 2)) *
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

/-- Arithmetic (reals only): side conditions on the radius. -/
lemma radius_facts (m q r : ℕ) (hm : 0 < m) (hq : 0 < q) (R : ℝ)
    (hR : R = 2 * m * (1 + (r : ℝ) / q)) :
    ((m : ℝ) - 1) + 1 < R ∧ 1 < R ∧
      0 ≤ (m : ℝ) / (R - ((m : ℝ) - 1)) ∧ (m : ℝ) / (R - ((m : ℝ) - 1)) ≤ 1 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hrq : 0 ≤ (r : ℝ) / q := by positivity
  have hR2m : 2 * (m : ℝ) ≤ R := by rw [hR]; nlinarith
  have hpos : 0 < R - ((m : ℝ) - 1) := by linarith
  refine ⟨by linarith, by linarith, by positivity, ?_⟩
  rw [div_le_one hpos]
  linarith

end Arith

end GS_upper

open GS_upper in
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
  have hK : 0 ≤ K := by positivity
  obtain ⟨C, hC1, hC⟩ := arith_combine m hm K hK C₀ hC₀
  refine ⟨C, hC1, ?_⟩
  intro n q r l₀ c hn hq hnr hl₀1 hl₀m hc hvan
  set E : ℂ → ℂ := fun z : ℂ => ∑ a : Fin q, ∑ b : Fin q,
    c a b * Complex.exp ((((a : ℕ) + 1 : ℂ) + ((b : ℕ) + 1 : ℂ) * β) * l * z) with hEdef
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · exfalso
      subst h
      have h2 : 0 < 2 * m * n := by positivity
      simp at hq
      omega
    · exact h
  have hr0 : 0 < r := lt_of_lt_of_le hn hnr
  -- (1) differentiability of `E`
  have hEd : Differentiable ℂ E := by
    rw [hEdef]
    fun_prop
  have hAn : ∀ z, AnalyticAt ℂ E z := fun z => hEd.analyticAt z
  -- the trivial case `E = 0`
  by_cases hE0 : E = 0
  · have h0 : iteratedDeriv r E (l₀ : ℂ) = 0 := by
      rw [hE0]
      have : (0 : ℂ → ℂ) = fun _ => (0 : ℂ) := rfl
      rw [this, iteratedDeriv_const]
      simp
    rw [h0, norm_zero]
    positivity
  -- (2) orders at the points of `S`: each is finite and `≥ r`
  have hfin : ∀ z, analyticOrderAt E z ≠ ⊤ := fun z h =>
    hE0 ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z hAn).mp h)
  have hordN : ∀ j : ℕ, 1 ≤ j → j ≤ m → r ≤ analyticOrderNatAt E (j : ℂ) := by
    intro j hj1 hjm
    have h1 : (r : ℕ∞) ≤ analyticOrderAt E (j : ℂ) :=
      (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hAn j)).mpr (hvan j hj1 hjm)
    rw [← Nat.cast_analyticOrderNatAt (hfin _)] at h1
    exact_mod_cast h1
  set S : Finset ℂ := (Finset.Icc 1 m).image (fun j : ℕ => (j : ℂ)) with hSdef
  have hScard : S.card = m := by
    rw [hSdef, Finset.card_image_of_injective _ Nat.cast_injective]
    simp
  have hsum : m * r ≤ ∑ z ∈ S, analyticOrderNatAt E z := by
    have h := Finset.card_nsmul_le_sum S (fun z => analyticOrderNatAt E z) r (by
      intro z hz
      rw [hSdef, Finset.mem_image] at hz
      obtain ⟨j, hj, rfl⟩ := hz
      rw [Finset.mem_Icc] at hj
      exact hordN j hj.1 hj.2)
    simpa [hScard] using h
  -- the points of `S` lie within `ρ = m - 1` of `l₀`
  have hS : ∀ z ∈ S, ‖z - (l₀ : ℂ)‖ ≤ (m : ℝ) - 1 := by
    intro z hz
    rw [hSdef, Finset.mem_image] at hz
    obtain ⟨j, hj, rfl⟩ := hz
    rw [Finset.mem_Icc] at hj
    have h1 : ((j : ℂ) - (l₀ : ℂ)) = (((j : ℝ) - (l₀ : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
    have hjm : (j : ℝ) ≤ m := by exact_mod_cast hj.2
    have hl1 : (1 : ℝ) ≤ l₀ := by exact_mod_cast hl₀1
    have hlm : (l₀ : ℝ) ≤ m := by exact_mod_cast hl₀m
    constructor <;> linarith
  -- the radius
  set R : ℝ := 2 * m * (1 + (r : ℝ) / q) with hRdef
  obtain ⟨hRρ, hR1, hb0, hb1⟩ := radius_facts m q r hm hq0 R hRdef
  -- (3) growth bound on the circle `‖z - l₀‖ = R`
  set B : ℝ := C₀ ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2) with hBdef
  have hB0 : 0 ≤ B := by positivity
  set M : ℝ := (q : ℝ) ^ 2 * B * Real.exp (K * (q * (m + R))) with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hM : ∀ z : ℂ, ‖z - (l₀ : ℂ)‖ = R → ‖E z‖ ≤ M := by
    intro z hz
    have hzn : ‖z‖ ≤ m + R := by
      have hlm : (l₀ : ℝ) ≤ m := by exact_mod_cast hl₀m
      calc ‖z‖ = ‖(z - l₀) + l₀‖ := by ring_nf
        _ ≤ ‖z - l₀‖ + ‖(l₀ : ℂ)‖ := norm_add_le _ _
        _ = R + l₀ := by rw [hz, Complex.norm_natCast]
        _ ≤ m + R := by linarith
    have hterm : ∀ a b : Fin q, ‖c a b * Complex.exp
        ((((a : ℕ) + 1 : ℂ) + ((b : ℕ) + 1 : ℂ) * β) * l * z)‖ ≤
        B * Real.exp (K * (q * (m + R))) := by
      intro a b
      rw [norm_mul]
      refine mul_le_mul (hc a b) ?_ (norm_nonneg _) hB0
      refine le_trans (Complex.norm_exp_le_exp_norm _) (Real.exp_le_exp.mpr ?_)
      have hlam : ‖(((a : ℕ) + 1 : ℂ) + ((b : ℕ) + 1 : ℂ) * β)‖ ≤ q * (1 + ‖β‖) := by
        have ha : (((a : ℕ) : ℂ) + 1) = (((a : ℕ) + 1 : ℕ) : ℂ) := by push_cast; ring
        have hb : (((b : ℕ) : ℂ) + 1) = (((b : ℕ) + 1 : ℕ) : ℂ) := by push_cast; ring
        have haq : (((a : ℕ) + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast a.isLt
        have hbq : (((b : ℕ) + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast b.isLt
        calc ‖(((a : ℕ) + 1 : ℂ) + ((b : ℕ) + 1 : ℂ) * β)‖
            ≤ ‖(((a : ℕ) + 1 : ℂ))‖ + ‖((b : ℕ) + 1 : ℂ) * β‖ := norm_add_le _ _
          _ = (((a : ℕ) + 1 : ℕ) : ℝ) + (((b : ℕ) + 1 : ℕ) : ℝ) * ‖β‖ := by
            rw [norm_mul, ha, hb, Complex.norm_natCast, Complex.norm_natCast]
          _ ≤ q + q * ‖β‖ := by gcongr
          _ = q * (1 + ‖β‖) := by ring
      rw [norm_mul, norm_mul]
      calc ‖(((a : ℕ) + 1 : ℂ) + ((b : ℕ) + 1 : ℂ) * β)‖ * ‖l‖ * ‖z‖
          ≤ (q * (1 + ‖β‖)) * ‖l‖ * (m + R) := by gcongr
        _ = K * (q * (m + R)) := by rw [hKdef]; ring
    calc ‖E z‖ ≤ ∑ a : Fin q, ∑ b : Fin q, ‖c a b * Complex.exp
          ((((a : ℕ) + 1 : ℂ) + ((b : ℕ) + 1 : ℂ) * β) * l * z)‖ := by
          refine le_trans (norm_sum_le _ _) ?_
          gcongr with a _
          exact norm_sum_le _ _
      _ ≤ ∑ a : Fin q, ∑ b : Fin q, B * Real.exp (K * (q * (m + R))) := by
          gcongr with a _ b _
          exact hterm a b
      _ = M := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hMdef]
          ring
  -- (4) apply the Cauchy node
  have hρ : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hnode := FourExp.cauchy_estimate_with_zeros E hEd (l₀ : ℂ) ((m : ℝ) - 1) R M hρ hRρ S hS
    hM r
  have hbase : ((m : ℝ) - 1 + 1) = m := by ring
  rw [hbase] at hnode
  have hpow : ((m : ℝ) / (R - ((m : ℝ) - 1))) ^ (∑ z ∈ S, analyticOrderNatAt E z) ≤
      ((m : ℝ) / (R - ((m : ℝ) - 1))) ^ (m * r) :=
    pow_le_pow_of_le_one hb0 hb1 hsum
  have hpre : 0 ≤ (r.factorial : ℝ) * (R / (R - 1)) := by
    have : 0 < R - 1 := by linarith
    positivity
  calc ‖iteratedDeriv r E (l₀ : ℂ)‖
      ≤ (r.factorial : ℝ) * (R / (R - 1)) *
          ((m : ℝ) / (R - ((m : ℝ) - 1))) ^ (∑ z ∈ S, analyticOrderNatAt E z) * M := hnode
    _ ≤ (r.factorial : ℝ) * (R / (R - 1)) * ((m : ℝ) / (R - ((m : ℝ) - 1))) ^ (m * r) * M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hpre) hM0
    _ ≤ C ^ r * (r : ℝ) ^ ((r : ℝ) * (3 - m) / 2 + 3 / 2) := hC n q r hn hq hnr R hRdef

#print axioms solution
#print axioms GS_upper.arith_combine
#print axioms GS_upper.radius_facts
#print axioms FourExp.cauchy_estimate_with_zeros
