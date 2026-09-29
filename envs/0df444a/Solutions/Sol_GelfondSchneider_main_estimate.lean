-- Prove2me | solution 1 for GelfondSchneider.main_estimate
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:11:30.713811+00:00
-- url     : https://prove2.me/submissions/44a1b4ed-2ab7-4e0d-bee6-62ca88cd3830

import Mathlib
import Theorems.Thm_GelfondSchneider_aux_coeffs
import Theorems.Thm_GelfondSchneider_deriv_identity
import Theorems.Thm_Transcendence_expSum_first_nonvanishing
import Theorems.Thm_GelfondSchneider_rho_denominator
import Theorems.Thm_GelfondSchneider_rho_house_le
import Theorems.Thm_GelfondSchneider_deriv_upper
import Theorems.Thm_Transcendence_liouville_house

/-!
# Outline: the main estimate of Gelfond–Schneider from the tree's stubs

Glue proof of `GelfondSchneider.main_estimate` against the stubs
`aux_coeffs`, `deriv_identity`, `expSum_first_nonvanishing`, `rho_denominator`,
`rho_house_le`, `deriv_upper`, `liouville_house`.

Parameters: `h := finrank ℚ K`, `m := 2h + 2`, `q := 2mk`, `n := 2mk²` (so `q² = 2mn`).
-/

open NumberField

namespace GS_main

/-- Choice of parameters (pure ℕ arithmetic): for `m > 0` and any `N`, there are `n ≥ N`,
`n > 0` and `q` with `q ^ 2 = 2 * m * n`; take `k = N + 1`, `q = 2mk`, `n = 2mk²`. -/
lemma exists_params (m N : ℕ) (hm : 0 < m) :
    ∃ n q : ℕ, N ≤ n ∧ 0 < n ∧ q ^ 2 = 2 * m * n := by
  refine ⟨2 * m * (N + 1) ^ 2, 2 * m * (N + 1), ?_, by positivity, by ring⟩
  nlinarith

/-- Final exponent combination (pure real arithmetic). With `d = |D|`, `L = ‖l‖`,
`s = ‖σ x‖`, `t = house x`: Liouville's inequality `1 ≤ (d^r)^h s t^(h-1)`, the upper bound
`L^r s ≤ C₂^r r^(r(3-m)/2+3/2)` (from `deriv_upper`) and `t ≤ C₁^r r^(r+3/2)`
(from `rho_house_le`), with `m = 2h+2`, give `r^((r-3h)/2) ≤ C^r`. -/
lemma final_combination (r h : ℕ) (hr : 0 < r) (hh : 0 < h) (d L C₁ C₂ s t : ℝ)
    (hd : 0 ≤ d) (hL : 0 < L) (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (ht : 0 ≤ t)
    (hliou : 1 ≤ (d ^ r) ^ h * s * t ^ (h - 1))
    (hsb : L ^ r * s ≤
      C₂ ^ r * (r : ℝ) ^ ((r : ℝ) * (3 - ((2 * h + 2 : ℕ) : ℝ)) / 2 + 3 / 2))
    (htb : t ≤ C₁ ^ r * (r : ℝ) ^ ((r : ℝ) + 3 / 2)) :
    (r : ℝ) ^ (((r : ℝ) - 3 * h) / 2) ≤ (max 1 (d ^ h * C₂ * C₁ ^ (h - 1) / L)) ^ r := by
  have hR : (0 : ℝ) < r := by exact_mod_cast hr
  -- the exponent identity, using `m = 2h + 2`
  have hexp : (r : ℝ) * (3 - ((2 * h + 2 : ℕ) : ℝ)) / 2 + 3 / 2 +
      ((r : ℝ) + 3 / 2) * ((h - 1 : ℕ) : ℝ) = -(((r : ℝ) - 3 * h) / 2) := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hh.ne')]
    push_cast
    ring
  have hpow : (r : ℝ) ^ (-(((r : ℝ) - 3 * h) / 2)) =
      (r : ℝ) ^ ((r : ℝ) * (3 - ((2 * h + 2 : ℕ) : ℝ)) / 2 + 3 / 2) *
        ((r : ℝ) ^ ((r : ℝ) + 3 / 2)) ^ (h - 1) := by
    rw [← hexp, Real.rpow_add hR ((r : ℝ) * (3 - ((2 * h + 2 : ℕ) : ℝ)) / 2 + 3 / 2)
      (((r : ℝ) + 3 / 2) * ((h - 1 : ℕ) : ℝ)),
      Real.rpow_mul hR.le ((r : ℝ) + 3 / 2) ((h - 1 : ℕ) : ℝ), Real.rpow_natCast]
  have hA : 0 ≤ d ^ h * C₂ * C₁ ^ (h - 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg hd _) (by linarith)) (pow_nonneg (by linarith) _)
  have hLr : 0 ≤ L ^ r := pow_nonneg hL.le r
  have h1 : L ^ r ≤ (d ^ r) ^ h *
      (C₂ ^ r * (r : ℝ) ^ ((r : ℝ) * (3 - ((2 * h + 2 : ℕ) : ℝ)) / 2 + 3 / 2)) *
      (C₁ ^ r * (r : ℝ) ^ ((r : ℝ) + 3 / 2)) ^ (h - 1) := by
    calc L ^ r = L ^ r * 1 := (mul_one _).symm
      _ ≤ L ^ r * ((d ^ r) ^ h * s * t ^ (h - 1)) := mul_le_mul_of_nonneg_left hliou hLr
      _ = (d ^ r) ^ h * (L ^ r * s) * t ^ (h - 1) := by ring
      _ ≤ _ := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hsb (pow_nonneg (pow_nonneg hd _) _))
          (pow_le_pow_left₀ ht htb _) (pow_nonneg ht _)
        exact mul_nonneg (pow_nonneg (pow_nonneg hd _) _)
          (mul_nonneg (pow_nonneg (by linarith) _) (Real.rpow_nonneg hR.le _))
  have h2 : (d ^ r) ^ h *
      (C₂ ^ r * (r : ℝ) ^ ((r : ℝ) * (3 - ((2 * h + 2 : ℕ) : ℝ)) / 2 + 3 / 2)) *
      (C₁ ^ r * (r : ℝ) ^ ((r : ℝ) + 3 / 2)) ^ (h - 1) =
      (d ^ h * C₂ * C₁ ^ (h - 1)) ^ r * (r : ℝ) ^ (-(((r : ℝ) - 3 * h) / 2)) := by
    rw [hpow]
    ring
  have h3 : (r : ℝ) ^ (((r : ℝ) - 3 * h) / 2) * L ^ r ≤ (d ^ h * C₂ * C₁ ^ (h - 1)) ^ r := by
    calc (r : ℝ) ^ (((r : ℝ) - 3 * h) / 2) * L ^ r
        ≤ (r : ℝ) ^ (((r : ℝ) - 3 * h) / 2) *
          ((d ^ h * C₂ * C₁ ^ (h - 1)) ^ r * (r : ℝ) ^ (-(((r : ℝ) - 3 * h) / 2))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2.le) (Real.rpow_nonneg hR.le _)
      _ = (d ^ h * C₂ * C₁ ^ (h - 1)) ^ r *
          ((r : ℝ) ^ (((r : ℝ) - 3 * h) / 2) * (r : ℝ) ^ (-(((r : ℝ) - 3 * h) / 2))) := by ring
      _ = (d ^ h * C₂ * C₁ ^ (h - 1)) ^ r := by
          rw [← Real.rpow_add hR, add_neg_cancel, Real.rpow_zero, mul_one]
  have h4 : (r : ℝ) ^ (((r : ℝ) - 3 * h) / 2) ≤ (d ^ h * C₂ * C₁ ^ (h - 1) / L) ^ r := by
    rw [div_pow, le_div_iff₀ (pow_pos hL r)]
    exact h3
  exact h4.trans (pow_le_pow_left₀ (div_nonneg hA hL.le) (le_max_right _ _) r)

end GS_main

open GS_main in
theorem solution (K : Type*) [Field K] [NumberField K] (σ : K →+* ℂ) (α' β' γ' : K)
    (l β : ℂ) (hl : l ≠ 0) (hβq : ∀ x : ℚ, β ≠ x)
    (hα : σ α' = Complex.exp l) (hβ : σ β' = β) (hγ : σ γ' = Complex.exp (β * l)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧ 0 < r ∧
      (r : ℝ) ^ (((r : ℝ) - 3 * Module.finrank ℚ K) / 2) ≤ C ^ r := by
  set h := Module.finrank ℚ K with hh_def
  have hh : 0 < h := Module.finrank_pos
  set m := 2 * h + 2 with hm_def
  have hm : 0 < m := by omega
  have hα0 : α' ≠ 0 := by
    intro h0; rw [h0, map_zero] at hα; exact Complex.exp_ne_zero l hα.symm
  have hγ0 : γ' ≠ 0 := by
    intro h0; rw [h0, map_zero] at hγ; exact Complex.exp_ne_zero _ hγ.symm
  -- constants of the stubs, all fixed before `N`
  obtain ⟨C₀, hC₀, haux⟩ := GelfondSchneider.aux_coeffs K α' β' γ' hα0 hγ0 m hm
  obtain ⟨D, hD0, hden⟩ := GelfondSchneider.rho_denominator K α' β' γ' m
  obtain ⟨C₁, hC₁, hhouse⟩ := GelfondSchneider.rho_house_le K α' β' γ' m hm C₀ hC₀
  obtain ⟨C₂, hC₂, hupper⟩ := GelfondSchneider.deriv_upper l β m hm C₀ hC₀
  refine ⟨max 1 (|(D : ℝ)| ^ h * C₂ * C₁ ^ (h - 1) / ‖l‖), le_max_left _ _, ?_⟩
  intro N
  obtain ⟨n, q, hNn, hn, hq⟩ := exists_params m N hm
  -- Step 1: Siegel
  obtain ⟨η, hη0, hηhouse, hηvan⟩ := haux n q hn hq
  -- the auxiliary function
  set E : ℂ → ℂ := fun z => ∑ a : Fin q, ∑ b : Fin q,
      σ (η a b : K) * Complex.exp ((((a : ℕ) + 1 : ℂ) + ((b : ℕ) + 1 : ℂ) * β) * l * z)
    with hE_def
  -- Step 2: derivatives of `E` at integers are `l ^ k * σ (sum)`
  have hid : ∀ k j : ℕ, iteratedDeriv k E (j : ℂ) =
      l ^ k * σ (∑ a : Fin q, ∑ b : Fin q, (η a b : K) *
        (((a : ℕ) + 1 : K) + ((b : ℕ) + 1 : K) * β') ^ k *
        α' ^ (((a : ℕ) + 1) * j) * γ' ^ (((b : ℕ) + 1) * j)) := fun k j =>
    GelfondSchneider.deriv_identity K σ α' β' γ' l β hβ hα hγ q (fun a b => (η a b : K)) k j
  have hvanE : ∀ j : ℕ, 1 ≤ j → j ≤ m → ∀ k < n, iteratedDeriv k E (j : ℂ) = 0 := by
    intro j hj1 hjm k hk
    rw [hid k j, hηvan j hj1 hjm k hk, map_zero, mul_zero]
  -- Step 3: first non-vanishing derivative, after reindexing by `Fin q × Fin q`
  set c : Fin q × Fin q → ℂ := fun i => σ (η i.1 i.2 : K) with hc_def
  set ρ : Fin q × Fin q → ℂ := fun i =>
      (((i.1 : ℕ) + 1 : ℂ) + ((i.2 : ℕ) + 1 : ℂ) * β) * l with hρ_def
  have hFE : (fun z : ℂ => ∑ i, c i * Complex.exp (ρ i * z)) = E := by
    funext z
    rw [Fintype.sum_prod_type]
  have hρinj : Function.Injective ρ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have h1 : ((a : ℕ) + 1 : ℂ) + ((b : ℕ) + 1 : ℂ) * β =
        ((a' : ℕ) + 1 : ℂ) + ((b' : ℕ) + 1 : ℂ) * β := mul_right_cancel₀ hl hab
    by_cases hb : (b : ℕ) = (b' : ℕ)
    · have hbb : b = b' := Fin.ext hb
      subst hbb
      have h2 : ((a : ℕ) : ℂ) = ((a' : ℕ) : ℂ) := by linear_combination h1
      have h3 : (a : ℕ) = (a' : ℕ) := by exact_mod_cast h2
      rw [Fin.ext h3]
    · exfalso
      have hne : ((b' : ℕ) : ℂ) - ((b : ℕ) : ℂ) ≠ 0 := by
        rw [sub_ne_zero]; exact_mod_cast (Ne.symm hb)
      apply hβq ((((a : ℕ) : ℚ) - ((a' : ℕ) : ℚ)) / (((b' : ℕ) : ℚ) - ((b : ℕ) : ℚ)))
      push_cast
      rw [eq_div_iff hne]
      linear_combination -h1
  have hc : c ≠ 0 := by
    intro hc0
    apply hη0
    funext a b
    have h1 : σ (η a b : K) = 0 := congrFun hc0 (a, b)
    have h2 : (η a b : K) = 0 := (map_eq_zero σ).mp h1
    show η a b = 0
    exact RingOfIntegers.coe_eq_zero_iff.mp h2
  obtain ⟨r, l₀, hnr, hl₀1, hl₀m, hEr, hvan_r⟩ :=
    Transcendence.expSum_first_nonvanishing c ρ hρinj hc m n hm (by rw [hFE]; exact hvanE)
  rw [hFE] at hEr hvan_r
  have hr : 0 < r := lt_of_lt_of_le hn hnr
  -- Step 4: the algebraic number `x` at level `r`, point `l₀`
  set x : K := ∑ a : Fin q, ∑ b : Fin q, (η a b : K) *
        (((a : ℕ) + 1 : K) + ((b : ℕ) + 1 : K) * β') ^ r *
        α' ^ (((a : ℕ) + 1) * l₀) * γ' ^ (((b : ℕ) + 1) * l₀) with hx_def
  have hEx : iteratedDeriv r E (l₀ : ℂ) = l ^ r * σ x := hid r l₀
  have hσx : σ x ≠ 0 := by
    intro h0; apply hEr; rw [hEx, h0, mul_zero]
  have hx0 : x ≠ 0 := by
    intro h0; apply hσx; rw [h0, map_zero]
  -- Step 5: denominator, house, analytic upper bound
  have hint : IsIntegral ℤ ((D : K) ^ r * x) := hden n q r l₀ η hn hq hnr hl₀1 hl₀m
  have hxhouse : house x ≤ C₁ ^ r * (r : ℝ) ^ ((r : ℝ) + 3 / 2) :=
    hhouse n q r l₀ η hn hq hnr hl₀1 hl₀m hηhouse
  have hcb : ∀ a b, ‖(fun a b => σ (η a b : K)) a b‖ ≤
      C₀ ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2) :=
    fun a b => (norm_embedding_le_house _ σ).trans (hηhouse a b)
  have hEbound := hupper n q r l₀ (fun a b => σ (η a b : K)) hn hq hnr hl₀1 hl₀m hcb hvan_r
  have hsb : ‖l‖ ^ r * ‖σ x‖ ≤
      C₂ ^ r * (r : ℝ) ^ ((r : ℝ) * (3 - ((2 * h + 2 : ℕ) : ℝ)) / 2 + 3 / 2) := by
    rw [← norm_pow, ← norm_mul, ← hEx]
    exact hEbound
  -- Step 6: Liouville with `c := D ^ r`
  have hliou := Transcendence.liouville_house hx0 (c := D ^ r) (pow_ne_zero r hD0)
    (by rw [Int.cast_pow]; exact hint) σ
  rw [Int.cast_pow, abs_pow] at hliou
  refine ⟨r, hNn.trans hnr, hr, ?_⟩
  exact final_combination r h hr hh |(D : ℝ)| ‖l‖ C₁ C₂ ‖σ x‖ (house x) (abs_nonneg _)
    (norm_pos_iff.mpr hl) hC₁ hC₂ (house_nonneg x) hliou hsb hxhouse

#print axioms solution

#print axioms GS_main.final_combination
#print axioms GS_main.exists_params
