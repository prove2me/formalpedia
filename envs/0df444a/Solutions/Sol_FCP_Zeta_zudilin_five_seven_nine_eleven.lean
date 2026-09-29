-- Prove2me | solution 1 for FCP.Zeta.zudilin_five_seven_nine_eleven
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-25T14:52:42.677109+00:00
-- url     : https://prove2.me/submissions/989f0a71-41ac-4aba-9c83-0181eb05b301
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ZudilinZetaSetup
import Definitions.Def_ZudilinZetaArith
import Definitions.Def_ZudilinZetaAsymp
import Definitions.Def_ZudilinZetaParams13
import Theorems.Thm_ZudilinZeta_zudilin_lemma3
import Theorems.Thm_ZudilinZeta_zudilin_numeric_C0_gt_C1
import Theorems.Thm_ZudilinZeta_exists_saddle_root_params13
import Theorems.Thm_ZudilinZeta_zetaR_eq_riemannZeta

/-!
# Reduction (proof sketch) of `FCP.Zeta.zudilin_five_seven_nine_eleven`

`theorem solution : ({5, 7, 9, 11} ∩ {a : ℕ | ∃ x : ℝ, Irrational x ∧ riemannZeta a = x}).Nonempty`

The proof decomposes the mission goal into the following frontier children, all in
the `ZudilinZeta` namespace:

1. `ZudilinZeta.exists_saddle_root_params13` — for the parameter set `params13`
   (`r = 3`, `q = 13`, `η₀ = 91`, `η₁ = η₂ = η₃ = 27`, `η₄ = 29`, …, `η₁₃ = 38`)
   there is a saddle point `τ₀` of the saddle-point equation in the upper half-plane,
   of maximal real part, with `Re τ₀ < η₀` and `Im f₀(τ₀) ∉ πℤ` (Lemma 2 of the note,
   plus the arithmetic content of `zudilin_numeric_C0_gt_C1`).

2. `ZudilinZeta.zudilin_numeric_C0_gt_C1` — at these parameters
   `C₀ = 227.58019641…` and `C₁ = 226.24944266…`, hence `C₁ < C₀`
   (the final paragraph of the note; rigorous bounds may be used).

3. `ZudilinZeta.zudilin_lemma3` — for `r = 3`, the inequality `C₁ < C₀` implies that
   one of `ζ(5), ζ(7), …, ζ(q-2)` is irrational; for `q = 13` this is the window
   `{ζ(5), ζ(7), ζ(9), ζ(11)}` (Lemma 3 of the note, with `k ∈ Icc 1 ((q-r-2)/2)`).

4. `ZudilinZeta.zetaR_eq_riemannZeta` — for `k ≥ 2` the series
   `zetaR k = ∑ₙ (n+1)⁻ᵏ` equals Mathlib's `riemannZeta (k : ℂ)`, so the
   irrationality statements transfer from the `ZudilinZeta` layer to the
   `FCP.Zeta` statement of the goal.

The small window arithmetic (`k ∈ Icc 1 4` ⇒ `3 + 2k ∈ {5, 7, 9, 11}`) is carried
out below by `interval_cases` + `simp`.
-/

open ZudilinZeta

lemma zeta_irr_of_window {a : ℕ} (ham : a ∈ ({5, 7, 9, 11} : Set ℕ))
    (hirr : Irrational (zetaR a)) (hge : 2 ≤ a) :
    a ∈ ({5, 7, 9, 11} : Set ℕ) ∩ {a : ℕ | ∃ x : ℝ, Irrational x ∧ riemannZeta a = x} := by
  rw [Set.mem_inter_iff]
  refine ⟨ham, ?_⟩
  change ∃ x : ℝ, Irrational x ∧ riemannZeta a = x
  exact ⟨zetaR a, hirr, zetaR_eq_riemannZeta a hge⟩

theorem solution :
    ({5, 7, 9, 11} ∩ {a : ℕ | ∃ x : ℝ, Irrational x ∧ riemannZeta a = x}).Nonempty := by
  rcases exists_saddle_root_params13 with ⟨τ₀, hroot, him, hmax, hre, hpi⟩
  have hC : C1 params13 < C0 params13 τ₀ :=
    (zudilin_numeric_C0_gt_C1 τ₀ hroot him hmax).2.2
  have h3 : ∃ k : ℕ, (1 ≤ k ∧ k ≤ 4) ∧ Irrational (zetaR (3 + 2 * k)) := by
    have h := zudilin_lemma3 params13 (by rfl) τ₀ hroot him hmax hre hpi hC
    norm_num [params13] at h
    exact h
  rcases h3 with ⟨k, hk14, hirk⟩
  have hkge : 1 ≤ k := hk14.1
  have hkle : k ≤ 4 := hk14.2
  have hge : 2 ≤ 3 + 2 * k := by omega
  have ham : 3 + 2 * k ∈ ({5, 7, 9, 11} : Set ℕ) := by
    interval_cases k <;> simp
  have hirr : Irrational (zetaR (3 + 2 * k)) := hirk
  rw [Set.Nonempty]
  exact ⟨3 + 2 * k, zeta_irr_of_window ham hirr hge⟩
