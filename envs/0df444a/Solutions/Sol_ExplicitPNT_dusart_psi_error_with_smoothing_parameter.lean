-- Prove2me | solution 1 for ExplicitPNT.dusart_psi_error_with_smoothing_parameter
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @chaikon
-- created : 2026-10-14T03:09:09.435685+00:00
-- url     : https://prove2.me/submissions/26fb9f5b-9843-49c8-9421-3ca60264998f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Theorems.Thm_ExplicitPNT_dusart_k_root_exists
import Theorems.Thm_ExplicitPNT_dusart_G2_lt_exp
import Theorems.Thm_ExplicitPNT_dusart_psi_smoothed_explicit_bound

/-!
Proof sketch of Dusart's smoothing estimate (HDR, proof of Théorème 45, printed p. 46).

* `dusart_k_root_exists` is Lemme 51: a root `ν ∈ (0.97, 1)` of `k(ν) = 1`.
* `dusart_psi_smoothed_explicit_bound` is the bound
  `|ψ(x) - x| < x G₂ (G₀G₁)^{1/4} √(8/π) X^{1/2} e^{-X} (1 + 3.27 X^{1/2} e^{-X})`
  obtained from Lemma 8 of Rosser–Schoenfeld and Lemmes 50, 52, 53, 54.
* `dusart_G2_lt_exp` is Lemme 55: `G₂ < exp(2.64 X^{1/2} e^{-X})`.

What remains is `G₂ (1 + 3.27 t) < exp(5.91 t)` for `t = X^{1/2} e^{-X}`.
-/

theorem solution
    (R : ℝ) (hR : 0 < R)
    (hzero : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0)
    (x : ℝ) (hx : 0 < x)
    (hX : max (836 / 100 : ℝ) (8 / R) < Real.sqrt (Real.log x / R)) :
    let X := Real.sqrt (Real.log x / R)
    ∃ ν : ℝ, (97 / 100 : ℝ) < ν ∧ ν < 1 ∧
      |Chebyshev.psi x - x| <
        x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) *
          (Real.sqrt (Real.sqrt
            (ν ^ 6 / (2 * ν ^ 2 - 1) *
              (1 - (Real.log (2 * Real.pi) - 1 / 2) / (X * ν)) *
              (1 - Real.log (2 * Real.pi) / (X * ν)))) *
            Real.exp ((591 / 100 : ℝ) * Real.sqrt X * Real.exp (-X))) := by
  intro X
  have hX8 : (836 / 100 : ℝ) < X := lt_of_le_of_lt (le_max_left _ _) hX
  obtain ⟨ν, h0, hν0, hν1, hk⟩ := ExplicitPNT.dusart_k_root_exists X hX8.le
  have h97 : (97 / 100 : ℝ) < ν := h0.trans hν0
  refine ⟨ν, h97, hν1, ?_⟩
  have hmain := ExplicitPNT.dusart_psi_smoothed_explicit_bound R hR hzero x hx hX ν h97 hν1 hk
  have hG := ExplicitPNT.dusart_G2_lt_exp X ν hX8 h97 hν1 hk
  simp only at hmain hG
  set t : ℝ := Real.sqrt X * Real.exp (-X) with ht
  set S : ℝ := Real.sqrt (Real.sqrt
            (ν ^ 6 / (2 * ν ^ 2 - 1) *
              (1 - (Real.log (2 * Real.pi) - 1 / 2) / (X * ν)) *
              (1 - Real.log (2 * Real.pi) / (X * ν)))) with hS
  set G := ((1 + Real.sqrt (2 / Real.pi) * S *
      Real.exp (-(X * (1 - ν) ^ 2 / ν) / 2) * Real.sqrt X * Real.exp (-X)) ^ 3 + 1) ^ 2 / 2 ^ 2 *
    (1 + 2 * Real.pi * (((137 / 1000 : ℝ) * Real.log (Real.exp (ν * X)) + 443 / 1000) /
      (Real.exp (ν * X) * Real.log (Real.exp (ν * X)) *
        Real.log (Real.exp (ν * X) / (2 * Real.pi))))) with hGdef
  have ht0 : 0 ≤ t := mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  have hB : 0 ≤ x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) * S := by
    have := Real.sqrt_nonneg (8 / Real.pi)
    have := Real.sqrt_nonneg X
    have := Real.exp_pos (-X)
    have : 0 ≤ S := Real.sqrt_nonneg _
    positivity
  have hG' : G < Real.exp ((264 / 100 : ℝ) * t) := by
    simpa only [ht, mul_assoc] using hG
  have h1 : 1 + (327 / 100 : ℝ) * t ≤ Real.exp ((327 / 100 : ℝ) * t) := by
    have := Real.add_one_le_exp ((327 / 100 : ℝ) * t)
    linarith
  have hprod : G * (1 + (327 / 100 : ℝ) * t) ≤ Real.exp ((591 / 100 : ℝ) * t) := by
    have hpos : 0 ≤ 1 + (327 / 100 : ℝ) * t := by positivity
    calc G * (1 + (327 / 100 : ℝ) * t)
        ≤ Real.exp ((264 / 100 : ℝ) * t) * (1 + (327 / 100 : ℝ) * t) :=
          mul_le_mul_of_nonneg_right hG'.le hpos
      _ ≤ Real.exp ((264 / 100 : ℝ) * t) * Real.exp ((327 / 100 : ℝ) * t) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp ((591 / 100 : ℝ) * t) := by
          rw [← Real.exp_add]; ring_nf
  have hmain' : |Chebyshev.psi x - x| <
      (x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) * S) *
        (G * (1 + (327 / 100 : ℝ) * t)) := by
    have : x * G * S * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) *
        (1 + (327 / 100 : ℝ) * Real.sqrt X * Real.exp (-X)) =
        (x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) * S) *
          (G * (1 + (327 / 100 : ℝ) * t)) := by
      rw [ht]; ring
    rw [← this]
    exact hmain
  calc |Chebyshev.psi x - x|
      < (x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) * S) *
          (G * (1 + (327 / 100 : ℝ) * t)) := hmain'
    _ ≤ (x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) * S) *
          Real.exp ((591 / 100 : ℝ) * t) := mul_le_mul_of_nonneg_left hprod hB
    _ = x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) *
          (S * Real.exp ((591 / 100 : ℝ) * Real.sqrt X * Real.exp (-X))) := by
        rw [ht]; ring_nf
