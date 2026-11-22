-- Prove2me | solution 1 for GRH.primitive_nonprincipal_fourth_power_ramp_window_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @GeorgeCoote
-- created : 2026-11-21T17:26:36.18364+00:00
-- url     : https://prove2.me/submissions/ccd7261a-3f14-4213-a39b-8a94e333d691
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlpoegeClaudeRH_EveryCharacter
import Theorems.Thm_GRH_nonprincipal_corrected_prime_ramp_mellin_inversion_of_zero_free
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Finset ArithmeticFunction MeasureTheory

theorem solution :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ θ : ℝ, 1/2 < θ → θ ≤ (0.8749570698:ℝ) → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
        ∀ K₀ : ℕ, ∃ K : ℕ, K₀ ≤ K ∧ 1 ≤ K ∧
          ∀ j : ℕ, K ≤ j → (j-1)^4 ≤ ⌊((K^4 : ℕ):ℝ)^(1+δ)⌋₊+1 →
          let k := j^4
          (∑ n ∈ range (k+1), vonMangoldt n * (χ (n:ZMod q)).re *
            max ((k:ℝ)/(n:ℝ)-1) 0) +
            (k:ℝ) * (deriv χ.LFunction 1 / χ.LFunction 1).re ≤ C*(k:ℝ)^θ := by
  intro q _ χ _ hχ θ hθ hθmax
  have hθ₁ : θ < 1 := hθmax.trans_lt (by norm_num)
  have hZero (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) : χ.LFunction z ≠ 0 :=
    AlpoegeClaudeRH.EveryCharacter q χ z hz (Or.inl hχ)
  let s (t : ℝ) : ℂ := (θ : ℂ) + (t : ℂ) * Complex.I
  let F (t : ℝ) : ℂ := -logDeriv χ.LFunction (s t) / (s t * (s t - 1))
  obtain ⟨hF, hRamp⟩ :=
    GRH.nonprincipal_corrected_prime_ramp_mellin_inversion_of_zero_free χ hχ
      (1 / 2) θ (by norm_num) hθ hθ₁ hZero
  change Integrable F at hF
  let factor : ℂ := 1 / (2 * (Real.pi : ℂ))
  let C : ℝ := ‖factor‖ * ∫ t : ℝ, ‖F t‖
  refine ⟨1, C, zero_lt_one, mul_nonneg (norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _),
    fun K₀ => ⟨max K₀ 2, le_max_left _ _, (by decide : 1 ≤ 2).trans (le_max_right _ _), ?_⟩⟩
  intro j hj _
  have hj₂ : 2 ≤ j := (le_max_right K₀ 2).trans hj
  have hk : 1 < j ^ 4 := (by decide : 1 < 2 ^ 4).trans_le (Nat.pow_le_pow_left hj₂ _)
  let k : ℕ := j ^ 4
  have hy : 1 < (k : ℝ) := by exact_mod_cast hk
  have hy₀ : 0 < (k : ℝ) := zero_lt_one.trans hy
  have hNorm (t : ℝ) : ‖((k : ℝ) : ℂ) ^ s t * F t‖ = (k : ℝ) ^ θ * ‖F t‖ := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy₀]
    simp [s]
  have hIntegral := norm_integral_le_of_norm_le (hF.norm.const_mul ((k : ℝ) ^ θ))
    (Filter.Eventually.of_forall fun t => (hNorm t).le)
  rw [integral_const_mul] at hIntegral
  have hReal := congrArg Complex.re (hRamp (k : ℝ) hy)
  simp only [Complex.add_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Complex.mul_im,
    Nat.floor_natCast] at hReal
  change _ ≤ C * (k : ℝ) ^ θ
  rw [hReal]
  calc
    _ ≤ ‖factor * ∫ t : ℝ, ((k : ℝ) : ℂ) ^ s t * F t‖ := Complex.re_le_norm _
    _ = ‖factor‖ * ‖∫ t : ℝ, ((k : ℝ) : ℂ) ^ s t * F t‖ := norm_mul _ _
    _ ≤ ‖factor‖ * ((k : ℝ) ^ θ * ∫ t : ℝ, ‖F t‖) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg _)
    _ = C * (k : ℝ) ^ θ := by dsimp only [C]; ring
