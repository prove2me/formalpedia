-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_origin_zero_of_superlinear_psi_nonnegative_q
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:33:54.852625+00:00
-- url     : https://prove2.me/submissions/06f50707-b987-4e58-8b28-368bf71061dd

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_laplace_origin_zero_of_normalised_small
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Superlinear Lévy exponent growth gives W(0) = 0 even at zero discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hgrowth : ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧
      ∀ θ : ℝ, β ≤ θ → C < X.ψ θ / θ) :
    W 0 = 0 := by
  rcases hgrowth (q + 1) with ⟨β, hβ, hfirst⟩
  apply laplace_origin_zero_of_normalised_small W X.ψ q β
    hW.2.1 hW.2.2.2.1
  · intro θ hθβ hθ
    have hθone : 1 ≤ θ := le_trans hβ hθβ
    have hθpos : 0 < θ := lt_of_lt_of_le (by norm_num) hθone
    have hg := hfirst θ hθβ
    have hgt : (q + 1) * θ < X.ψ θ :=
      (lt_div_iff₀ hθpos).mp hg
    have hqθ : q ≤ q * θ := by
      have hm := mul_le_mul_of_nonneg_left hθone hq
      nlinarith
    have hψ : q < X.ψ θ := by nlinarith
    simpa only [neg_mul] using (hW.2.2.2.2 θ (le_of_lt hθ) hψ)
  · intro ε hε
    rcases hgrowth (q + ε⁻¹ + 1) with ⟨β₂, hβ₂, hsecond⟩
    let θ : ℝ := max β β₂ + 1
    have hθβ : β ≤ θ := by
      have hm := le_max_left β β₂
      dsimp [θ]
      linarith
    have hθβ₂ : β₂ ≤ θ := by
      have hm := le_max_right β β₂
      dsimp [θ]
      linarith
    have hθone : 1 ≤ θ := le_trans hβ hθβ
    have hθpos : 0 < θ := lt_of_lt_of_le (by norm_num) hθone
    have hgt : (q + ε⁻¹ + 1) * θ < X.ψ θ :=
      (lt_div_iff₀ hθpos).mp (hsecond θ hθβ₂)
    have hqθ : q ≤ q * θ := by
      have hm := mul_le_mul_of_nonneg_left hθone hq
      nlinarith
    have hsmall : ε⁻¹ * θ < X.ψ θ - q := by nlinarith
    have hscaled : θ < ε * (X.ψ θ - q) := by
      have hh := mul_lt_mul_of_pos_left hsmall hε
      have hid : ε * (ε⁻¹ * θ) = θ := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hε), one_mul]
      simpa only [hid] using hh
    have hden : 0 < X.ψ θ - q := by
      have hnonneg : 0 ≤ ε⁻¹ * θ :=
        mul_nonneg (le_of_lt (inv_pos.mpr hε)) (le_of_lt hθpos)
      linarith
    refine ⟨θ, hθβ, hθpos, ?_⟩
    change θ / (X.ψ θ - q) < ε
    exact (div_lt_iff₀ hden).2 hscaled
