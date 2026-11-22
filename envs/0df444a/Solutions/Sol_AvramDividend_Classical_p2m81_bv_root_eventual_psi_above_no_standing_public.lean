-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_root_eventual_psi_above_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T06:32:09.710611+00:00
-- url     : https://prove2.me/submissions/73587417-06fd-4303-a670-bdee925bc3b0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_convexOn_nonnegative
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hBV : X.BoundedVariation) :
    ∃ β₀ : ℝ, 0 ≤ β₀ ∧ ∀ θ : ℝ, β₀ ≤ θ → q < X.ψ θ := by
  have hconv := levy_laplace_exponent_convexOn_nonnegative X
  have hψ0 : X.ψ 0 = 0 := by
    simp only [SpectrallyNegativeLevy.ψ, laplaceExponent]
    simp
  refine ⟨2 * φ, by linarith [hφ], ?_⟩
  intro θ hθ
  have hθpos : 0 < θ := by linarith [hφ, hθ]
  have hθne : θ ≠ 0 := ne_of_gt hθpos
  have hb_pos : 0 < φ / θ := div_pos hφ hθpos
  have hb_nonneg : 0 ≤ φ / θ := le_of_lt hb_pos
  have hr_half : φ / θ ≤ 1 / 2 := by
    rw [div_le_iff₀ hθpos]
    linarith [hθ]
  have hb_le_one : φ / θ ≤ 1 := by linarith [hr_half]
  have ha_nonneg : 0 ≤ 1 - φ / θ := by linarith [hb_le_one]
  have hab : (1 - φ / θ) + φ / θ = 1 := by ring
  have h0mem : (0 : ℝ) ∈ Ici (0 : ℝ) := mem_Ici.mpr le_rfl
  have hθmem : θ ∈ Ici (0 : ℝ) := mem_Ici.mpr (le_of_lt hθpos)
  have hj := hconv.2 h0mem hθmem ha_nonneg hb_nonneg hab
  simp only [smul_eq_mul] at hj
  have hdiv : (φ / θ) * θ = φ := div_mul_cancel₀ φ hθne
  have harg : (1 - φ / θ) * 0 + (φ / θ) * θ = φ := by
    rw [mul_zero, zero_add]
    exact hdiv
  rw [harg, hψ0] at hj
  simp only [mul_zero, zero_add] at hj
  rw [hroot] at hj
  have hYpos : 0 < X.ψ θ := by
    have hpos : 0 < (φ / θ) * X.ψ θ := by linarith [hq, hj]
    exact pos_of_mul_pos_right hpos hb_nonneg
  have hmul : (φ / θ) * X.ψ θ ≤ (1 / 2) * X.ψ θ :=
    mul_le_mul_of_nonneg_right hr_half (le_of_lt hYpos)
  have h2q : q ≤ (1 / 2) * X.ψ θ := le_trans hj hmul
  linarith [h2q, hq]
