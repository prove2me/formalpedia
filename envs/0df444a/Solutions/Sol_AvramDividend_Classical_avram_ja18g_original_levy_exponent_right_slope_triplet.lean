-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_levy_exponent_right_slope_triplet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:16:51.453807+00:00
-- url     : https://prove2.me/submissions/2582d784-6068-421a-8403-5d025b00069c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_small_negative_exp_quotient_zero
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_large_negative_exp_quotient_signed
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_psi_small_large_integral_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Combine the genuine small/large jump limits with the exact original Lévy integral split. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    Filter.Tendsto (fun θ : ℝ => X.ψ θ / θ)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (X.c + (∫ z in Iic (-1 : ℝ), z ∂X.ν))) := by
  let l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0)
  let small : ℝ → ℝ := fun θ =>
    ∫ z in Ioo (-1 : ℝ) 0, Real.exp (θ * z) - 1 - θ * z ∂X.ν
  let large : ℝ → ℝ := fun θ =>
    ∫ z in Iic (-1 : ℝ), Real.exp (θ * z) - 1 ∂X.ν
  have hθ : Tendsto (fun θ : ℝ => θ) l (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hσ : Tendsto
      (fun θ : ℝ => X.σ ^ 2 * θ / 2) l (nhds 0) := by
    simpa using ((tendsto_const_nhds.mul hθ).div_const (2 : ℝ))
  have hs : Tendsto (fun θ => small θ / θ) l (nhds 0) := by
    exact avram_ja18g_original_small_negative_exp_quotient_zero X
  have hb : Tendsto (fun θ => large θ / θ) l
      (nhds (∫ z in Iic (-1 : ℝ), z ∂X.ν)) := by
    exact avram_ja18g_original_large_negative_exp_quotient_signed X hX hFinite
  have hsum : Tendsto
      (fun θ => ((X.c + X.σ ^ 2 * θ / 2) + small θ / θ) + large θ / θ)
      l (nhds (X.c + (∫ z in Iic (-1 : ℝ), z ∂X.ν))) := by
    convert (((tendsto_const_nhds.add hσ).add hs).add hb) using 1
    simp
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθpos
  change (0 : ℝ) < θ at hθpos
  have hsplit :=
    avram_ja18g_original_psi_small_large_integral_split X hX hFinite θ hθpos.le
  change ((X.c + X.σ ^ 2 * θ / 2) + small θ / θ) +
    large θ / θ = X.ψ θ / θ
  rw [hsplit]
  dsimp [small, large]
  field_simp [ne_of_gt hθpos]
