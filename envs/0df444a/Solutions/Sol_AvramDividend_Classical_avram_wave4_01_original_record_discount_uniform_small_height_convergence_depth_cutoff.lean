-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_discount_uniform_small_height_convergence_depth_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:55:21.988663+00:00
-- url     : https://prove2.me/submissions/7b151c4f-9103-4ca9-bae4-ba57a3a4f195

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_uniform_small_height_linear_lower_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_reflected_record_discount_strict_lt_one_of_root
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-- Genuine source first-record survival converges uniformly to one over all depths above a fixed positive cutoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ∀ a : ℝ, δ ≤ a →
        1 - ε ≤
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal ∧
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal ≤ 1 := by
  let C : ℝ := |deriv W δ / W δ| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hCge : deriv W δ / W δ ≤ C := by
    dsimp [C]
    linarith [le_abs_self (deriv W δ / W δ)]
  have htpos : 0 < ε / C := div_pos hε hCpos
  have hnear : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      0 < h ∧ h < ε / C := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds htpos).filter_mono
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds (0 : ℝ))]
      with h hh hht
    exact ⟨hh, hht⟩
  filter_upwards [hnear] with h hh
  intro a hδa
  have hbound := avram_wave4_01_original_record_discount_uniform_small_height_linear_lower_bound
    X q hq W hW hvar δ a h hδ hδa hh.1
  have hupper := avram_wave4_01_reflected_record_discount_strict_lt_one_of_root
    X q hq φ hφ hroot a h hh.1
  have hm : h * (deriv W δ / W δ) ≤ h * C :=
    mul_le_mul_of_nonneg_left hCge (le_of_lt hh.1)
  have hsmall : h * C < ε := (lt_div_iff₀ hCpos).mp hh.2
  constructor
  · linarith
  · exact le_of_lt hupper
