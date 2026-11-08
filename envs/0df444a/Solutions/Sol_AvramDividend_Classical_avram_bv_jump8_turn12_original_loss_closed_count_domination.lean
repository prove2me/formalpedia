-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn12_original_loss_closed_count_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:30:44.860318+00:00
-- url     : https://prove2.me/submissions/4ae3b6a7-84fc-4725-bfdc-e3d464ebf983

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn12_real_loss_ofReal_sum
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn13_original_loss_le_strict_card
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_strict_finite_set_card_le_closed
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_interval_negative_band_count_ncard

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The independent finite-loss/cardinality bound combines with the already
proved original strict-to-closed count comparison. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((k : ℝ) + 1))))
    ∀ ω : Ω, 0 ≤ L ω ∧ L ω ≤ (N ω).toReal := by
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
    (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((k : ℝ) + 1))))
  change ∀ ω : Ω, 0 ≤ L ω ∧ L ω ≤ (N ω).toReal
  intro ω
  have hnon : 0 ≤ L ω := by
    have h := avram_bv_jump8_turn12_real_loss_ofReal_sum X hX hBV k n
    simpa only [T, S, L] using (h ω).1
  have hsum : L ω ≤ ((S ω).card : ℝ) := by
    simpa only [T, S, L] using
      (avram_bv_jump8_turn13_original_loss_le_strict_card X hX hBV k n ω)
  let Cω : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
      -(1 / ((k : ℝ) + 1))}
  have hcardNat : (S ω).card ≤ Cω.ncard := by
    simpa only [S, Cω] using
      (avram_bv_jump8_turn10_strict_finite_set_card_le_closed X ω T k)
  have hcard : ((S ω).card : ℝ) ≤ (Cω.ncard : ℝ) := by
    exact_mod_cast hcardNat
  have hcount : N ω = (Cω.ncard : ℝ≥0∞) := by
    simpa only [N, Cω] using
      (avram_p2_e_compensator_original_interval_negative_band_count_ncard
        X ω 0 T (by exact zero_le) k)
  have hreal : (N ω).toReal = (Cω.ncard : ℝ) := by
    rw [hcount]
    simp
  constructor
  · exact hnon
  · calc
      L ω ≤ (Cω.ncard : ℝ) := hsum.trans hcard
      _ = (N ω).toReal := hreal.symm
