-- Prove2me | solution 2 for AvramDividend.Classical.shifted_twoSided_firstExit_implies_nextRecord_killed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:48:58.84944+00:00
-- url     : https://prove2.me/submissions/cc491fef-c658-4763-8740-c70cb69ddc77

import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_raw_twoSidedFutureExit_prefix_strip
import Theorems.Thm_AvramDividend_Classical_shifted_future_strip_implies_drawdown_guard
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_nextRecord_killed_survival_of_shifted_guard
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! A successful shifted two-sided exit survives global reflected ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ω : Ω) (u T : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω)
    (hUp : (T : ℝ≥0∞) =
      (⨅ (r : ℝ≥0)
        (_ : ε < X.X (u + r) ω - X.X u ω), (r : ℝ≥0∞)))
    (hUpBeforeDown : (T : ℝ≥0∞) <
      (⨅ (r : ℝ≥0)
        (_ : X.X (u + r) ω - X.X u ω < ε - a),
        (r : ℝ≥0∞))) :
    twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω := by
  let g : ℝ≥0 → ℝ := fun r => X.X (u + r) ω - X.X u ω
  have hClock : twoSidedExitUpTime X (b + ε) ω =
      ((u + T : ℝ≥0) : ℝ≥0∞) := by
    rw [nextRecord_upclock_eq_add_shifted_inf X b ε hε u ω hu hAt]
    rw [← hUp, ← ENNReal.coe_add]
  have hNextValue : X.X (u + T) ω = b + ε :=
    firstUpcrossing_value_eq_threshold
      X (b + ε) (add_nonneg hb hε) ω (u + T) hClock.symm
  have hAtNext : g T = ε := by
    dsimp only [g]
    rw [hNextValue, hAt]
    linarith
  have hBand : ∀ r : ℝ≥0, r < T →
      ε - a ≤ g r ∧ g r ≤ ε :=
    raw_twoSidedFutureExit_prefix_strip g ε a T hUp hUpBeforeDown
  have hUpper : ∀ r : ℝ≥0, r ≤ T → g r ≤ ε := by
    intro r hr
    rcases lt_or_eq_of_le hr with hlt | heq
    · exact (hBand r hlt).2
    · subst r
      exact le_of_eq hAtNext
  have hLower : ∀ r : ℝ≥0, r ≤ T → ε - a ≤ g r := by
    intro r hr
    rcases lt_or_eq_of_le hr with hlt | heq
    · exact (hBand r hlt).1
    · subst r
      rw [hAtNext]
      exact sub_le_self ε (le_of_lt ha)
  have hPost :=
    shifted_future_strip_implies_drawdown_guard
      X a ε ω u T (by simpa only [g] using hUpper)
        (by simpa only [g] using hLower)
  have hKill :=
    nextRecord_killed_survival_of_shifted_guard
      X a b ε ha hb hε ω u (u + T) T hu hClock.symm
        hBefore (le_refl _) hPost
  rw [hClock]
  exact hKill
