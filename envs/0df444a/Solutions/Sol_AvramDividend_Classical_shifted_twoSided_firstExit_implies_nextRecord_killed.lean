-- Prove2me | solution 1 for AvramDividend.Classical.shifted_twoSided_firstExit_implies_nextRecord_killed
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:47:32.228691+00:00
-- url     : https://prove2.me/submissions/d5db46c6-3a27-4fa5-a00c-7c8e3ff116a5

import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_raw_twoSidedFutureExit_prefix_strip
import Theorems.Thm_AvramDividend_Classical_shifted_future_strip_implies_drawdown_guard
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_nextRecord_killed_survival_of_shifted_guard

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
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
  have hstrip := AvramDividend.Classical.raw_twoSidedFutureExit_prefix_strip
    (fun r => X.X (u + r) ω - X.X u ω) ε a T hUp hUpBeforeDown
  have hlow : ∀ t : ℝ≥0, t ≤ T → ε - a ≤ X.X (u + t) ω - X.X u ω := by
    intro t ht
    rcases lt_or_eq_of_le ht with h | rfl
    · exact (hstrip t h).1
    · by_contra hc
      push_neg at hc
      have : (⨅ (r : ℝ≥0) (_ : X.X (u + r) ω - X.X u ω < ε - a), (r : ℝ≥0∞)) ≤ t := iInf₂_le t hc
      exact absurd (lt_of_lt_of_le hUpBeforeDown this) (lt_irrefl _)
  have hPost : ∀ t : ℝ≥0, t ≤ T →
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) - X.X (u + t) ω ≤ a := by
    intro t ht
    have hS : sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) ≤ X.X (u + t) ω + a := by
      apply csSup_le ((Set.nonempty_Icc.2 (zero_le (a := t))).image _)
      rintro _ ⟨r, hr, rfl⟩
      have h1 := hlow t ht
      rcases lt_or_eq_of_le (hr.2.trans ht) with h | h
      · have h2 := (hstrip r h).2
        linarith
      · have hrt : r = t := le_antisymm hr.2 (h ▸ ht)
        rw [hrt]; linarith
    linarith
  have hv : ((u + T : ℝ≥0) : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω := by
    rw [AvramDividend.Classical.nextRecord_upclock_eq_add_shifted_inf X b ε hε u ω hu hAt, ← hUp,
      ENNReal.coe_add]
  rw [← hv]
  exact AvramDividend.Classical.nextRecord_killed_survival_of_shifted_guard X a b ε ha hb hε ω u (u + T) T
    hu hv hBefore le_rfl hPost
