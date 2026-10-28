-- Prove2me | solution 2 for AvramDividend.Classical.nextRecord_killed_of_shifted_safe_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:33:34.266462+00:00
-- url     : https://prove2.me/submissions/a6853ec3-019a-43e2-ae55-eaac2971e676

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_le_shifted_witness
import Theorems.Thm_AvramDividend_Classical_nextRecord_killed_survival_of_shifted_guard

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Convert a finite shifted witness into a surviving higher first record. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ω : Ω) (u T : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hBefore : (u : ℝ≥0∞) < barrierRuinTime X a ω)
    (hNext : ε < X.X (u + T) ω - X.X u ω)
    (hPost : ∀ t : ℝ≥0, t ≤ T →
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
        X.X (u + t) ω ≤ a) :
    twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω := by
  let τ : ℝ≥0∞ := twoSidedExitUpTime X (b + ε) ω
  have hτle : τ ≤ ((u + T : ℝ≥0) : ℝ≥0∞) :=
    nextRecord_upclock_le_shifted_witness X b ε u T ω hAt hNext
  have hτne : τ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hτle
  let v : ℝ≥0 := τ.toNNReal
  have hv : (v : ℝ≥0∞) = τ := ENNReal.coe_toNNReal hτne
  have hvT : v ≤ u + T := by
    have h : (v : ℝ≥0∞) ≤ ((u + T : ℝ≥0) : ℝ≥0∞) := by
      simpa only [hv] using hτle
    exact_mod_cast h
  have hvRecord : (v : ℝ≥0∞) =
      twoSidedExitUpTime X (b + ε) ω := hv
  have hKill := nextRecord_killed_survival_of_shifted_guard
    X a b ε ha hb hε ω u v T hu hvRecord hBefore hvT hPost
  simpa only [hv] using hKill
