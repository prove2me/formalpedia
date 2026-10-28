-- Prove2me | solution 2 for AvramDividend.Classical.survived_nextRecord_strict_shifted_exit_with_minimal_imports
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:52:45.235771+00:00
-- url     : https://prove2.me/submissions/8682f14e-b165-4aea-87ae-33659f37dcd9

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_upclock_le_lower_exit
import Theorems.Thm_AvramDividend_Classical_separated_strict_passage_infima_no_finite_tie
import Theorems.Thm_AvramDividend_Classical_levy_shiftedIncrements_rightContinuous
import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (u v δ : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω)
    (hδ : u + δ = v)
    (hSurvive : (v : ℝ≥0∞) < barrierRuinTime X a ω) :
    (⨅ (t : ℝ≥0)
        (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)) <
    (⨅ (t : ℝ≥0)
        (_ : X.X (u + t) ω - X.X u ω < -a), (t : ℝ≥0∞)) := by
  have hle := survived_nextRecord_shifted_upclock_le_lower_exit
    X ω a b ε ha hb hε u v δ hu hAt hv hδ hSurvive
  rcases lt_or_eq_of_le hle with hstrict | heq
  · exact hstrict
  · exfalso
    have hclock := nextRecord_upclock_eq_add_shifted_inf
      X b ε hε u ω hu hAt
    have hcoeeq : (u : ℝ≥0∞) + (δ : ℝ≥0∞) =
        (u : ℝ≥0∞) + (⨅ (t : ℝ≥0)
        (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)) := by
      calc
        (u : ℝ≥0∞) + (δ : ℝ≥0∞) =
          ((u + δ : ℝ≥0) : ℝ≥0∞) := by simp
        _ = (v : ℝ≥0∞) := by rw [hδ]
        _ = (u : ℝ≥0∞) + (⨅ (t : ℝ≥0)
        (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)) := hv.trans hclock
    have hup : (δ : ℝ≥0∞) = (⨅ (t : ℝ≥0)
        (_ : ε < X.X (u + t) ω - X.X u ω), (t : ℝ≥0∞)) :=
      (ENNReal.add_right_inj (by simp : (u : ℝ≥0∞) ≠ ⊤)).mp hcoeeq
    have hdown : (δ : ℝ≥0∞) = (⨅ (t : ℝ≥0)
        (_ : X.X (u + t) ω - X.X u ω < -a), (t : ℝ≥0∞)) := hup.trans heq
    have hsep : -a < ε := by linarith
    exact separated_strict_passage_infima_no_finite_tie
      (fun t : ℝ≥0 => X.X (u + t) ω - X.X u ω)
      δ (-a) ε hsep
      (levy_shiftedIncrements_rightContinuous X ω u δ) hup hdown
