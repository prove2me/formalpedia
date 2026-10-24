-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_exit_success_antitone_upper_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:31:33.461917+00:00
-- url     : https://prove2.me/submissions/aaf21e97-341a-4d6c-9e71-cf00c70cc9cf

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-!
Raising the upper barrier delays strict upcrossing and can only remove
paths from the event of crossing that barrier before ruin. The result
is pointwise and includes infinite crossing times.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b x : ℝ) (hab : a ≤ b) (ω : Ω) :
    twoSidedExitUpTime X (a - x) ω ≤
      twoSidedExitUpTime X (b - x) ω ∧
    (twoSidedExitUpTime X (b - x) ω <
       twoSidedExitDownTime X (-x) ω →
     twoSidedExitUpTime X (a - x) ω <
       twoSidedExitDownTime X (-x) ω) := by
  have hthreshold : a - x ≤ b - x := sub_le_sub_right hab x
  have hup :
      twoSidedExitUpTime X (a - x) ω ≤
        twoSidedExitUpTime X (b - x) ω := by
    change (⨅ t : ℝ≥0, ⨅ _ : a - x < X.X t ω, (t : ℝ≥0∞)) ≤
      (⨅ t : ℝ≥0, ⨅ _ : b - x < X.X t ω, (t : ℝ≥0∞))
    refine le_iInf fun t => le_iInf fun ht => ?_
    exact iInf_le_of_le t (iInf_le _ (lt_of_le_of_lt hthreshold ht))
  exact ⟨hup, fun hsuccess => lt_of_le_of_lt hup hsuccess⟩
