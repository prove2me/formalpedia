-- Prove2me | solution 2 for AvramDividend.Classical.survived_nextRecord_shifted_upclock_lt_lower_exit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:53:04.063568+00:00
-- url     : https://prove2.me/submissions/c53b02ed-65b1-448d-9fb0-0db2133caf4e

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_upclock_le_lower_exit
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_levy_shifted_exit_strict_order_of_finite_weak_order

open AvramDividend.Classical MeasureTheory Set
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
  have hle := survived_nextRecord_shifted_upclock_le_lower_exit X ω a b ε ha hb hε u v δ hu hAt hv hδ hSurvive
  have h1 := nextRecord_upclock_eq_add_shifted_inf X b ε hε u ω hu hAt
  rw [← hv, ← hδ, ENNReal.coe_add] at h1
  have hI := (ENNReal.add_right_inj ENNReal.coe_ne_top).1 h1
  refine levy_shifted_exit_strict_order_of_finite_weak_order X ω u (-a) ε (by linarith) ?_ hle
  rw [← hI]; exact ENNReal.coe_ne_top
