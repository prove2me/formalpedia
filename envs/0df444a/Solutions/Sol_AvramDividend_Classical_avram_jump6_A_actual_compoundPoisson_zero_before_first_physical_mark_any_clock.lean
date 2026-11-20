-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_actual_compoundPoisson_zero_before_first_physical_mark_any_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:35:52.377178+00:00
-- url     : https://prove2.me/submissions/35d33170-b420-4f92-98d1-306f29911453

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Finset
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (τ Y : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω)
    (ht : t < arrival τ 0 ω) :
    compoundPoisson (0 : ℝ) τ Y t ω = 0 := by
  have hz : jumpCount (fun n => arrival τ n ω) t = 0 := by
    exact Nat.le_zero.mp (Nat.sInf_le
      (show (0 : ℕ) ∈ {n | t < arrival τ n ω} from ht))
  simp [compoundPoisson, piecewisePath, hz]
