-- Prove2me | solution 1 for FirstPassageLinearTransport.shellMaximalParityBad_subset_hit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:24:35.016692+00:00
-- url     : https://prove2.me/submissions/04b07351-bc04-4b71-ae8f-692f2cbe04a9

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Theorems.Thm_FirstPassageLinearTransport_maximalParityRegular_of_not_hitsBarrier

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution (M : ℕ) (h : ℝ) :
    shellMaximalParityBad M h ⊆ shellBarrierHit M h := by
  classical
  intro n hn
  rw [shellMaximalParityBad, Finset.mem_filter] at hn
  rw [shellBarrierHit, Finset.mem_filter]
  refine ⟨hn.1, ?_⟩
  by_contra hnot
  exact hn.2 (maximalParityRegular_of_not_hitsBarrier hnot)
end FirstPassageLinearTransport
