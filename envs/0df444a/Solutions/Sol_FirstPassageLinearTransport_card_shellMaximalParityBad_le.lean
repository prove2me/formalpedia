-- Prove2me | solution 1 for FirstPassageLinearTransport.card_shellMaximalParityBad_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:26:38.592984+00:00
-- url     : https://prove2.me/submissions/c9b4c08d-31bb-4ff8-9901-7ef7cb3b621a

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Theorems.Thm_FirstPassageLinearTransport_barrierHitCount_le_exp
import Theorems.Thm_FirstPassageLinearTransport_card_shellBarrierHit
import Theorems.Thm_FirstPassageLinearTransport_shellMaximalParityBad_subset_hit

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution {M : ℕ} {h : ℝ}
    (hh : 0 ≤ h) (hM : 0 < M) :
    ((shellMaximalParityBad M h).card : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-(2 * h ^ 2 / (M : ℝ))) := by
  have hcard :
      (shellMaximalParityBad M h).card ≤ (shellBarrierHit M h).card :=
    Finset.card_le_card (shellMaximalParityBad_subset_hit M h)
  have hcardR :
      ((shellMaximalParityBad M h).card : ℝ) ≤
        ((shellBarrierHit M h).card : ℝ) := by exact_mod_cast hcard
  rw [card_shellBarrierHit] at hcardR
  exact hcardR.trans (barrierHitCount_le_exp h M hh hM)
end FirstPassageLinearTransport
