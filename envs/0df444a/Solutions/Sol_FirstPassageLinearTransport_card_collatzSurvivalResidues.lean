-- Prove2me | solution 1 for FirstPassageLinearTransport.card_collatzSurvivalResidues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:30.160798+00:00
-- url     : https://prove2.me/submissions/d39a6c3e-c763-4e6a-8e71-7ec1d4dcffdd

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (m : ℕ) (B : ℝ) :
    (collatzSurvivalResidues m B).card =
      (collatzSurvivalWords m B).card := by
  classical
  unfold collatzSurvivalResidues collatzSurvivalWords
  rw [← Fintype.card_subtype (fun x : Fin (2 ^ m) =>
        wordSurvivesFrom (-B) collatzLogIncrement m 0 (boolParityCode m x)),
      ← Fintype.card_subtype
        (wordSurvivesFrom (-B) collatzLogIncrement m 0)]
  exact Fintype.card_congr (collatzSurvivalResidueEquiv m B)
end FirstPassageLinearTransport
