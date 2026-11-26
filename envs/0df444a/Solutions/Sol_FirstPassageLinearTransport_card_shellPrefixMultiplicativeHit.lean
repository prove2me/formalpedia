-- Prove2me | solution 1 for FirstPassageLinearTransport.card_shellPrefixMultiplicativeHit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:15.682831+00:00
-- url     : https://prove2.me/submissions/05a021a9-7502-4506-afe6-bdb4909256e7

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Theorems.Thm_FirstPassageLinearTransport_card_shellPrefixResidueSet
import Theorems.Thm_FirstPassageLinearTransport_card_multiplicativeHitResidues


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (M h : ℕ) (hhM : h ≤ M) (u : ℝ) :
    (shellPrefixMultiplicativeHit M h hhM u).card =
      2 ^ (M - h) * multiplicativeHitCount u h 1 := by
  rw [shellPrefixMultiplicativeHit, card_shellPrefixResidueSet,
    card_multiplicativeHitResidues]
end FirstPassageLinearTransport
