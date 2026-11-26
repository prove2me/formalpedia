-- Prove2me | solution 1 for FirstPassageLinearTransport.card_periodicMultiplicativeHitBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:28.790804+00:00
-- url     : https://prove2.me/submissions/d6fbc984-b847-4534-a660-14c008f70a74

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Theorems.Thm_FirstPassageLinearTransport_card_multiplicativeHitResidues


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (N t h : ℕ) (u : ℝ) :
    (periodicMultiplicativeHitBlock N t h u).card =
      (t - N) * multiplicativeHitCount u h 1 := by
  classical
  rw [periodicMultiplicativeHitBlock, Finset.card_map]
  calc
    ((Finset.Ico N t).product (multiplicativeHitResidues h u)).card =
        (Finset.Ico N t).card * (multiplicativeHitResidues h u).card :=
      Finset.card_product _ _
    _ = (t - N) * multiplicativeHitCount u h 1 := by
      rw [Nat.card_Ico, card_multiplicativeHitResidues]
end FirstPassageLinearTransport
