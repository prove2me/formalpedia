-- Prove2me | solution 1 for FirstPassageLinearTransport.normalized_card_shellPrefixMultiplicativeHit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:35:15.050088+00:00
-- url     : https://prove2.me/submissions/c6d33f98-b624-47fa-afaa-54680ce699dc

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Theorems.Thm_FirstPassageLinearTransport_card_shellPrefixMultiplicativeHit

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (M h : ℕ) (hhM : h ≤ M) (u : ℝ) :
    ((shellPrefixMultiplicativeHit M h hhM u).card : ℝ) /
        (2 : ℝ) ^ M =
      (multiplicativeHitCount u h 1 : ℝ) / (2 : ℝ) ^ h := by
  rw [card_shellPrefixMultiplicativeHit]
  push_cast
  have hpow : (2 : ℝ) ^ M =
      (2 : ℝ) ^ (M - h) * (2 : ℝ) ^ h := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  field_simp
end FirstPassageLinearTransport
