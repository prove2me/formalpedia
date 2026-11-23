-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg_emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:42.126519+00:00
-- url     : https://prove2.me/submissions/539e3178-5c1a-4b8c-aae1-e55cec8884e9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution {d : ℕ} {J : Finset (Fin n)} (h : J.card = d + 1) (j : Fin (d + 1)) :
    sg J (J.orderEmbOfFin h j) = (-1) ^ (d + (j : ℕ)) := by
  have hf : (J.filter fun x => J.orderEmbOfFin h j < x) =
      (Finset.Ioi j).map (J.orderEmbOfFin h).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Ioi, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hx, hlt⟩
      have : x ∈ Set.range (J.orderEmbOfFin h) := by rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨k, rfl⟩ := this
      exact ⟨k, (J.orderEmbOfFin h).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem J h k, (J.orderEmbOfFin h).lt_iff_lt.mpr hk⟩
  unfold sg
  rw [hf, Finset.card_map, Fin.card_Ioi]
  have hj := j.isLt
  rw [show d + (j : ℕ) = (d + 1 - 1 - j) + 2 * j by omega, pow_add, pow_mul]
  simp
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
