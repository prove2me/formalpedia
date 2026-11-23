-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_card_gt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:07.869127+00:00
-- url     : https://prove2.me/submissions/d7dba729-6ef2-4fd1-b19d-bbe2fd92a8a5

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable {R : Type*} [CommRing R] (g : Matrix (Fin n) (Fin n) R)
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {h : ℕ} (s : Finset (Fin n)) (hs : s.card = h + 1) (j : Fin (h + 1)) :
    ((s.erase (s.orderEmbOfFin hs j)).filter (s.orderEmbOfFin hs j < ·)).card = h - j := by
  have : (s.erase (s.orderEmbOfFin hs j)).filter (s.orderEmbOfFin hs j < ·) =
      (Finset.Ioi j).map (s.orderEmbOfFin hs).toEmbedding := by
    ext x
    simp only [mem_filter, mem_erase, mem_map, mem_Ioi, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨⟨_, hx⟩, hlt⟩
      have hx' : x ∈ Set.range (s.orderEmbOfFin hs) := by rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨i, rfl⟩ := hx'
      exact ⟨i, (s.orderEmbOfFin hs).lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨((s.orderEmbOfFin hs).lt_iff_lt.2 hi).ne', Finset.orderEmbOfFin_mem _ _ _⟩,
        (s.orderEmbOfFin hs).lt_iff_lt.2 hi⟩
  rw [this, card_map, Fin.card_Ioi]; omega
end Formalism.InvariantFactorPaths.ColumnFamilies
