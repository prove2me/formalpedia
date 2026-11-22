-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_wtT_can
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:40:54.50443+00:00
-- url     : https://prove2.me/submissions/4ed26a03-8dbc-403b-be47-6523ccc87e13

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreW
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_mem_canT
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_lt_colH_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_le_lastIdx

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
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {mu : Fin n → ℤ} (hmu : Dominant mu) : qb_wtT mu (canT mu) = mu := by
  funext b
  unfold qb_wtT
  have e : ((univ.filter fun c : ↥(TCols mu) => b ∈ (canT mu c).1).map (Function.Embedding.subtype _)) =
      Finset.Ioc (mu (lastIdx n)) (mu b) := by
    ext c
    rw [mem_map, mem_Ioc]
    constructor
    · rintro ⟨⟨c', hc'⟩, h1, rfl⟩
      rw [mem_filter, qb_mem_canT, qb_lt_colH_iff hmu] at h1
      exact ⟨(mem_Ioc.1 hc').1, h1.2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨⟨c, mem_Ioc.2 ⟨h1, h2.trans (hmu (Fin.zero_le b))⟩⟩, ?_, rfl⟩
      rw [mem_filter, qb_mem_canT, qb_lt_colH_iff hmu]
      exact ⟨mem_univ _, h2⟩
  rw [← card_map (Function.Embedding.subtype _), e, Int.card_Ioc]
  have := hmu (qb_le_lastIdx b)
  rw [Int.toNat_of_nonneg (by omega)]
  ring
end Formalism.InvariantFactorPaths.ColumnFamilies
