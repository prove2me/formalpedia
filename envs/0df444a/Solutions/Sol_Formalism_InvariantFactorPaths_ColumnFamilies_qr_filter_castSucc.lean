-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_filter_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:12.197136+00:00
-- url     : https://prove2.me/submissions/68b2a963-3743-4222-8cd6-9bca4256c2b0

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_mem_castSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {m : ℕ} (e : Prop) [Decidable e] (S : Finset (Fin m))
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (t : Fin m) :
    ((qr_ext e S).filter (· ≤ t.castSucc)) = (S.filter (· ≤ t)).map Fin.castSuccEmb := by
  ext x
  induction x using Fin.lastCases with
  | last =>
    simp only [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨_, h⟩; exact absurd h (not_le.2 (Fin.castSucc_lt_last t))
    · rintro ⟨a, _, h⟩; exact absurd h (Fin.castSucc_lt_last a).ne
  | cast a =>
    simp only [Finset.mem_filter, qr_mem_castSucc, Finset.mem_map, Fin.castSuccEmb_apply, Fin.castSucc_inj,
      exists_eq_right, Fin.castSucc_le_castSucc_iff]
end Formalism.InvariantFactorPaths.ColumnFamilies
