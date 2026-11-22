-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_card_D
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:30.209617+00:00
-- url     : https://prove2.me/submissions/c8f66318-f50b-43fc-8a5f-071a4452461d

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_cnt_mc

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
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b) :
    Fintype.card ↥(qs_D lam kap) = b := by
  have h1 := qs_sum_cnt (qs_mc lam kap)
  have h2 : ((∑ x, qs_cnt (qs_mc lam kap) x : ℕ) : ℤ) = (b : ℤ) := by
    rw [← hs.2.2]; push_cast
    exact Finset.sum_congr rfl fun x _ => qs_cnt_mc hl hk hs x
  rw [h1] at h2
  exact_mod_cast h2
end Formalism.InvariantFactorPaths.ColumnFamilies
