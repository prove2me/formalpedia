-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_ps_lead
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:15.523211+00:00
-- url     : https://prove2.me/submissions/0c2298c5-be0c-405c-98b1-a502c67bb174

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_can_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_card_D
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ext_can
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ini_erase
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mem_D
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_sg_ini


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
theorem _root_.solution (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip mu nu b) :
    qs_ps b mu nu (canT mu, qs_mon (qs_card_D hmu hnu hs) (qs_mc mu nu)) (canT nu) = 1 := by
  rw [qs_ps, Finset.sum_eq_single (qs_mc mu nu)]
  · rw [if_pos ((qs_can_iff hmu hnu hs _).2 rfl), if_pos]
    swap
    · intro x; rfl
    refine Finset.prod_eq_one fun c _ => ?_
    rw [qs_ext_can hnu, (qs_mem_D hmu hnu c.1).1 c.2]
    have hlt : colH mu c.1 < n := (qs_mc mu nu c).2
    show qs_sg ((qs_ini (colH mu c.1 + 1)).erase ⟨colH mu c.1, hlt⟩) ⟨colH mu c.1, hlt⟩ = 1
    rw [qs_ini_erase, qs_sg_ini]
  · intro m _ hm
    rw [if_neg (fun h => hm ((qs_can_iff hmu hnu hs _).1 h))]
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.InvariantFactorPaths.ColumnFamilies
