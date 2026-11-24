-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_psD_lead
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:15.298774+00:00
-- url     : https://prove2.me/submissions/7fde13f2-950c-402f-93c3-3a0a6d5984d5

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymDStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_can_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_card_D
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ext_can
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_rem_iff_add
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
theorem _root_.solution (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip nu mu b) :
    qs_psD b mu nu (canT mu, qs_mon (qs_card_D hnu hmu hs) (qs_mc nu mu)) (canT nu) = 1 := by
  have hiff : ∀ m : ↥(qs_D nu mu) → Fin n, ((∀ c : ↥(qs_D nu mu), m c ∉ qs_ext nu (canT nu) c.1) ∧
      qs_ext mu (canT mu) = qs_add (qs_D nu mu) (qs_ext nu (canT nu)) m) ↔ m = qs_mc nu mu := fun m =>
    (qs_rem_iff_add _ _ _ m).symm.trans (qs_can_iff hnu hmu hs m)
  rw [qs_psD, Finset.sum_eq_single (qs_mc nu mu)]
  · rw [if_pos ((hiff _).2 rfl), if_pos]
    swap
    · intro x; rfl
    refine Finset.prod_eq_one fun c _ => ?_
    rw [qs_ext_can hnu]
    exact qs_sg_ini _ _
  · intro m _ hm
    rw [if_neg (fun h => hm ((hiff _).1 h))]
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.InvariantFactorPaths.ColumnFamilies
