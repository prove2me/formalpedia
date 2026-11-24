-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.symStrip_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:11:45.022441+00:00
-- url     : https://prove2.me/submissions/75be353d-dab7-40ff-8956-7bf281cc886a

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ps_left
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ps_right
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ps_lead
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_gC_torus
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_prod_torus
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mem_strUp
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_SM_diag
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_SM_map
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_SymMat_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_card_D
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_cnt_mc
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_dom_up


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
theorem _root_.solution : CntSym → SymStrip := by
  intro hc n _ b
  refine ⟨fun α x => ((α.1 x : ℕ) : ℤ), qs_ps b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α β h
    exact Subtype.ext (funext fun x => Fin.ext (by have := congrFun h x; simp only at this; exact_mod_cast this))
  · intro k l
    rw [qs_SymMat_eq, qs_SM_map, qs_gC_torus, qs_SM_diag]
    split_ifs with h
    · subst h
      rw [qs_prod_torus]; simp
    · rfl
  · intro mu hmu nu hnu
    exact qs_dom_up hmu (qs_mem_strUp hnu)
  · intro mu hmu nu hnu
    have hs := qs_mem_strUp hnu
    have hnu' := qs_dom_up hmu hs
    ext ⟨J, α⟩ K
    exact (qs_ps_left b hmu hnu' hs J α K).trans (qs_ps_right b hmu hnu' hs J α K).symm
  · intro mu hmu nu hnu
    have hs := qs_mem_strUp hnu
    have hnu' := qs_dom_up hmu hs
    refine ⟨qs_mon (qs_card_D hmu hnu' hs) (qs_mc mu nu), ?_, Or.inl (qs_ps_lead b hmu hnu' hs)⟩
    funext x
    exact qs_cnt_mc hmu hnu' hs x
  · intro mu hmu
    exact hc n mu b hmu
end Formalism.InvariantFactorPaths.ColumnFamilies
