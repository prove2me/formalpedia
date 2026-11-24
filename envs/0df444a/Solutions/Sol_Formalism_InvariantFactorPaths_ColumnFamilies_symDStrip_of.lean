-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.symDStrip_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:11:43.523628+00:00
-- url     : https://prove2.me/submissions/9a79f306-7d29-43f4-b05e-7106a8a8f80e

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymDStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_psD_left
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_psD_right
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_psD_lead
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_gI_torus
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_mem_strDown
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_SM_diag
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_SM_map
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_SymDMat_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_card_D
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_cnt_mc
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_dom_down
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_prod_torus


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
theorem _root_.solution : CntSymD → SymDStrip := by
  intro hc n _ b
  refine ⟨fun α x => -((α.1 x : ℕ) : ℤ), qs_psD b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α β h
    exact Subtype.ext (funext fun x => Fin.ext (by
      have := congrFun h x; simp only [neg_inj] at this; exact_mod_cast this))
  · intro k l
    rw [qs_SymDMat_eq, qs_SM_map, qs_gI_torus, qs_SM_diag]
    split_ifs with h
    · subst h
      rw [qs_prod_torus]; simp
    · rfl
  · intro mu hmu nu hnu
    exact qs_dom_down hmu (qs_mem_strDown hnu)
  · intro mu hmu nu hnu
    have hs := qs_mem_strDown hnu
    have hnu' := qs_dom_down hmu hs
    ext ⟨J, α⟩ K
    exact (qs_psD_left b hmu hnu' hs J α K).trans (qs_psD_right b hmu hnu' hs J α K).symm
  · intro mu hmu nu hnu
    have hs := qs_mem_strDown hnu
    have hnu' := qs_dom_down hmu hs
    refine ⟨qs_mon (qs_card_D hnu' hmu hs) (qs_mc nu mu), ?_, Or.inl (qs_psD_lead b hmu hnu' hs)⟩
    funext x
    have := qs_cnt_mc hnu' hmu hs x
    show -((qs_cnt (qs_mc nu mu) x : ℕ) : ℤ) = nu x - mu x
    omega
  · intro mu hmu
    exact hc n mu b hmu
end Formalism.InvariantFactorPaths.ColumnFamilies
