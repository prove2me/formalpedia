-- Prove2me | solution 1 for Formalism.LatticeIndexTer.lattice_index_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:06:52.505362+00:00
-- url     : https://prove2.me/submissions/2a99ab6d-207b-4f07-b4f4-e6516d74d4a6

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_GeneralBFactSecondFurther_Imports
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexLength_exists_smul_mem_inf_three
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexLength_len_ne_top
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexLength_idx_eq_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Module
open scoped Pointwise
open LatticeIndexLength
namespace Formalism.LatticeIndexTer
theorem _root_.solution : IdxAdd := by
  intro O K X _ _ _ _ _ _ _ _ _ _ A B C hA hB hC
  let D := A ⊓ B ⊓ C
  have fin : ∀ P : Submodule O X, IsLat O K X P → Module.length O (P ⧸ D.comap P.subtype) ≠ ⊤ := by
    intro P hP
    obtain ⟨d, hd, h⟩ := exists_smul_mem_inf_three (K := K) P A B C hP.1 hA.2 hB.2 hC.2
    exact len_ne_top P D hP.1 d hd h
  have hAB : D ≤ A ⊓ B := inf_le_left
  have hBC : D ≤ B ⊓ C := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hAC : D ≤ A ⊓ C := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  rw [idx_eq_sub A C D hAC (fin A hA) (fin C hC), idx_eq_sub A B D hAB (fin A hA) (fin B hB),
    idx_eq_sub B C D hBC (fin B hB) (fin C hC)]
  ring
end Formalism.LatticeIndexTer
