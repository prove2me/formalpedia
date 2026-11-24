-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol_claimA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:55.316509+00:00
-- url     : https://prove2.me/submissions/07c0293b-c258-458d-ad62-4de526a8bd34

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_pigeon

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (S : Submonoid R) {X Y : Submodule R W}
    (hfin : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0) :
    locS S Y ≤ Y ⊔ locS S X := by
  rintro y ⟨s, hs, hsy⟩
  obtain ⟨m, k, hk, hmk⟩ := genusCovol_pigeon hfin s hsy
  have hb : s ^ k • y ∈ Y := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ, mul_smul]
    exact Y.smul_mem _ hsy
  have hr : y - s ^ k • y ∈ locS S X := by
    refine ⟨s ^ (m + 1), S.pow_mem hs _, ?_⟩
    have e : s ^ (m + 1) • (y - s ^ k • y) = s ^ m • (s • y) - s ^ (m + k) • (s • y) := by
      rw [smul_sub, smul_smul, smul_smul, smul_smul, ← pow_succ, ← pow_succ, ← pow_add]
      congr 2
      ring
    rw [e]
    exact hmk
  have : y = s ^ k • y + (y - s ^ k • y) := by abel
  rw [this]
  exact Submodule.add_mem_sup hb hr
end Formalism.HermitianLatticesTheory
