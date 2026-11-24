-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol_ri_peel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:19.185633+00:00
-- url     : https://prove2.me/submissions/53e10ad5-a499-4c60-9fa8-515207805881

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_le_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_locS_mono
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_claimA

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
theorem _root_.solution (S : Submonoid R) {X Y : Submodule R W} (hXY : X ≤ Y)
    (hfin : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0) :
    (Y ⊓ locS S X).toAddSubgroup.relIndex Y.toAddSubgroup =
      (locS S X).toAddSubgroup.relIndex (locS S Y).toAddSubgroup := by
  have e : locS S Y = locS S X ⊔ Y :=
    le_antisymm (by rw [sup_comm]; exact genusCovol_claimA S hfin)
      (sup_le (genusCovol_locS_mono S hXY) (genusCovol_le_locS S Y))
  rw [e, Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left,
    ← AddSubgroup.inf_relIndex_right (locS S X).toAddSubgroup, inf_comm]
  rfl
end Formalism.HermitianLatticesTheory
