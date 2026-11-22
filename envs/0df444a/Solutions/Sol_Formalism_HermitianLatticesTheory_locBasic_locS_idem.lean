-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locBasic_locS_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:36:23.374473+00:00
-- url     : https://prove2.me/submissions/83a482c5-8633-4796-84b0-68f28480445b

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (S : Submonoid R) (L : Submodule R W) :
    locS S (locS S L) = locS S L := by
  refine le_antisymm ?_ (locBasic_le_locS S _)
  intro x hx
  obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp hx
  obtain ⟨t, ht, htx⟩ := locBasic_mem_locS.mp hsx
  exact locBasic_mem_locS.mpr ⟨t * s, S.mul_mem ht hs, by rwa [mul_smul]⟩
end Formalism.HermitianLatticesTheory
