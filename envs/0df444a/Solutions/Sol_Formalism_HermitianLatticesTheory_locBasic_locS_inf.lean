-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locBasic_locS_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:44:20.760802+00:00
-- url     : https://prove2.me/submissions/7af029f3-4b54-419e-ace9-50dc4ece7b24

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono

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
theorem _root_.solution (S : Submonoid R) (L M : Submodule R W) :
    locS S (L ⊓ M) = locS S L ⊓ locS S M := by
  apply le_antisymm
  · exact le_inf (locBasic_locS_mono S inf_le_left) (locBasic_locS_mono S inf_le_right)
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp (Submodule.mem_inf.mp hx).1
    obtain ⟨t, ht, htx⟩ := locBasic_mem_locS.mp (Submodule.mem_inf.mp hx).2
    refine locBasic_mem_locS.mpr ⟨s * t, S.mul_mem hs ht, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩
    · rw [mul_comm, mul_smul]
      exact L.smul_mem t hsx
    · rw [mul_smul]
      exact M.smul_mem s htx
end Formalism.HermitianLatticesTheory
