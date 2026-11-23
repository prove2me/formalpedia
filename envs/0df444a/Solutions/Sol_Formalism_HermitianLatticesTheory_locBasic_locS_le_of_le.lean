-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locBasic_locS_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:20.18785+00:00
-- url     : https://prove2.me/submissions/78e3463d-fe35-4c0d-b1e0-4dab835a725d

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS

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
theorem _root_.solution {S T : Submonoid R} (hST : S ≤ T) (L : Submodule R W) :
    locS S L ≤ locS T L := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp hx
  exact locBasic_mem_locS.mpr ⟨s, hST hs, hsx⟩
end Formalism.HermitianLatticesTheory
