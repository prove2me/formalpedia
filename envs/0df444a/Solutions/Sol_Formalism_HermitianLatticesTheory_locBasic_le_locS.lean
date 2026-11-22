-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locBasic_le_locS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:08:10.71891+00:00
-- url     : https://prove2.me/submissions/8f609ef7-3d15-45dc-9bdf-f4788421b2e0

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
theorem _root_.solution (S : Submonoid R) (L : Submodule R W) : L ≤ locS S L := by
  intro x hx
  exact locBasic_mem_locS.mpr ⟨1, S.one_mem, by rwa [one_smul]⟩
end Formalism.HermitianLatticesTheory
