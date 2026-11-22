-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locBasic_locS_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:08:13.873399+00:00
-- url     : https://prove2.me/submissions/fb9ebf08-1ea9-4101-bd3b-2536149046c1

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
theorem _root_.solution (S : Submonoid R) {L M : Submodule R W} (h : L ≤ M) :
    locS S L ≤ locS S M := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp hx
  exact locBasic_mem_locS.mpr ⟨s, hs, h hsx⟩
end Formalism.HermitianLatticesTheory
