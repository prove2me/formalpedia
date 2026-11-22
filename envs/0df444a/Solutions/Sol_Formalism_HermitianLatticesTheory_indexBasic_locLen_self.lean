-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.indexBasic_locLen_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:35:48.660827+00:00
-- url     : https://prove2.me/submissions/28357f69-bb72-4c36-ab1b-1f7443558626

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (p : Ideal R) [p.IsPrime] (X : Submodule R W) :
    locLen p X X = 0 := by
  unfold locLen
  rw [Submodule.comap_subtype_self]
  simp
end Formalism.HermitianLatticesTheory
