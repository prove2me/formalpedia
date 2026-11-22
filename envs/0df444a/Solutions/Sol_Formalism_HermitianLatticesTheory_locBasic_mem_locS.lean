-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locBasic_mem_locS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:00:54.926805+00:00
-- url     : https://prove2.me/submissions/1ad8c428-3609-4e73-bfbb-1b6faee9cbdf

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic

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
theorem _root_.solution {S : Submonoid R} {L : Submodule R W} {x : W} :
    x ∈ locS S L ↔ ∃ s ∈ S, s • x ∈ L := Iff.rfl
end Formalism.HermitianLatticesTheory
