-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.isomAct_mem_locS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:45.686304+00:00
-- url     : https://prove2.me/submissions/b80f4441-33a4-4068-8920-10fe7295e291

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct

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
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R)
    (L : Submodule R W) (x : W) : x ∈ locS S L ↔ ∃ s ∈ S, s • x ∈ L := Iff.rfl
end Formalism.HermitianLatticesTheory
