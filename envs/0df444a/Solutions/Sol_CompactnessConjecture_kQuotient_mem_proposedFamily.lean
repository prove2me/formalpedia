-- Prove2me | solution 1 for CompactnessConjecture.kQuotient_mem_proposedFamily
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/70d952a0-4d97-41e7-9181-3d683298868c

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamily_mem_iff

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    encodeFiniteGraph (quotientGraph kTemplate f) ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inr ⟨f, hf, rfl⟩)
end CompactnessConjecture
