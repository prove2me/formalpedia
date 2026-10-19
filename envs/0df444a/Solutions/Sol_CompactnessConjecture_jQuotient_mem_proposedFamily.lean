-- Prove2me | solution 1 for CompactnessConjecture.jQuotient_mem_proposedFamily
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/695de4dc-5768-4020-86e4-8fecd952dca5

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamily_mem_iff

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    encodeFiniteGraph (quotientGraph jTemplate f) ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inl (.inr ⟨f, hf, rfl⟩))
end CompactnessConjecture
