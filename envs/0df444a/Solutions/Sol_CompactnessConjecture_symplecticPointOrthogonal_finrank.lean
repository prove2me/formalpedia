-- Prove2me | solution 1 for CompactnessConjecture.symplecticPointOrthogonal_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/a816e30a-a7e7-4457-bc48-5269b507dccc

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (p : SymplecticPoint K) :
    Module.finrank K (SymplecticPointOrthogonal K p) = 3 := by
  change Module.finrank K
    ((standardSymplecticBilin K).orthogonal p.1) = 3
  rw [LinearMap.BilinForm.finrank_orthogonal
    (standardSymplecticBilin_nondegenerate K), p.2]
  simp [SymplecticVector]
end CompactnessConjecture
