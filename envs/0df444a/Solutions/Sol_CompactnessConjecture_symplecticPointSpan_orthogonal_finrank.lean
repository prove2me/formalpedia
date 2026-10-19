-- Prove2me | solution 1 for CompactnessConjecture.symplecticPointSpan_orthogonal_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/50418c73-4d26-4cd2-8a7b-8a21ed2912d2

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticPoint_sup_finrank

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {y z : SymplecticPoint K} (hyz : y ≠ z) :
    Module.finrank K
      ((standardSymplecticBilin K).orthogonal
        (y.1 ⊔ z.1)) = 2 := by
  rw [LinearMap.BilinForm.finrank_orthogonal
    (standardSymplecticBilin_nondegenerate K),
    symplecticPoint_sup_finrank K hyz]
  simp [SymplecticVector]
end CompactnessConjecture
