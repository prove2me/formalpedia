-- Prove2me | solution 1 for CompactnessConjecture.proposedFamilyFree_no_kTemplate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/81db0162-0fd1-413c-9295-b6a1e027a9ed

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_kQuotient_mem_proposedFamily
import Theorems.Thm_CompactnessConjecture_kernelNormalForm_kAdmissible

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host)
    (hom : kTemplate →g host)
    (hcolor : ∀ u v, hom u = hom v → kColor u = kColor v)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = copy}) : False := by
  let f := kernelNormalForm hom
  have hf : KAdmissible f :=
    kernelNormalForm_kAdmissible hom hcolor hcopies
  have hmember := kQuotient_mem_proposedFamily hf
  apply hfree _ hmember
  exact ⟨encodeFiniteGraphCopy
    (quotientGraph kTemplate f) host
    (kernelQuotientCopy kTemplate host hom)⟩
end CompactnessConjecture
