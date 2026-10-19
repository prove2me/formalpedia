-- Prove2me | solution 1 for CompactnessConjecture.proposedFamilyFree_no_jTemplate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/50bc47cc-6f5d-4a39-adeb-faebff6a97b1

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_jQuotient_mem_proposedFamily
import Theorems.Thm_CompactnessConjecture_kernelNormalForm_jAdmissible

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host)
    (hom : jTemplate →g host)
    (hcolor : ∀ u v, hom u = hom v → jColor u = jColor v)
    (hbase : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v}) : False := by
  let f := kernelNormalForm hom
  have hf : JAdmissible f :=
    kernelNormalForm_jAdmissible hom hcolor hbase hcopies
  have hmember := jQuotient_mem_proposedFamily hf
  apply hfree _ hmember
  exact ⟨encodeFiniteGraphCopy
    (quotientGraph jTemplate f) host
    (kernelQuotientCopy jTemplate host hom)⟩
end CompactnessConjecture
