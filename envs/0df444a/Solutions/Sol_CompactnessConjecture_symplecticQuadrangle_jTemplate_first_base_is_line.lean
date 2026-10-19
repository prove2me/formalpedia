-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_jTemplate_first_base_is_line
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/35773c0a-5334-425b-b559-51e531fcd3d1

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_no_point_jTemplate_of_first_base

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v}) :
    ∃ L : SymplecticLine K,
      hom (.inl (.inl (0 : Fin 4))) = .inr L := by
  cases h : hom (.inl (.inl (0 : Fin 4))) with
  | inl p =>
      exact False.elim
        (symplecticQuadrangle_no_point_jTemplate_of_first_base K
          hom hbase_inj hcopies ⟨p, h⟩)
  | inr L => exact ⟨L, rfl⟩
end CompactnessConjecture
