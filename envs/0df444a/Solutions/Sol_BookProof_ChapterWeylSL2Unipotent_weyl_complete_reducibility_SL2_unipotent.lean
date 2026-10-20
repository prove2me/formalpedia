-- Prove2me | solution 1 for BookProof.ChapterWeylSL2Unipotent.weyl_complete_reducibility_SL2_unipotent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:21:03.43942+00:00
-- url     : https://prove2.me/submissions/78143a91-552b-4bed-bfca-b5f1cd046162

-- Generated from ChapterWeylSL2Unipotent.lean — theorem BookProof.ChapterWeylSL2Unipotent.weyl_complete_reducibility_SL2_unipotent
import Definitions.Def_ChapterWeylSl2
import Definitions.Def_ChapterWeylSL2Group
import Mathlib
import Theorems.Thm_BookProof_ChapterWeylSL2Group_weyl_complete_reducibility_SL2
import Definitions.Def_ChapterWeylSL2Unipotent
open BookProof.ChapterWeylSL2Unipotent



open BookProof.ChapterWeylSl2 BookProof.ChapterWeylSL2Group
open Polynomial

universe u

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V}
  {E F : Module.End ℂ V} {n : ℕ}
variable (hU : ∀ t : ℂ, rho (uPlus t) = expSum E n t)
  (hL : ∀ t : ℂ, rho (uMinus t) = expSum F n t)
variable {N : ℕ}
open BookProof.ChapterWeylSL2Unipotent in
theorem solution [FiniteDimensional ℂ V]
    (h : IsUnipotentExp rho E F N) {W : Submodule ℂ V}
    (hW : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ v ∈ W, rho g v ∈ W) :
    ∃ U : Submodule ℂ V,
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ v ∈ U, rho g v ∈ U) ∧ IsCompl W U := by 
  have hexp : IsExpOfSl2 rho (sl2OfUnipotent h) N :=
    { two_le := h.two_le
      expE := fun t => h.expE t
      expF := fun t => h.expF t }
  exact BookProof.ChapterWeylSL2Group.weyl_complete_reducibility_SL2 hexp hW
