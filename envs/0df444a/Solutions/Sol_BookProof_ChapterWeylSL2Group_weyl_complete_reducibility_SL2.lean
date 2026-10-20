-- Prove2me | solution 1 for BookProof.ChapterWeylSL2Group.weyl_complete_reducibility_SL2
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:40:59.540086+00:00
-- url     : https://prove2.me/submissions/2cfb339f-6522-4ef0-99ec-b560c8589e46

-- Generated from ChapterWeylSL2Group.lean — solution of BookProof.ChapterWeylSL2Group.weyl_complete_reducibility_SL2
import Mathlib
import Definitions.Def_ChapterWeylSL2Group
import Theorems.Thm_BookProof_ChapterWeylSL2Group_rho_mem_of_isInv
import Theorems.Thm_BookProof_ChapterWeylSL2Group_isInv_of_rho
import Theorems.Thm_BookProof_ChapterWeylSL2Group_rho_mem_of_unipotent_inv
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_weyl_complete_reducibility
import Definitions.Def_ChapterWeylSl2
open BookProof.ChapterWeylSL2Group




open BookProof.ChapterWeylSl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V} {R : Sl2Rep V} {N : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution [FiniteDimensional ℂ V]
    (h : IsExpOfSl2 rho R N) {W : Submodule ℂ V}
    (hW : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ v ∈ W, rho g v ∈ W) :
    ∃ U : Submodule ℂ V,
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ v ∈ U, rho g v ∈ U) ∧ IsCompl W U := by

  have hWinv : R.IsInv W :=
    isInv_of_rho h (fun t => hW (uPlus t)) (fun t => hW (uMinus t))
  obtain ⟨U, hUinv, hcompl⟩ := Sl2Rep.weyl_complete_reducibility R W hWinv
  refine ⟨U, fun g => ?_, hcompl⟩
  exact rho_mem_of_unipotent_inv (fun t => (rho_mem_of_isInv h hUinv t).1)
    (fun t => (rho_mem_of_isInv h hUinv t).2) g
