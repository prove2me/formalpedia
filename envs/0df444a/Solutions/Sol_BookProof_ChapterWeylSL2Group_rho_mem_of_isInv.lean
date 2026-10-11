-- Prove2me | solution 1 for BookProof.ChapterWeylSL2Group.rho_mem_of_isInv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:40:42.922458+00:00
-- url     : https://prove2.me/submissions/a30c52ba-dc12-4b7b-b20a-13e2580d0ea7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterWeylSL2Group.lean — solution of BookProof.ChapterWeylSL2Group.rho_mem_of_isInv
import Mathlib
import Definitions.Def_ChapterWeylSL2Group
import Theorems.Thm_BookProof_ChapterWeylSL2Group_pow_mem_of_mem
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterGleasonPureMixed
import Definitions.Def_ChapterWeylSl2
open BookProof.ChapterWeylSL2Group




open BookProof.ChapterWeylSl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V} {R : Sl2Rep V} {N : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (h : IsExpOfSl2 rho R N) {W : Submodule ℂ V} (hW : R.IsInv W) :
    ∀ t : ℂ, (∀ v ∈ W, rho (uPlus t) v ∈ W) ∧ (∀ v ∈ W, rho (uMinus t) v ∈ W) := by

  intro t
  constructor
  · intro v hv
    rw [h.expE t]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (pow_mem_of_mem hW.1 hv k)
  · intro v hv
    rw [h.expF t]
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (pow_mem_of_mem hW.2.1 hv k)
