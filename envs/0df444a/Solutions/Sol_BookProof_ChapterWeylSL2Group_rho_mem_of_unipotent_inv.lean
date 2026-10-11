-- Prove2me | solution 1 for BookProof.ChapterWeylSL2Group.rho_mem_of_unipotent_inv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:40:58.51587+00:00
-- url     : https://prove2.me/submissions/7eb5d316-331e-4680-87f9-8093618dd828

-- Generated from ChapterWeylSL2Group.lean — solution of BookProof.ChapterWeylSL2Group.rho_mem_of_unipotent_inv
import Mathlib
import Definitions.Def_ChapterWeylSL2Group
import Theorems.Thm_BookProof_ChapterWeylSL2Group_exists_factorization
import Definitions.Def_ChapterWeylSl2
open BookProof.ChapterWeylSL2Group




open BookProof.ChapterWeylSl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V} {R : Sl2Rep V} {N : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {W : Submodule ℂ V}
    (hplus : ∀ (t : ℂ), ∀ v ∈ W, rho (uPlus t) v ∈ W)
    (hminus : ∀ (t : ℂ), ∀ v ∈ W, rho (uMinus t) v ∈ W)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℂ) : ∀ v ∈ W, rho g v ∈ W := by

  obtain ⟨x, y, z, w, hg⟩ := exists_factorization g
  intro v hv
  have happ : rho g v = rho (uPlus x) (rho (uMinus y) (rho (uPlus z) (rho (uMinus w) v))) := by
    rw [hg]
    simp [map_mul, Module.End.mul_apply]
  rw [happ]
  exact hplus _ _ (hminus _ _ (hplus _ _ (hminus _ _ hv)))
