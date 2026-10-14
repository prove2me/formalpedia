-- Prove2me | solution 1 for BookProof.ChapterWeylSL2Group.pow_mem_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:40:41.948744+00:00
-- url     : https://prove2.me/submissions/db76fa4b-907e-4a2e-bc0d-25a411d67b95

-- Generated from ChapterWeylSL2Group.lean — solution of BookProof.ChapterWeylSL2Group.pow_mem_of_mem
import Mathlib
import Definitions.Def_ChapterWeylSL2Group
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_pow_succ_apply
import Definitions.Def_ChapterWeylSl2
open BookProof.ChapterWeylSL2Group




open BookProof.ChapterWeylSl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V} {R : Sl2Rep V} {N : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {W : Submodule ℂ V} {a : Module.End ℂ V} (ha : ∀ x ∈ W, a x ∈ W)
    {v : V} (hv : v ∈ W) (k : ℕ) : (a ^ k) v ∈ W := by

  induction k with
  | zero => simpa using hv
  | succ k ih => rw [Sl2Rep.pow_succ_apply]; exact ha _ ih
