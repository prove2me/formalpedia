-- Prove2me | solution 1 for BookProof.ChapterWeylSl2.Sl2Rep.isInv_ker_cas
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:59:49.954166+00:00
-- url     : https://prove2.me/submissions/da0d701c-2171-4777-8b78-6388022abdc6

-- Generated from ChapterWeylSl2.lean — solution of BookProof.ChapterWeylSl2.Sl2Rep.isInv_ker_cas
import Mathlib
import Definitions.Def_ChapterWeylSl2
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_cas_comm_apply_E
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_cas_comm_apply_F
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_cas_comm_apply_H
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterGleasonPureMixed
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2.Sl2Rep




universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable (R : Sl2Rep V)
variable {R}
variable {R : Sl2Rep V}

set_option maxHeartbeats 1000000 in
theorem solution (R : Sl2Rep V) : R.IsInv (LinearMap.ker R.cas) := by

  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩ <;>
    rw [LinearMap.mem_ker] at hx ⊢
  · rw [cas_comm_apply_E, hx, map_zero]
  · rw [cas_comm_apply_F, hx, map_zero]
  · rw [cas_comm_apply_H, hx, map_zero]
