-- Prove2me | solution 1 for BookProof.ChapterWeylSl2.Sl2Rep.cas_highestWeight
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:51:34.479633+00:00
-- url     : https://prove2.me/submissions/a81f1382-d79c-40cb-b515-c31148cc053a

-- Generated from ChapterWeylSl2.lean — solution of BookProof.ChapterWeylSl2.Sl2Rep.cas_highestWeight
import Mathlib
import Definitions.Def_ChapterWeylSl2
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_apply_E_F
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
theorem solution {R : Sl2Rep V} {w : V} {lam : ℂ} (hE : R.E w = 0)
    (h : R.H w = lam • w) : R.cas w = (lam ^ 2 + 2 * lam) • w := by

  have h1 : (R.E * R.F) w = lam • w := by
    rw [Module.End.mul_apply, apply_E_F, hE, map_zero, h, zero_add]
  have h2 : (R.F * R.E) w = 0 := by rw [Module.End.mul_apply, hE, map_zero]
  have h3 : (R.H * R.H) w = (lam ^ 2) • w := by
    rw [Module.End.mul_apply, h, map_smul, h, smul_smul, sq]
  simp only [cas, LinearMap.add_apply, two_nsmul, h1, h2, h3]
  module
