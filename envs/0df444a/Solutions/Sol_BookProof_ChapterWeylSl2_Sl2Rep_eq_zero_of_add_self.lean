-- Prove2me | solution 1 for BookProof.ChapterWeylSl2.Sl2Rep.eq_zero_of_add_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:59:44.908994+00:00
-- url     : https://prove2.me/submissions/d9a48cfd-9abf-4bb7-9a64-8b05706e30e2

-- Generated from ChapterWeylSl2.lean — solution of BookProof.ChapterWeylSl2.Sl2Rep.eq_zero_of_add_self
import Mathlib
import Definitions.Def_ChapterWeylSl2
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2.Sl2Rep




universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable (R : Sl2Rep V)
variable {R}
variable {R : Sl2Rep V}

set_option maxHeartbeats 1000000 in
theorem solution {x : V} (h : x + x = 0) : x = 0 := by

  have h2 : (2 : ℂ) • x = 0 := by rw [two_smul]; exact h
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
