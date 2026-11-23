-- Prove2me | solution 1 for FRI_State_monotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:22:09.979823+00:00
-- url     : https://prove2.me/submissions/9b87ee17-a544-4caa-ba97-077287356e2c

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) (i j : ℕ) (h : i ≤ j) :
    FRI_State P f_0 bound T i → FRI_State P f_0 bound T j := by
  induction j with
  | zero => exact (Nat.le_zero.mp h) ▸ id
  | succ j ih =>
    cases h with
    | refl => exact id
    | step a =>
      intro h
      simp only [FRI_State]
      split_ifs
      · left; exact ih a h
      · left; exact ih a h
      · exact ih a h
