-- Prove2me | solution 1 for FRI_State_independent_of_s
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:11:47.446113+00:00
-- url     : https://prove2.me/submissions/af74836c-f989-4256-9bee-beff92d94934

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (f : (i : Fin P.num_foldings) → FRI_domain P i.val.succ → F)
    (alpha : Fin P.num_foldings → F)
    (s1 s2 : Fin P.q_rep → P.D_0)
    (i : ℕ) (h : i ≤ P.num_foldings) :
    FRI_State P f_0 bound { f := f, alpha := alpha, s := s1 } i ↔
    FRI_State P f_0 bound { f := f, alpha := alpha, s := s2 } i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [FRI_State]
    split_ifs with h_lt
    · exact (ih (Nat.le_of_succ_le h)).or Iff.rfl
    · grind
    · grind
