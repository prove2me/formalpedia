-- Prove2me | solution 1 for FRI_degree_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:33:32.822922+00:00
-- url     : https://prove2.me/submissions/a5953cf7-4e40-4a78-b48c-342617ed44d5

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
import Theorems.Thm_m_dvd_FRI_degree
import Theorems.Thm_FRI_degree_succ_eq


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (i : ℕ) (hi : i ≤ P.num_foldings) :
    0 < FRI_degree P i := by
  induction i with
  | zero => exact P.h_d0_pos
  | succ i ih =>
    have hi' := Nat.lt_of_succ_le hi
    exact (FRI_degree_succ_eq P i hi') ▸
      Nat.div_pos (Nat.le_of_dvd (ih hi'.le) (m_dvd_FRI_degree P ⟨i, hi'⟩)) (P.h_m_pos ⟨i, hi'⟩)
