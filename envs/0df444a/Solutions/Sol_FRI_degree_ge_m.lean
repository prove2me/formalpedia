-- Prove2me | solution 1 for FRI_degree_ge_m
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:36:52.369557+00:00
-- url     : https://prove2.me/submissions/69faf088-af95-43a3-8a6d-89d04d48c861

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
import Theorems.Thm_m_dvd_FRI_degree
import Theorems.Thm_FRI_degree_pos

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (i : Fin P.num_foldings) :
    FRI_degree P i ≥ P.m i :=
  Nat.le_of_dvd (FRI_degree_pos P i i.isLt.le) (m_dvd_FRI_degree P i)
