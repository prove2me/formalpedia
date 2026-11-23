-- Prove2me | solution 1 for FRI_domain_foldable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:34:20.099285+00:00
-- url     : https://prove2.me/submissions/0218df88-271c-466f-95f7-d85ab2509133

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
import Theorems.Thm_FRI_prod_tail_split
import Theorems.Thm_P2M_IsFoldable_of_dvd__2b6a9c0f2500
import Theorems.Thm_FRI_domain_foldable_strong

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (i : Fin P.num_foldings) :
    IsFoldable (FRI_domain P i) (P.m i) :=
  (FRI_domain_foldable_strong P i i.isLt.le).of_dvd' <|
    FRI_prod_tail_split P i i.isLt ▸ dvd_mul_right (P.m i) _
