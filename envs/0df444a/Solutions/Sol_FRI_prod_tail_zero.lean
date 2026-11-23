-- Prove2me | solution 1 for FRI_prod_tail_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:18:13.269561+00:00
-- url     : https://prove2.me/submissions/bf0206dd-ebf0-4240-9966-0a4a6207ba5f

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F) :
    FRI_prod_tail P 0 = ∏ j, P.m j := by
  simp [FRI_prod_tail]
