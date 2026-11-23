-- Prove2me | solution 1 for FRI_degree_succ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:54:13.500811+00:00
-- url     : https://prove2.me/submissions/d0222c1f-40f4-4527-888c-b13a5ca5e308

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (i : ℕ) (h : i < P.num_foldings) :
    FRI_degree P (i + 1) = FRI_degree P i / P.m ⟨i, h⟩ :=
  dif_pos h
