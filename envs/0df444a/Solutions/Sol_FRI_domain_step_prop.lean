-- Prove2me | solution 1 for FRI_domain_step_prop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:19:45.920396+00:00
-- url     : https://prove2.me/submissions/da85baab-a8a2-42d4-9e5c-2dc3b932cc53

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F] (P : FRIParameters F)
    (i : ℕ) (h : i < P.num_foldings) (x : F) (hx : x ∈ FRI_domain P i) :
    x ^ (P.m ⟨i, h⟩) ∈ FRI_domain P (i + 1) := by
  simp only [FRI_domain, h, ↓reduceDIte, pow_domain]
  grind
