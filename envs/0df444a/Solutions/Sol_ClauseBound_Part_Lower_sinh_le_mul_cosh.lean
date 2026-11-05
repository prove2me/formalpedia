-- Prove2me | solution 1 for ClauseBound.Part.Lower.sinh_le_mul_cosh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:28:38.518943+00:00
-- url     : https://prove2.me/submissions/d39d75a6-5756-44d1-aa3b-a933985f47a2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower
namespace ClauseBound.Part.Lower
theorem _root_.solution {z : ℝ} (hz : 0 ≤ z) : Real.sinh z ≤ z * Real.cosh z := by
  have h := (convex_Icc (0 : ℝ) z).image_sub_le_mul_sub_of_deriv_le (f := Real.sinh) (C := Real.cosh z)
    Real.continuous_sinh.continuousOn Real.differentiable_sinh.differentiableOn
    (fun x hx => by
      rw [interior_Icc] at hx
      rw [Real.deriv_sinh, Real.cosh_le_cosh, abs_of_pos hx.1, abs_of_nonneg hz]
      exact hx.2.le) 0 (Set.left_mem_Icc.2 hz) z (Set.right_mem_Icc.2 hz) hz
  rw [Real.sinh_zero] at h
  linarith
end ClauseBound.Part.Lower
