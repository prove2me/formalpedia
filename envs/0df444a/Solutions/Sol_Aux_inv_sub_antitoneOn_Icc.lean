-- Prove2me | solution 1 for Aux.inv_sub_antitoneOn_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T16:12:00.594862+00:00
-- url     : https://prove2.me/submissions/d94ed54e-5b5e-4234-9775-74014190edad

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Definitions.Def_Sieve_AuxResults_defs
import Theorems.Thm_Aux_inv_sub_antitoneOn_gt

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset

open ArithmeticFunction.IsMultiplicative

variable {R : Type*}

open Aux

open Aux in
theorem solution
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : R) (ha : c < a) :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact inv_sub_antitoneOn_gt c |>.mono <| (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

-- Lemma 3.1 in Heath-Brown's notes
