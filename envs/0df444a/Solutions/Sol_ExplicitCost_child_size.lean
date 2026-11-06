-- Prove2me | solution 1 for ExplicitCost.child_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:52:18.882335+00:00
-- url     : https://prove2.me/submissions/2e420776-597f-4b1c-8a0c-8a2e3ae66880

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverPattern
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverCall
import Theorems.Thm_ExplicitCost_child_eq
import Theorems.Thm_ExplicitCost_size_units
import Theorems.Thm_ExplicitCost_pattern_input
import Theorems.Thm_ExplicitCost_rG_ready
import Theorems.Thm_ExplicitCost_rK_ready
import Theorems.Thm_ExplicitCost_size_le_of_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_P2M_ExplicitCost_size_unary__02a080207638
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l y : ℕ} {D : PiecesCounted.Data} {a : Ctx} {f : TableQuery → Option Ans}
namespace ExplicitCost
theorem _root_.solution (hLL : LabelLengthIsL) (hBN : BothNetworks) (hS : Setting ρ c x₀ D) (Bound : Ctx → Prop) (hF : Fits x₀ a f) (hl : cLev a = l + 1) (a' : Ctx) (hC : (spec D c x₀ Bound).Child a f a') :
    size a' ≤ (2 * size (readyOf D x₀ a.1) + 2 * size (nPatterns (readyOf D x₀ a.1)) + size (Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l) + 2 * Levels.Gen.g x₀ l + 6 * (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a)) + 2 * bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) + 12) := by
  obtain ⟨-, y, x, hy, hfind, rfl⟩ := hC
  obtain ⟨-, -, -, hL3⟩ := pattern_input hLL hBN hS hF hl hy
  have hx : x < Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l := by
    have h := List.mem_range.1 (List.mem_of_find?_eq_some hfind)
    rwa [rK_ready D x₀ a.1 hl, rG_ready D x₀ a.1 hl] at h
  rw [child_eq hLL hBN hS hF hl hy x]
  have s1 := size_le_of_le hx.le
  have s2 := size_le_of_le hy.le
  have s3 : size (readyOf D x₀ a.1) = size a.1.1 + (size a.1.2.1 + size a.1.2.2) + (size (unary (2 ^ (3 * (hLev a.1 - 1) + x₀))) + size (unary (Levels.Gen.K x₀ (hLev a.1 - 1)))) + size (listsOf D (cLam a)).1 +
      size (D.fam (cLam a)).d + size (listsOf D (cLam a)).2.1 + size (listsOf D (cLam a)).2.2 := rfl
  have s5 : hLev a.1 - 1 = l := by
    have : hLev a.1 = l + 1 := hl
    omega
  rw [s5, size_units, size_units, size_units, size_unary', size_unary'] at s3
  have s6 : a.1.2.1.length = cLam a := rfl
  have s7 : a.1.2.2.length = cB a := rfl
  have s8 : a.1.1.length = l + 1 := hl
  have hsz : size (((unary l, unary (labelLength (searchInput c (readyOf D x₀ a.1, y))), unary (bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))), some (mkParent D (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (cLam a) (cB a) (direction (readyOf D x₀ a.1, y)) y x)) : Ctx) =
      size (unary l) + (size (unary (labelLength (searchInput c (readyOf D x₀ a.1, y)))) + size (unary (bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))))) + ((size (unary (Levels.Gen.K x₀ l)) + size (unary (Levels.Gen.g x₀ l))) + ((size (unary (cLam a)) + size (unary (cB a))) +
        ((size (listsOf D (cLam a)).1 + (size (listsOf D (cLam a)).2.1 + size (listsOf D (cLam a)).2.2)) + (1 + (size y + size x)))) + 1) := rfl
  rw [hsz, size_unary', size_unary', size_unary', size_unary', size_unary', size_unary', size_unary']
  omega
end ExplicitCost
