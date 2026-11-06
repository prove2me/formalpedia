-- Prove2me | solution 1 for ExplicitCost.solver_room
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:35:36.572428+00:00
-- url     : https://prove2.me/submissions/5e2197c9-1f61-49d9-b03d-32af33eee803

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverCall
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverRoom
import Theorems.Thm_ExplicitCost_pw_add
import Theorems.Thm_ExplicitCost_pw_mul
import Theorems.Thm_ExplicitCost_pw_num
import Theorems.Thm_ExplicitCost_pw_up
import Theorems.Thm_ExplicitCost_room_arith
import Theorems.Thm_ExplicitCost_size_of_le_two_pow
import Theorems.Thm_ExplicitCost_pow_le_two_pow
import Theorems.Thm_ExplicitCost_size_of_abs_lt
import Theorems.Thm_ExplicitCost_size_of_elements
import Theorems.Thm_ClauseBound_Gen_Pick_K_le_g
import Theorems.Thm_ExplicitCost_K_le_g
import Theorems.Thm_ExplicitCost_nPatterns_ready
import Theorems.Thm_ExplicitCost_size_le_of_le
import Theorems.Thm_ExplicitCost_size_le_succ
import Theorems.Thm_ExplicitCost_size_units
import Theorems.Thm_ExplicitCost_two_le_K
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_ExplicitCost_size_unary__02a080207638
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (hFew : PatternsFew) (hCr : CrudeBounds) (c Cn Cg : ℕ) : ∃ C : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (a : Ctx) (l : ℕ), 1 ≤ cLam a → 1 ≤ cB a → cLev a = l + 1 →
    20 * (Cn * Levels.Gen.g x₀ l + size (readyOf D x₀ a.1) + size (nPatterns (readyOf D x₀ a.1)) + size (nPatterns (readyOf D x₀ a.1) * 2 ^ (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) + (Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + size ((1 : ℕ), 2 ^ (l + 5))) ^ Cg + (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + size (Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l) + Levels.Gen.g x₀ l + Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) + 4) ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C ∧
    Cg + 3 ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C ∧ 2 * l + 7 + 2 * #(D.fam (cLam a)).I ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C := by
  obtain ⟨C, hC⟩ := room_arith c Cn Cg
  refine ⟨C + (Cg + 3) + (2 + 1 + 7 + 1 + (2 + c) + 1), fun ρ x₀ D hS a l hlam hB hl => ?_⟩
  have hx := hS.x₀_ge
  have hK2 := two_le_K (by omega : 1 ≤ x₀) l
  have hKg := K_le_g x₀ l
  have hp : 2 ^ (3 * l + x₀) ≤ Levels.Gen.g x₀ l := Nat.le_mul_of_pos_right _ (by omega)
  have hlg : l ≤ Levels.Gen.g x₀ l := (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))).trans hp
  have hgg : Levels.Gen.g x₀ l * Levels.Gen.g x₀ l ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) := by
    calc Levels.Gen.g x₀ l * Levels.Gen.g x₀ l = Levels.Gen.g x₀ l ^ 2 * 1 := by ring
      _ ≤ Levels.Gen.g x₀ l ^ 2 * (cLam a + cB a) := Nat.mul_le_mul_left _ (by omega)
  have h4 : 2 * 2 ≤ Levels.Gen.g x₀ l * Levels.Gen.g x₀ l := Nat.mul_le_mul (by omega) (by omega)
  have hX : 2 ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) := by omega
  have h2lam : 2 * cLam a ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) := by
    calc 2 * cLam a ≤ Levels.Gen.g x₀ l ^ 2 * cLam a := Nat.mul_le_mul_right _ (by rw [sq]; omega)
      _ ≤ Levels.Gen.g x₀ l ^ 2 * (cLam a + cB a) := Nat.mul_le_mul_left _ (by omega)
  have hBX : cB a ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) := by
    calc cB a ≤ Levels.Gen.g x₀ l ^ 2 * cB a := Nat.le_mul_of_pos_left _ (by rw [sq]; omega)
      _ ≤ Levels.Gen.g x₀ l ^ 2 * (cLam a + cB a) := Nat.mul_le_mul_left _ (by omega)
  have hm : (2 * cLam a) ^ c ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ c := Nat.pow_le_pow_left h2lam c
  have hn : #(D.fam (cLam a)).I ≤ (2 * cLam a) ^ c := hS.is.card _ hlam
  obtain ⟨hB', hA, -⟩ := hCr c x₀ l (cLam a) (cB a) 0 hx hlam hB (Nat.zero_le _)
  have hXX : Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ 1 := (pow_one _).ge
  refine ⟨?_, pw_up hX (pw_num hX (Cg + 3)) (by omega), pw_up hX (pw_add hX (pw_add hX (pw_mul (pw_num hX 2) ((hlg.trans ((Nat.le_mul_self _).trans hgg)).trans hXX)) (pw_num hX 7)) (pw_mul (pw_num hX 2) (hn.trans hm))) (by omega)⟩
  refine le_trans ?_ (pw_up hX (hC _ _ _ _ l _ _ _ _ _ hX hgg hKg hp hlg h2lam hBX hm hn hA) (by omega))
  refine Nat.mul_le_mul_left 20 ?_
  -- what the solver holds
  have s3 : size (readyOf D x₀ a.1) = size a.1.1 + (size a.1.2.1 + size a.1.2.2) + (size (unary (2 ^ (3 * (hLev a.1 - 1) + x₀))) + size (unary (Levels.Gen.K x₀ (hLev a.1 - 1)))) + size (listsOf D (cLam a)).1 +
      size (D.fam (cLam a)).d + size (listsOf D (cLam a)).2.1 + size (listsOf D (cLam a)).2.2 := rfl
  have s5 : hLev a.1 - 1 = l := by
    have : hLev a.1 = l + 1 := hl
    omega
  rw [s5, size_units, size_units, size_units, size_unary', size_unary'] at s3
  have s6 : a.1.2.1.length = cLam a := rfl
  have s7 : a.1.2.2.length = cB a := rfl
  have s8 : a.1.1.length = l + 1 := hl
  have sI : size (listsOf D (cLam a)).1 ≤ #(D.fam (cLam a)).I * ((2 * cLam a) ^ c + 2) + 1 := by
    have h := size_of_elements ((D.fam (cLam a)).I.sort) ((2 * cLam a) ^ c + 2) fun i hi => by
      have := size_of_abs_lt (hS.is.size_I _ hlam i ((Finset.mem_sort _).1 hi))
      omega
    rwa [Finset.length_sort] at h
  have sd : size (D.fam (cLam a)).d ≤ (2 * cLam a) ^ c + 1 := size_of_abs_lt (by
    rw [abs_of_pos (by have := hS.is.d_pos _ hlam; omega)]
    exact hS.is.size_d _ hlam)
  have sc : ∀ tr : Bool, size (((D.fam (cLam a)).I.sort).map fun i => D.cap (cLam a) tr i) ≤ #(D.fam (cLam a)).I * (2 * cLam a + 2) + 1 := fun tr => by
    have h := size_of_elements (((D.fam (cLam a)).I.sort).map fun i => D.cap (cLam a) tr i) (2 * cLam a + 2) fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      have h1 := size_le_of_le (hS.short (cLam a) tr i)
      have h2 := size_le_succ (2 * cLam a)
      omega
    rwa [List.length_map, Finset.length_sort] at h
  have sc0 : size (listsOf D (cLam a)).2.1 ≤ #(D.fam (cLam a)).I * (2 * cLam a + 2) + 1 := sc false
  have sc1 : size (listsOf D (cLam a)).2.2 ≤ #(D.fam (cLam a)).I * (2 * cLam a + 2) + 1 := sc true
  -- the number of patterns
  have hnP : nPatterns (readyOf D x₀ a.1) ≤ 2 ^ (Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) * (c * Levels.Gen.g x₀ l ^ 4)) := by
    rw [nPatterns_ready D x₀ a.1 hl]
    exact ((Nat.le_self_pow (by norm_num) _).trans (hFew ρ c x₀ D hS (Levels.Gen.g x₀ l) (cLam a) (cB a) (by omega) hlam hB).2).trans (pow_le_two_pow _ _)
  have sP := size_of_le_two_pow hnP
  have hgP : Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) ≤ (Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  have hgB : Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) ≤ Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))
  have sV : size (nPatterns (readyOf D x₀ a.1) * 2 ^ (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) * (c * Levels.Gen.g x₀ l ^ 4) + ((Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) + Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))))) + 2 := size_of_le_two_pow
    ((Nat.mul_le_mul hnP (Nat.pow_le_pow_right (by norm_num) (by omega))).trans (pow_add 2 (Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) * (c * Levels.Gen.g x₀ l ^ 4)) ((Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) + Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))))).ge)
  have sK : size (Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l) ≤ Levels.Gen.K x₀ l * Levels.Gen.g x₀ l + 2 := size_of_le_two_pow (pow_le_two_pow _ _)
  have sz : size ((1 : ℕ), 2 ^ (l + 5)) ≤ l + 9 := by
    have h1 : size ((1 : ℕ), 2 ^ (l + 5)) = size (1 : ℕ) + size (2 ^ (l + 5)) := rfl
    have h2 := size_le_succ 1
    have h3 := size_of_le_two_pow (le_refl (2 ^ (l + 5)))
    omega
  have sg : (Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + size ((1 : ℕ), 2 ^ (l + 5))) ^ Cg ≤ ((Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) + (l + 9)) ^ Cg := Nat.pow_le_pow_left (by omega) _
  have hB2 : Levels.Gen.g x₀ l ^ 2 * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) ≤ Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) := by rw [sq]; exact hgB
  omega
end ExplicitCost
