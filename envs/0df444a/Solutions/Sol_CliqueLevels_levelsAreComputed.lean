-- Prove2me | solution 1 for CliqueLevels.levelsAreComputed
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:51:00.336869+00:00
-- url     : https://prove2.me/submissions/92872235-030e-4f1e-9fec-c9f7b182a8bc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_GenLevelsDefs
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Closure_Fold
import Definitions.Def_ToTuring_Closure_Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_CountedToPadded_GenLevels
import Theorems.Thm_Groundwork_PolyT_len_mul_le
import Theorems.Thm_Groundwork_PolyT_unary_min_length
import Theorems.Thm_Groundwork_len_units

attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.pow_const
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_inl__78f4b62d65a1
attribute [local fun_prop] P2M_Groundwork_PolyT_inr__53ca1f30b2d3
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_some__e6a32bd6af45

set_option autoImplicit false
section
section
open CliqueLevels
open Groundwork Printed Proof

namespace CliqueLevels.Proof

open Groundwork Printed

/-- K_ℓ ≥ 1. -/
theorem K_pos (x₀ l : ℕ) : 0 < Levels.Gen.K x₀ l := by
  cases l with
  | zero => exact Nat.two_pow_pos x₀
  | succ l => exact pow_pos (Nat.mul_pos (Nat.two_pow_pos _) (K_pos x₀ l)) 2

/-- K_ℓ ≤ K_{ℓ+1}. -/
theorem K_le_succ (x₀ l : ℕ) : Levels.Gen.K x₀ l ≤ Levels.Gen.K x₀ (l + 1) := by
  have h1 : 0 < 2 ^ (3 * l + x₀) := Nat.two_pow_pos _
  have h2 := K_pos x₀ l
  calc Levels.Gen.K x₀ l ≤ 2 ^ (3 * l + x₀) * Levels.Gen.K x₀ l := Nat.le_mul_of_pos_left _ h1
    _ ≤ (2 ^ (3 * l + x₀) * Levels.Gen.K x₀ l) ^ 2 := Nat.le_self_pow (by norm_num) _

/-- The state after ℓ rounds. -/
theorem fold_eq (x₀ b l : ℕ) : (unary l).foldl (fun s _ => roundUnder b s) (if 2 ^ x₀ ≤ b then some (2 ^ x₀, 2 ^ x₀) else none) =
    if Levels.Gen.K x₀ l ≤ b then some (2 ^ (3 * l + x₀), Levels.Gen.K x₀ l) else none := by
  induction l with
  | zero =>
    change (if 2 ^ x₀ ≤ b then some (2 ^ x₀, 2 ^ x₀) else none) = if 2 ^ x₀ ≤ b then some (2 ^ (3 * 0 + x₀), 2 ^ x₀) else none
    rw [Nat.mul_zero, Nat.zero_add]
  | succ l ih =>
    have e : unary (l + 1) = unary l ++ [()] := List.replicate_succ'
    rw [e, List.foldl_append, ih]
    change roundUnder b _ = _
    have hK : Levels.Gen.K x₀ (l + 1) = (2 ^ (3 * l + x₀) * Levels.Gen.K x₀ l) ^ 2 := rfl
    by_cases h : Levels.Gen.K x₀ l ≤ b
    · rw [if_pos h]
      change (if (2 ^ (3 * l + x₀) * Levels.Gen.K x₀ l) ^ 2 ≤ b then some (8 * 2 ^ (3 * l + x₀), (2 ^ (3 * l + x₀) * Levels.Gen.K x₀ l) ^ 2) else none) = _
      have e8 : 8 * 2 ^ (3 * l + x₀) = 2 ^ (3 * (l + 1) + x₀) := by
        have h3 : 3 * (l + 1) + x₀ = 3 + (3 * l + x₀) := by ring
        calc 8 * 2 ^ (3 * l + x₀) = 2 ^ 3 * 2 ^ (3 * l + x₀) := by norm_num
          _ = 2 ^ (3 + (3 * l + x₀)) := (pow_add 2 3 _).symm
          _ = 2 ^ (3 * (l + 1) + x₀) := by rw [h3]
      rw [e8, hK]
    · rw [if_neg h, if_neg fun h' => h ((K_le_succ x₀ l).trans h')]
      rfl

/-- After a round the second number is at most b. -/
theorem roundUnder_le {b : ℕ} {s : Option (ℕ × ℕ)} {pk : ℕ × ℕ} (h : roundUnder b s = some pk) : pk.2 ≤ b := by
  cases s with
  | none => cases h
  | some q =>
    change (if (q.1 * q.2) ^ 2 ≤ b then some (8 * q.1, (q.1 * q.2) ^ 2) else none) = some pk at h
    by_cases hq : (q.1 * q.2) ^ 2 ≤ b
    · rw [if_pos hq] at h
      obtain rfl := Option.some.inj h
      exact hq
    · rw [if_neg hq] at h
      cases h

/-- On every input the second number of the state is at most b. -/
theorem fold_le (b : ℕ) (L : List Unit) (s : Option (ℕ × ℕ)) (hs : ∀ pk, s = some pk → pk.2 ≤ b) :
    ∀ pk, L.foldl (fun s _ => roundUnder b s) s = some pk → pk.2 ≤ b := by
  induction L generalizing s with
  | nil => exact hs
  | cons _ L ih => exact ih _ fun _ h => roundUnder_le h

/-- A round makes the word of the state longer by at most 3b + 16. -/
theorem len_roundUnder_le (b : ℕ) (s : Option (ℕ × ℕ)) : len (roundUnder b s) ≤ len s + (3 * b + 16) := by
  cases s with
  | none =>
    change len (none : Option (ℕ × ℕ)) ≤ _
    omega
  | some q =>
    change len (if (q.1 * q.2) ^ 2 ≤ b then some (8 * q.1, (q.1 * q.2) ^ 2) else none) ≤ _
    by_cases hq : (q.1 * q.2) ^ 2 ≤ b
    · rw [if_pos hq, len_some, len_some, len_pair]
      have e : len q = len q.1 + len q.2 + 2 := len_pair q.1 q.2
      have h1 := PolyT.len_mul_le 8 q.1
      have h2 := len_nat_mono hq
      have h3 : len (8 : ℕ) ≤ 14 := by
        rw [len_nat]
        have := Nat.size_le.2 (by norm_num : (8 : ℕ) < 2 ^ 4)
        omega
      have h4 : len b ≤ 3 * b + 2 := by
        rw [len_nat]
        have := Nat.size_le.2 (Nat.lt_two_pow_self (n := b))
        omega
      omega
    · rw [if_neg hq, len_none]
      omega

/-- The rounds are computed in polynomial time. -/
theorem fold_polyT (x₀ : ℕ) : PolyT fun p : List Unit × List Unit =>
    p.1.foldl (fun s _ => roundUnder p.2.length s) (if 2 ^ x₀ ≤ p.2.length then some (2 ^ x₀, 2 ^ x₀) else none) := by
  refine PolyT.foldl_add (l := fun p : List Unit × List Unit => p.1) (a := fun p => if 2 ^ x₀ ≤ p.2.length then some (2 ^ x₀, 2 ^ x₀) else none)
    (g := fun p s _ => roundUnder p.2.length s) (by fun_prop) (by fun_prop) (by unfold roundUnder; fun_prop)
    ⟨fun n => 3 * n + 16, ((PB.const 3).mul PB.id').add (PB.const 16), fun p s _ _ => ?_⟩
  refine (len_roundUnder_le _ s).trans ?_
  change len s + (3 * p.2.length + 16) ≤ len s + (3 * len p + 16)
  have h1 : len p = len p.1 + len p.2 + 2 := len_pair p.1 p.2
  have h2 := len_units p.2
  omega

end CliqueLevels.Proof

theorem solution : LevelsAreComputed := by
  intro x₀
  refine ⟨?_, fun l b => ?_⟩
  · have hu : PolyT fun q : (List Unit × List Unit) × (ℕ × ℕ) => unary (min q.2.2 q.1.2.length) :=
      PolyT.unary_min_length (q := fun q : (List Unit × List Unit) × (ℕ × ℕ) => q.2.2) (l := fun q => q.1.2) (by fun_prop) (by fun_prop)
    refine (PolyT.optionMap (f := fun (p : List Unit × List Unit) (pk : ℕ × ℕ) => unary (min pk.2 p.2.length)) hu (fold_polyT x₀)).congr fun p => ?_
    unfold levelsUnder
    cases h : p.1.foldl (fun s _ => roundUnder p.2.length s) (if 2 ^ x₀ ≤ p.2.length then some (2 ^ x₀, 2 ^ x₀) else none) with
    | none => rfl
    | some pk =>
      have hle := fold_le p.2.length p.1 _ (fun pk' h' => by
        by_cases hb : 2 ^ x₀ ≤ p.2.length
        · rw [if_pos hb] at h'
          obtain rfl := Option.some.inj h'
          exact hb
        · rw [if_neg hb] at h'
          cases h') pk h
      simp only [Option.map_some, min_eq_left hle]
  · unfold levelsUnder
    have e : (unary b).length = b := List.length_replicate
    change Option.map _ ((unary l).foldl (fun s _ => roundUnder (unary b).length s) (if 2 ^ x₀ ≤ (unary b).length then some (2 ^ x₀, 2 ^ x₀) else none)) = _
    rw [e, fold_eq]
    by_cases h : Levels.Gen.K x₀ l ≤ b
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h]
      rfl
