-- Prove2me | solution 2 for CountKSat.stWalkSum
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:20:47.91195+00:00
-- url     : https://prove2.me/submissions/9da560f1-c2ed-43c9-b342-ca94b5068604

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Poly_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Mathlib.Tactic.Ring
import Definitions.Def_CountKSat_Walk
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Stepped_orbit_visits
import Theorems.Thm_Groundwork_Stepped_filterMap_visits
import Theorems.Thm_Groundwork_Stepped_length_visits
import Theorems.Thm_Groundwork_Stepped_foldWhile_runs
import Theorems.Thm_Groundwork_Stepped_sum_sel
import Theorems.Thm_Groundwork_Stepped_exists_round_of_orbit
import Theorems.Thm_Groundwork_Stepped_guard_runs_none
import Theorems.Thm_Groundwork_Stepped_guard_runs_some
attribute [local fun_prop] Groundwork.PolyT.all

set_option autoImplicit false
section
open CountKSat
open Groundwork Groundwork.Stepped Groundwork.Sparsify
variable {α ν : Type}

namespace CountKSat.Walk

/-- The loop's fold accumulates the values selected from the visited states. -/
private theorem foldl_add_sel {τ : Type} (sel : τ → Option ν) (v : ν → ℕ) (xs : List τ) (c : ℕ) :
    xs.foldl (fun c x => c + ((sel x).map v).getD 0) c = c + ((xs.filterMap sel).map v).sum := by
  induction xs generalizing c with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    cases h : sel x <;> simp [h, Nat.add_assoc]

/-- The selected-value sum over a prefix is bounded by the sum over the whole list. -/
private theorem sum_prefix_le {τ : Type} (sel : τ → Option ν) (v : ν → ℕ) {l xs : List τ} (h : l <+: xs) :
    ((l.filterMap sel).map v).sum ≤ ((xs.filterMap sel).map v).sum := by
  obtain ⟨r, rfl⟩ := h
  rw [List.filterMap_append, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

end CountKSat.Walk

namespace CountKSat

open Walk

/-- The summing walk runs for `t + 2` steps per visited leaf and returns their value sum. -/
private theorem walkSum_runs [HasSize ν] (step : ν → Option (ν × ν)) {root : α → ν} {T : Stepped ν ℕ} (d : ℕ) (a : α)
    (hd : ∀ x ∈ leaves step d (root a), step x = none) (v : ν → ℕ) (t Sm Sx B : ℕ)
    (hT : ∀ x ∈ leaves step d (root a), T.Runs x t Sm (v x))
    (hS : ∀ i, size ((Sparsify.round step)^[i] ([root a], [])).1 ≤ Sx)
    (hB : ((leaves step d (root a)).map v).sum < 2 ^ B) :
    (walkSum step root T).Runs a ((leaves step d (root a)).length * (t + 2)) (Sx + (B + 1 + (Sm + 1)) + 1)
      ((leaves step d (root a)).map v).sum := by
  have ho : Orbit (walkNext step) (some [root a]) (visits step d (root a) [] ++ [[]]) :=
    orbit_visits step d (root a) [] [[]] hd (.cons .nil)
  have hf : (visits step d (root a) [] ++ [[]]).filterMap (walkSel step) = leaves step d (root a) := by
    rw [List.filterMap_append, filterMap_visits step d (root a) [] hd]
    simp [walkSel]
  have hlen : (visits step d (root a) [] ++ [[]]).length = 2 * (leaves step d (root a)).length := by
    rw [List.length_append, ← length_visits step d (root a) []]
    rfl
  have key := foldWhile_runs (start := fun a : α => some [root a]) (M := guard (walkSel step) T 0)
    (g := fun c _ b => c + b) (c₀ := fun _ => 0) (a := a) ho
    (fun st => ((walkSel step st).map fun _ => t).getD 0) (fun st => ((walkSel step st).map v).getD 0)
    Sx (B + 1) (Sm + 1)
    (by
      intro st hst
      cases h : walkSel step st with
      | none => exact (guard_runs_none h).mono le_rfl (by omega)
      | some x => exact guard_runs_some h (hT x (hf ▸ List.mem_filterMap.2 ⟨st, hst, h⟩)))
    (by
      intro st hst
      obtain ⟨i, rfl⟩ := exists_round_of_orbit step ho st hst
      exact hS i)
    (by
      intro l hl
      rw [Walk.foldl_add_sel, Nat.zero_add]
      have h1 := Walk.sum_prefix_le (walkSel step) v hl
      rw [hf] at h1
      exact Nat.succ_le_succ (Nat.size_le.2 (lt_of_le_of_lt h1 hB)))
  rw [sum_sel, Walk.foldl_add_sel, hf, hlen, Nat.zero_add] at key
  exact key.mono (le_of_eq (by ring)) le_rfl

end CountKSat

open Walk

theorem solution : StWalkSum := fun _ _ _ step _ _ d a hd v t Sm Sx B hT hS hB =>
  CountKSat.walkSum_runs step d a hd v t Sm Sx B hT hS hB

#print axioms solution
