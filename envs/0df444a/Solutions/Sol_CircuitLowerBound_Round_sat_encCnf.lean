-- Prove2me | solution 1 for CircuitLowerBound.Round.sat_encCnf
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:33:21.552753+00:00
-- url     : https://prove2.me/submissions/44dda025-a4a6-42c0-a700-5dc36c20cfb8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Round
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Round

private theorem replicate_inj' {v v' : ℕ} {Y Y' : List Bool}
    (h : List.replicate v true ++ false :: Y = List.replicate v' true ++ false :: Y') : v = v' ∧ Y = Y' := by
  induction v generalizing v' with
  | zero =>
    cases v' with
    | zero => simpa using h
    | succ v' => simp [List.replicate_succ] at h
  | succ v ih =>
    cases v' with
    | zero => simp [List.replicate_succ] at h
    | succ v' =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨a, b⟩ := ih h
      exact ⟨by rw [a], b⟩

private theorem clause_inj' {C C' : List (ℕ × Bool)} {r r' : List Bool}
    (h : C.flatMap encLit ++ false :: r = C'.flatMap encLit ++ false :: r') : C = C' ∧ r = r' := by
  induction C generalizing C' with
  | nil =>
    cases C' with
    | nil => simpa using h
    | cons l' C' => simp [encLit] at h
  | cons l C ih =>
    cases C' with
    | nil => simp [encLit] at h
    | cons l' C' =>
      simp only [List.flatMap_cons, encLit, List.cons_append, List.append_assoc, List.cons.injEq, true_and, List.nil_append] at h
      obtain ⟨a, b⟩ := replicate_inj' h
      simp only [List.cons.injEq] at b
      obtain ⟨c, d⟩ := ih b.2
      exact ⟨by rw [c, Prod.ext a b.1], d⟩

private theorem encCnf_cons' (C : List (ℕ × Bool)) (φ : Cnf) :
    encCnf (C :: φ) = C.flatMap encLit ++ false :: true :: encCnf φ := by
  simp [encCnf]

private theorem encCnf_injective' {φ φ' : Cnf} (h : encCnf φ = encCnf φ') : φ = φ' := by
  induction φ generalizing φ' with
  | nil =>
    cases φ' with
    | nil => rfl
    | cons C' φ' =>
      rw [encCnf_cons'] at h
      have h' : ([] : List (ℕ × Bool)).flatMap encLit ++ false :: [false] =
          C'.flatMap encLit ++ false :: true :: encCnf φ' := h
      simpa using (clause_inj' h').2
  | cons C φ ih =>
    cases φ' with
    | nil =>
      rw [encCnf_cons'] at h
      have h' : C.flatMap encLit ++ false :: true :: encCnf φ =
          ([] : List (ℕ × Bool)).flatMap encLit ++ false :: [false] := h
      simpa using (clause_inj' h').2
    | cons C' φ' =>
      rw [encCnf_cons', encCnf_cons'] at h
      obtain ⟨a, b⟩ := clause_inj' h
      rw [a, ih (List.cons.inj b).2]

theorem solution (φ : Cnf) : SAT (encCnf φ) ↔ Sat φ :=
  ⟨fun ⟨_, h, hs⟩ => encCnf_injective' h ▸ hs, fun h => ⟨φ, rfl, h⟩⟩
