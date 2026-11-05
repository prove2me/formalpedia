-- Prove2me | solution 1 for CircuitLowerBound.stNorm
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:22:11.472887+00:00
-- url     : https://prove2.me/submissions/13765813-d5bc-4be0-90f4-2de3267c9f14

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Norm
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Norm

private theorem toGate_op' (n : ℕ) (G : Gate) (x y : Bool) :
    (ng n G).toGate.op x y = op' n G x y := by
  cases x <;> cases y <;> rfl

private theorem length_norm' (C : Circuit) (n : ℕ) : (norm n C).length = C.length := by
  induction C generalizing n with
  | nil => rfl
  | cons G C ih => simp [CircuitLowerBound.Norm.norm, ih]

private theorem value_ng' (w : List Bool) (G : Gate) :
    (ng w.length G).toGate.op
        (w.getD (ng w.length G).toGate.in₁ false)
        (w.getD (ng w.length G).toGate.in₂ false) =
      G.op (w.getD G.in₁ false) (w.getD G.in₂ false) := by
  rw [toGate_op']
  change op' w.length G
      (w.getD (if G.in₁ < w.length then G.in₁ else 0) false)
      (w.getD (if G.in₂ < w.length then G.in₂ else 0) false) = _
  unfold op'
  by_cases h1 : G.in₁ < w.length <;> by_cases h2 : G.in₂ < w.length <;>
    simp [h1, h2]

private theorem wires_norm' (C : Circuit) (w : List Bool) :
    wires w (toC (norm w.length C)) = wires w C := by
  induction C generalizing w with
  | nil => rfl
  | cons G C ih =>
    have h := ih (w ++ [G.op (w.getD G.in₁ false) (w.getD G.in₂ false)])
    rw [List.length_append, List.length_singleton] at h
    change wires (w ++ [(ng w.length G).toGate.op
        (w.getD (ng w.length G).toGate.in₁ false)
        (w.getD (ng w.length G).toGate.in₂ false)])
      (toC (norm (w.length + 1) C)) =
        wires (w ++ [G.op (w.getD G.in₁ false) (w.getD G.in₂ false)]) C
    rw [value_ng', h]

private theorem wf_norm' (C : Circuit) (n : ℕ) (hn : 1 ≤ n) : WF n (norm n C) := by
  induction C generalizing n with
  | nil => intro t h; simp [CircuitLowerBound.Norm.norm] at h
  | cons G C ih =>
    intro t h
    cases t with
    | zero =>
      change (if G.in₁ < n then G.in₁ else 0) < n + 0 ∧
        (if G.in₂ < n then G.in₂ else 0) < n + 0
      constructor <;> split_ifs <;> omega
    | succ t =>
      have h' : t < (norm (n + 1) C).length := by simpa [CircuitLowerBound.Norm.norm] using h
      have := ih (n + 1) (by omega) t h'
      change (norm (n + 1) C)[t].2.1 < n + (t + 1) ∧
        (norm (n + 1) C)[t].2.2 < n + (t + 1)
      omega

theorem solution : StNorm := by
  intro m C hm
  refine ⟨norm m C, wf_norm' C m hm, length_norm' C m, fun x hx => ?_⟩
  unfold eval
  rw [← hx, wires_norm']
