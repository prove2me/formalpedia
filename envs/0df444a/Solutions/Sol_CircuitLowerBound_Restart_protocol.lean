-- Prove2me | solution 1 for CircuitLowerBound.Restart.protocol
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:18:43.938306+00:00
-- url     : https://prove2.me/submissions/0cd8e58f-24ec-439d-a2ff-d42987a97ac0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_ENP_Round
import Definitions.Def_CircuitLowerBound_Small
import Definitions.Def_CountKSatRate_Pad
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Restart
import Theorems.Thm_CircuitLowerBound_Round_sat_encCnf
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork PaddedDescent Turing
open CircuitLowerBound.Restart
open Classical
namespace CircuitLowerBound.Restart
theorem _root_.solution {N : TM2ComputableAux Bool Bool} {T : ℕ} {x : List Bool} {φ : Cnf}
    (hq : ∀ j ≤ ofWord x, ENP.Round N T x ((greedy φ j).map fun b => !b) (true :: encCnf (φ ++ units (greedy φ j ++ [false]))))
    (hd : ENP.Round N T x ((greedy φ (ofWord x + 1)).map fun b => !b) [false, (greedy φ (ofWord x + 1)).getD (ofWord x) false]) :
    ∀ d j r : ℕ, j + d = ofWord x + 1 → d ≤ r →
      Protocol N T x ((greedy φ (ofWord x + 1)).getD (ofWord x) false) ((greedy φ j).map fun b => !b) r
  | 0, j, r, hj, _ => by
    obtain rfl : j = ofWord x + 1 := by omega
    exact .done hd
  | d + 1, j, r, hj, hr => by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    refine .query (hq j (by omega)) ?_
    have e1 : decide (SAT (encCnf (φ ++ units (greedy φ j ++ [false])))) = decide (Sat (φ ++ units (greedy φ j ++ [false]))) :=
      decide_eq_decide.2 (Round.sat_encCnf _)
    have e : ((greedy φ j).map fun b => !b) ++ [decide (SAT (encCnf (φ ++ units (greedy φ j ++ [false]))))] = (greedy φ (j + 1)).map fun b => !b := by
      rw [e1, greedy, List.map_append, List.map_singleton, Bool.not_not]
    rw [e]
    exact solution hq hd d (j + 1) r' (by omega) (by omega)
end CircuitLowerBound.Restart
