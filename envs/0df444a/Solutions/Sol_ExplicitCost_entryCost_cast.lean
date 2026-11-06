-- Prove2me | solution 1 for ExplicitCost.entryCost_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:26:12.264194+00:00
-- url     : https://prove2.me/submissions/b70bdbfe-7a94-462d-a3a0-98452ad2848c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallParts
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallLemma

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (hE : EntryCostExplicit) : ∃ c₁ : ℕ, ∀ (K g n : ℕ) (_ : n = g) (hK0 : 0 < K) (N : Net n) (P B τ : ℕ), K ≤ g → N.Is P B → 1 ≤ τ →
    ∀ x < K ^ g, ∀ L ≤ 2 * (g * P), (∀ γ : Fin K, K * #{a : Fin n | Paper.grouping hK0 x a = γ} ≤ 2 * g) → (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) →
      ∀ (γ : Fin K), ∀ Θ ∈ words ((K - 1) * L),
        entryData.Within (netOracle N) (fun _ => τ) ((((unary K, unary g), netInput N P B), x), toLists K L (γ.val, Θ)) (2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ c₁) ((g * (P + B)) ^ c₁)
          ((Value.groupClique asked.under (netInput N P B) N hK0 x L).W γ Θ) ∧
        |(Value.groupClique asked.under (netInput N P B) N hK0 x L).W γ Θ| < 2 ^ bitsOut K g P B := by
  obtain ⟨c₁, h⟩ := hE
  refine ⟨c₁, fun K g n hn => ?_⟩
  subst hn
  exact h K n
end ExplicitCost
