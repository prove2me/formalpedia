-- Prove2me | solution 1 for ClauseBound.Group.Grouping.card_filter_le_of_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:58:15.174446+00:00
-- url     : https://prove2.me/submissions/12723f6d-cbac-4bd1-9eda-3e635c024113

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Group_Sample
import Definitions.Def_ClauseBound_Group_Grouping

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Group
open Finset
open ClauseBound.Group.Grouping
namespace ClauseBound.Group.Grouping
theorem _root_.solution {Ω X : Type} [DecidableEq X] (Ω' : Finset Ω) (F : Ω → X) (Xs : Finset X) (hF : ∀ e ∈ Ω', F e ∈ Xs)
    (hconst : ∀ x ∈ Xs, ∀ x' ∈ Xs, #{e ∈ Ω' | F e = x} ≤ #{e ∈ Ω' | F e = x'}) (Q : X → Prop) [DecidablePred Q] (ε : ℝ)
    (hQ : (#{x ∈ Xs | Q x} : ℝ) ≤ ε * #Xs) : (#{e ∈ Ω' | Q (F e)} : ℝ) ≤ ε * #Ω' := by
  rcases Xs.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · have : Ω' = ∅ := eq_empty_iff_forall_notMem.2 fun e he => by simpa using hF e he
    subst this
    simp
  · have hf : ∀ x ∈ Xs, #{e ∈ Ω' | F e = x} = #{e ∈ Ω' | F e = x₀} := fun x hx => le_antisymm (hconst x hx x₀ hx₀) (hconst x₀ hx₀ x hx)
    have h1 : #Ω' = #Xs * #{e ∈ Ω' | F e = x₀} := by
      rw [card_eq_sum_card_fiberwise (f := F) (t := Xs) (fun e he => hF e he), sum_congr rfl hf, sum_const, smul_eq_mul]
    have h2 : #{e ∈ Ω' | Q (F e)} = #{x ∈ Xs | Q x} * #{e ∈ Ω' | F e = x₀} := by
      rw [card_eq_sum_card_fiberwise (f := F) (t := {x ∈ Xs | Q x})
        (fun e he => mem_coe.2 (mem_filter.2 ⟨hF e (mem_filter.1 (mem_coe.1 he)).1, (mem_filter.1 (mem_coe.1 he)).2⟩)), ← smul_eq_mul, ← sum_const]
      refine sum_congr rfl fun x hx => ?_
      rw [← hf x (mem_filter.1 hx).1, filter_filter]
      congr 1
      refine filter_congr fun e _ => ⟨fun h => h.2, fun h => ⟨h ▸ (mem_filter.1 hx).2, h⟩⟩
    rw [h1, h2]
    push_cast
    calc (#{x ∈ Xs | Q x} : ℝ) * #{e ∈ Ω' | F e = x₀} ≤ ε * #Xs * #{e ∈ Ω' | F e = x₀} := mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg _)
      _ = ε * (#Xs * #{e ∈ Ω' | F e = x₀}) := by ring
end ClauseBound.Group.Grouping
