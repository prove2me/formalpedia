-- Prove2me | solution 1 for ClauseBound.Alg.Enum.value_eq_sum_labels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:37:02.862977+00:00
-- url     : https://prove2.me/submissions/d51a9715-14a2-4d8d-8abc-7a91a2278c38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_StepMachines_Math_CodeSeq
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_ClauseBound_Alg_Enum
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_pr_of_lt
import Theorems.Thm_Groundwork_prod_erase_eq_pairs
import Theorems.Thm_Groundwork_sum_tuples_prod


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.Enum
open Finset Groundwork Groundwork.Prog PaddedDescent.F
variable {J σ τ : Type} [Fintype J] [LinearOrder J]
namespace ClauseBound.Alg.Enum
theorem _root_.solution (N : Network J σ τ) (t₀ : τ) :
    N.value = ∑ t ∈ tuples (fun p : J × J => p.1 < p.2) (fun p => N.lab p.1 p.2) t₀,
      ∏ a, ∑ z ∈ N.S a, N.W a z * ∏ b ∈ univ.erase a, N.f a b z (t (pr a b)) := by
  unfold Network.value
  have h1 : ∀ z : J → σ, ∏ p ∈ pairs J, N.Ψ p.1 p.2 (z p.1) (z p.2) =
      ∑ t ∈ tuples (fun p : J × J => p.1 < p.2) (fun p => N.lab p.1 p.2) t₀,
        ∏ p ∈ pairs J, N.f p.1 p.2 (z p.1) (t p) * N.f p.2 p.1 (z p.2) (t p) := fun z =>
    (sum_tuples_prod (fun p : J × J => p.1 < p.2) (fun p => N.lab p.1 p.2) t₀
      fun p θ => N.f p.1 p.2 (z p.1) θ * N.f p.2 p.1 (z p.2) θ).symm
  simp_rw [h1, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  rw [prod_univ_sum]
  refine sum_congr rfl fun z _ => ?_
  rw [prod_mul_distrib (s := univ), prod_erase_eq_pairs fun a b => N.f a b (z a) (t (pr a b))]
  congr 1
  refine prod_congr rfl fun p hp => ?_
  have h := pr_of_lt (mem_filter.1 hp).2
  rw [h.1, h.2]
end ClauseBound.Alg.Enum
