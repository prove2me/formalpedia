-- Prove2me | solution 1 for ClauseBound.ParityChecks.Bridge.two_layers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:45:24.59425+00:00
-- url     : https://prove2.me/submissions/82226a59-4c4d-4fc3-b232-8f140219fe06

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_Bridge
import Theorems.Thm_ClauseBound_ParityChecks_Bridge_sum_Icc_choose
import Theorems.Thm_ClauseBound_ParityChecks_Bridge_sum_split
import Theorems.Thm_ClauseBound_ParityChecks_Bridge_truncW2
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_nvio_all
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_nvio_incL_take
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_prod_J1
import Theorems.Thm_ClauseBound_ParityChecks_Dummy_cutoff_dummy
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Bridge
open Groundwork.Prog (Fml)
open PaddedDescent.F.Mark (nvio vio nSat)
open ClauseBound.TopN.EvalW (truncW)
open ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc
namespace ClauseBound.ParityChecks.Bridge
theorem _root_.solution {n r j : ℕ} {ψ : Fml} {Lam : List (List ℕ)} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (hW : WfC ψ r Lam) (hj : j ≤ r) (M : ℕ)
    (w : ℤ) (l h : ℕ) (f : (Fin n → Bool) → ℤ) (hf : ∀ ξ, ∑ q ∈ Icc l h, w ^ q * ((#(Vof ψ ξ)).choose q : ℤ) = f ξ) :
    truncW (n + r) [w, -2] [l, 0] [h, M] [ψ, incL n ψ (Lam.take j) j] ≡
      2 ^ r * ∑ ξ, f ξ * ∏ j' ∈ range j, ev #(Lof ψ Lam j' ∩ Vof ψ ξ) [ZMOD 2 ^ (M + 1)] := by
  have e : truncW (n + r) [w, -2] [l, 0] [h, M] [ψ, incL n ψ (Lam.take j) j] = ∑ ξ, f ξ *
      ∑ y : Fin r → Bool, ∑ S ∈ (Dummy.inc (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) ∅ ξ y).powerset with #S ≤ M, (-2 : ℤ) ^ #S := by
    rw [truncW2, ← sum_congr rfl fun ξ _ => (mul_sum _ _ _).symm,
      ← sum_split fun ξ y => f ξ *
        ∑ S ∈ (Dummy.inc (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) ∅ ξ y).powerset with #S ≤ M, (-2 : ℤ) ^ #S]
    refine sum_congr rfl fun σ _ => ?_
    rw [nvio_all hψ, nvio_incL_take hψ hW hj, sum_Icc_choose, hf, mul_one]
  rw [e]
  refine (Dummy.cutoff_dummy (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) ∅ (disjoint_empty_right _) f M).symm.trans ?_
  have e2 : ∑ ξ, f ξ * (∏ j' ∈ J1 r j, ev #(Lof ψ Lam j' ∩ Vof ψ ξ)) * ∏ j' ∈ (∅ : Finset (Fin r)), (-1 : ℤ) ^ #(Lof ψ Lam j' ∩ Vof ψ ξ) =
      ∑ ξ, f ξ * ∏ j' ∈ range j, ev #(Lof ψ Lam j' ∩ Vof ψ ξ) := by
    refine sum_congr rfl fun ξ _ => ?_
    rw [prod_J1 hj fun j' => ev #(Lof ψ Lam j' ∩ Vof ψ ξ), prod_empty, mul_one]
  rw [e2]
end ClauseBound.ParityChecks.Bridge
