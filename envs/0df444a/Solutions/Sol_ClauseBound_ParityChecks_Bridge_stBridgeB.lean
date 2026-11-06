-- Prove2me | solution 1 for ClauseBound.ParityChecks.Bridge.stBridgeB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:51:40.687192+00:00
-- url     : https://prove2.me/submissions/f2157a13-6348-499b-85a5-68b8a84b3c81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_Bridge
import Theorems.Thm_ClauseBound_ParityChecks_Bridge_sum_Icc_choose
import Theorems.Thm_ClauseBound_ParityChecks_Bridge_sum_Icc_self
import Theorems.Thm_ClauseBound_ParityChecks_Bridge_sum_split
import Theorems.Thm_ClauseBound_ParityChecks_Bridge_truncW3
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_disjoint_J
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_nvio_all
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_nvio_drop
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_nvio_incL
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_prod_J1
import Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_prod_J2
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
theorem _root_.solution : StBridgeB := by
  intro n r nb M i j t ψ Lam hψ hW hj
  have e : sumB n r nb M i ψ Lam j t = ∑ ξ, ((omega (Vof (n := n) ψ) nb ξ : ℤ) * ((#(Dof ψ t ∩ Vof ψ ξ)).choose i : ℤ)) *
      ∑ y : Fin r → Bool, ∑ S ∈ (Dummy.inc (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) (J2 r j) ξ y).powerset with #S ≤ M, (-2 : ℤ) ^ #S := by
    rw [sumB, truncW3, ← sum_congr rfl fun ξ _ => (mul_sum _ _ _).symm,
      ← sum_split fun ξ y => ((omega (Vof (n := n) ψ) nb ξ : ℤ) * ((#(Dof ψ t ∩ Vof ψ ξ)).choose i : ℤ)) *
        ∑ S ∈ (Dummy.inc (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) (J2 r j) ξ y).powerset with #S ≤ M, (-2 : ℤ) ^ #S]
    refine sum_congr rfl fun σ _ => ?_
    rw [sum_Icc_self, sum_Icc_self, nvio_all hψ, nvio_incL hψ hW hj.le, nvio_drop hψ, sum_Icc_choose, omega]
    ring
  rw [e]
  refine (Dummy.cutoff_dummy (Vof (n := n) ψ) r (Lof ψ Lam) (J1 r j) (J2 r j) (disjoint_J r j) _ M).symm.trans ?_
  have e2 : ∑ ξ, ((omega (Vof (n := n) ψ) nb ξ : ℤ) * ((#(Dof ψ t ∩ Vof ψ ξ)).choose i : ℤ)) *
      (∏ j' ∈ J1 r j, ev #(Lof ψ Lam j' ∩ Vof ψ ξ)) * ∏ j' ∈ J2 r j, (-1 : ℤ) ^ #(Lof ψ Lam j' ∩ Vof ψ ξ) =
      Bint (Vof (n := n) ψ) nb i j (Lof ψ Lam) (Dof ψ t) := by
    unfold Bint
    refine sum_congr rfl fun ξ _ => ?_
    rw [prod_J1 hj.le fun j' => ev #(Lof ψ Lam j' ∩ Vof ψ ξ), prod_J2 hj fun j' => (-1 : ℤ) ^ #(Lof ψ Lam j' ∩ Vof ψ ξ)]
    ring
  rw [e2]
end ClauseBound.ParityChecks.Bridge
