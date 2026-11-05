-- Prove2me | solution 1 for ClauseBound.ParityChecks.Start.nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:15:17.016768+00:00
-- url     : https://prove2.me/submissions/1072408d-dbcf-4cb2-adfa-23db099d96d8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_ClauseBound_ParityChecks_Start
import Theorems.Thm_ClauseBound_ParityChecks_Start_one_sub_nonneg
import Theorems.Thm_ClauseBound_ParityChecks_Start_one_sub_le_one
import Theorems.Thm_ClauseBound_ParityChecks_Start_ev_nonneg
import Theorems.Thm_ClauseBound_ParityChecks_Start_factor_nonneg

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Start
open _root_.ParityChecks Finset
namespace ClauseBound.ParityChecks.Start
theorem _root_.solution : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (D : Finset E), 2 ≤ nb →
    0 ≤ Upar V nb r j Λ D ∧ 0 ≤ Uinc nb r j Λ D ∧ 0 ≤ Urow nb r j Λ D ∧ 0 ≤ Ucol nb r j Λ D := by
  intro X E _ _ _ V nb r j Λ D hnb
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Upar
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun ξ _ => ?_)
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun _ _ => ev_nonneg _))
      (factor_nonneg (one_sub_nonneg hnb) (one_sub_le_one hnb) _ _)
  · unfold Uinc pr; positivity
  · unfold Urow pr
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  · unfold Ucol pr
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
end ClauseBound.ParityChecks.Start
