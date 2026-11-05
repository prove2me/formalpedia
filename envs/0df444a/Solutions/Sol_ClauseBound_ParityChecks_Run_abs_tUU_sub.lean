-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.abs_tUU_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:07:14.628767+00:00
-- url     : https://prove2.me/submissions/1b15a9eb-8b99-464e-86b6-b9eb52caae5f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
import Theorems.Thm_ClauseBound_ParityChecks_Approx_approx


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
open ClauseBound.ParityChecks.Run
variable {q}
variable {V} {orcA orcB} {ε : ℚ}
namespace ClauseBound.ParityChecks.Run
theorem _root_.solution (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) (Ls : List Chk) (cur : Chk) (e : ℕ) :
    |tUU q V Ls cur e - UU q V Ls cur e| ≤ 1 / 2 * ε * NN X q := by
  have h := H2.approx X (Fin q.m) V q.nb q.r q.i₀ Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) ε
  simp only [Fintype.card_fin] at h
  have h1 := h hq.series
  have e1 : tUU q V Ls cur e - UU q V Ls cur e =
      tUpar V q.nb q.r q.i₀ Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) - Upar V q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) := by
    unfold tUU UU Ups
    ring
  rw [e1]
  exact h1
end ClauseBound.ParityChecks.Run
