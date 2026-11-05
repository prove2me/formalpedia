-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.bd_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:21:53.431357+00:00
-- url     : https://prove2.me/submissions/84a1ab17-f374-40dd-9449-d31bfa6cd683

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
import Theorems.Thm_ClauseBound_ParityChecks_isState


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
theorem _root_.solution (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) {Ls : List Chk} {cur : Chk} {e : ℕ} (hj : Ls.length < q.r) (hc : ChkOK e cur)
    (hU : UU q V Ls cur e < 1) : Bd q (lam q.m (Ls ++ [cur])) := by
  have h := H2.structure_ X (Fin q.m) V q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) hq.nb_two
  simp only [Fintype.card_fin] at h
  obtain ⟨h1, h2, h3⟩ := h hq.m_pos (isState q hj hc) hU
  exact ⟨h1, h2, h3⟩
end ClauseBound.ParityChecks.Run
