-- Prove2me | solution 1 for ClauseBound.ParityChecks.run_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:27:11.322803+00:00
-- url     : https://prove2.me/submissions/8ae92c59-71f9-414d-a9e2-abc5fc401616

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
import Theorems.Thm_ClauseBound_ParityChecks_Run_Dset_self
import Theorems.Thm_ClauseBound_ParityChecks_Run_bd_of_lt_one
import Theorems.Thm_ClauseBound_ParityChecks_Run_Inv_lt_one
import Theorems.Thm_ClauseBound_ParityChecks_Run_runChecks_succ
import Theorems.Thm_ClauseBound_ParityChecks_Run_inv_runTo
import Theorems.Thm_ClauseBound_ParityChecks_Run_inv_runChecks
import Theorems.Thm_ClauseBound_ParityChecks_isState


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
open Run
namespace ClauseBound.ParityChecks
theorem _root_.solution (H2 : ChoiceByPotential) {ε : ℚ} (hq : Hyp q (Fintype.card X) ε) (ho : OrcOK q V orcA orcB) :
    (q.run orcA orcB).length = q.r ∧ (∀ L ∈ q.run orcA orcB, ChkOK q.m L) ∧ Good V q.nb q.r (lam q.m (q.run orcA orcB)) ∧
      ((∑ j' ∈ range q.r, #(lam q.m (q.run orcA orcB) j') : ℕ) : ℚ) < 8 * pr q.nb * q.m * q.r ∧
      (∀ j' < q.r, (2 : ℚ) ^ #(lam q.m (q.run orcA orcB) j') < 8 * q.r * (1 + pr q.nb) ^ q.m) ∧
      ∀ x : Fin q.m, (2 : ℚ) ^ #{j' ∈ range q.r | x ∈ lam q.m (q.run orcA orcB) j'} < 8 * q.m * (1 + pr q.nb) ^ q.r := by
  have hr := hq.r_pos
  obtain ⟨hlen, hinv⟩ := inv_runChecks H2 hq ho (q.r - 1) (by omega)
  have hend := inv_runTo H2 hq ho hinv q.m le_rfl
  have erun : q.run orcA orcB = q.runChecks orcA orcB (q.r - 1) ++ [q.runTo orcA orcB (q.runChecks orcA orcB (q.r - 1)) q.m] := by
    unfold Par.run
    conv_lhs => rw [show q.r = q.r - 1 + 1 by omega]
    exact runChecks_succ _
  have hb := bd_of_lt_one H2 hq hend.lt hend.okc (hend.lt_one hq)
  rw [← erun] at hb
  refine ⟨by rw [erun, List.length_append, hlen]; simp; omega, fun L hL => ?_, ?_, hb.inc, hb.row, hb.col⟩
  · rw [erun] at hL
    rcases List.mem_append.1 hL with h | h
    · exact hinv.done L h
    · rw [List.mem_singleton.1 h]; exact hend.okc
  · have hst := isState q hend.lt hend.okc
    have hU := hend.lt_one hq
    unfold UU at hU
    rw [Dset_self, hlen, ← erun] at hst hU
    exact H2.final X (Fin q.m) V q.nb q.r _ hq.nb_two hst hU
end ClauseBound.ParityChecks
