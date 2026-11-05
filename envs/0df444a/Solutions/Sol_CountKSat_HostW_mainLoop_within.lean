-- Prove2me | solution 1 for CountKSat.HostW.mainLoop_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:42:41.80521+00:00
-- url     : https://prove2.me/submissions/9895a9b4-2d49-4c7c-909c-5f49406653e2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_CountKSat_Host
import Theorems.Thm_CountKSat_HostW_chkW_none
import Theorems.Thm_CountKSat_HostW_chkW_some
import Theorems.Thm_CountKSat_HostW_size_le_of_reaches
import Theorems.Thm_CountKSat_HostW_look_within
import Theorems.Thm_Groundwork_Host_look_within
import Theorems.Thm_Groundwork_Host_size_le_of_reaches
import Theorems.Thm_Groundwork_Host_within_io
import Theorems.Thm_Groundwork_TM_Frag_Within_seq
import Theorems.Thm_Groundwork_TM_Frag_loop_runs_exit
import Theorems.Thm_Groundwork_TM_Frag_loop_runs_iter


set_option autoImplicit false
section
open CountKSat CountKSat.HostW
open Groundwork Groundwork.TM Groundwork.Host Turing
variable {M : Stepped (List Bool) (List Bool)}
variable [Enc M.σ]
variable {Ps Po : Fr} {tS tO : ℕ → ℕ}
  (hS : ∀ (s : M.σ) (M' A B N : List Sym),
    Ps.Within (st (wd s ++ M') A B N) (tS (len s)) (st (wd (M.step s) ++ M') A B N))
  (hO : ∀ (s : M.σ) (M' A B N : List Sym),
    Po.Within (st (wd s ++ M') A B N) (tO (len s)) (st (wd (M.out s) ++ M') A B N))
include hS hO
namespace CountKSat.HostW
theorem _root_.solution (mS : Monotone tS) (mO : Monotone tO) {S L : ℕ} (hL : ∀ s : M.σ, size s ≤ S → len s ≤ L) {w : List Bool}
    {s : M.σ} {t : ℕ} (h : M.Reaches S w s t) :
    ∃ s' : M.σ, size s' ≤ S ∧ M.out s' = some w ∧
      Frag.Within (mainLoop Ps Po) (withIO [] (st (wd (M.out s) ++ (wd s ++ [])) [] [] []))
        (t * (1 + (tS L + (3 * L + 3 + tO L))) + 1) (withIO [] (st (wd w ++ (.L :: .R :: .R :: (wd s' ++ []))) [] [] [])) := by
  induction h with
  | @halt s t ho hs =>
    refine ⟨s, hs, ho, 1, by omega, ?_⟩
    rw [ho]
    exact Frag.loop_runs_exit (chkW_some _ _ _ _ _ w)
  | @step s t ho hs hr ih =>
    obtain ⟨s', hs', ho', n, hn, hrun⟩ := ih
    obtain ⟨m, hm, hb⟩ := within_io ((hS s [] [] [] []).seq (look_within hO (M.step s) [] [] [] [])) []
    refine ⟨s', hs', ho', 1 + m + n, ?_, ?_⟩
    · have h1 := mS (hL s hs)
      have h2 := hL _ (size_le_of_reaches hr)
      have h3 := mO h2
      have e : (t + 1) * (1 + (tS L + (3 * L + 3 + tO L))) =
          t * (1 + (tS L + (3 * L + 3 + tO L))) + (1 + (tS L + (3 * L + 3 + tO L))) := Nat.succ_mul _ _
      omega
    · rw [ho]
      exact Frag.loop_runs_iter (chkW_none _ _ _ _ _) hb hrun
end CountKSat.HostW
