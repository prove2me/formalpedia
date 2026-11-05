-- Prove2me | solution 1 for ClauseBound.ParityChecks.Run.inv_runChecks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:25:54.274642+00:00
-- url     : https://prove2.me/submissions/43a5465e-5eee-4edf-9690-c103cd490480

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
import Definitions.Def_ClauseBound_ParityChecks_Run
import Theorems.Thm_ClauseBound_ParityChecks_Run_chkOK_nil
import Theorems.Thm_ClauseBound_ParityChecks_Run_Dset_zero
import Theorems.Thm_ClauseBound_ParityChecks_Run_Dset_self
import Theorems.Thm_ClauseBound_ParityChecks_Run_lam_append_nil
import Theorems.Thm_ClauseBound_ParityChecks_Run_lam_start
import Theorems.Thm_ClauseBound_ParityChecks_Run_NN_nonneg
import Theorems.Thm_ClauseBound_ParityChecks_Run_eps_nonneg
import Theorems.Thm_ClauseBound_ParityChecks_Run_runChecks_succ
import Theorems.Thm_ClauseBound_ParityChecks_Run_inv_runTo
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
theorem _root_.solution (H2 : ChoiceByPotential) (hq : Hyp q (Fintype.card X) ε) (ho : OrcOK q V orcA orcB) :
    ∀ j < q.r, (q.runChecks orcA orcB j).length = j ∧ Inv q V ε (q.runChecks orcA orcB j) [] 0 := by
  intro j
  induction j with
  | zero =>
    intro hr
    refine ⟨rfl, hr, fun L hL => absurd hL (List.not_mem_nil), chkOK_nil 0, Nat.zero_le _, ?_⟩
    have h := H2.start X (Fin q.m) V q.nb q.r hq.nb_two hq.r_pos
    simp only [Fintype.card_fin] at h
    have h1 := h hq.m_pos hq.start
    have e1 : UU q V (q.runChecks orcA orcB 0) [] 0 = Ups V q.nb q.r 0 (fun _ => ∅) univ := by
      change Ups V q.nb q.r 0 (lam q.m ([] ++ [[]])) (Dset q.m 0) = _
      rw [lam_start, Dset_zero]
    rw [e1]
    have h2 : 0 ≤ (((q.runChecks orcA orcB 0).length * q.m + 0 : ℕ) : ℚ) * (ε * NN X q) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (eps_nonneg hq) NN_nonneg)
    linarith
  | succ j ih =>
    intro hj
    obtain ⟨hlen, hinv⟩ := ih (by omega)
    have hend := inv_runTo H2 hq ho hinv q.m le_rfl
    have hlen' : (q.runChecks orcA orcB (j + 1)).length = j + 1 := by rw [runChecks_succ, List.length_append, hlen]; rfl
    refine ⟨hlen', by rw [hlen']; exact hj, fun L hL => ?_, chkOK_nil 0, Nat.zero_le _, ?_⟩
    · rw [runChecks_succ] at hL
      rcases List.mem_append.1 hL with h | h
      · exact hinv.done L h
      · rw [List.mem_singleton.1 h]; exact hend.okc
    · have hb := H2.boundary X (Fin q.m) V q.nb q.r (q.runChecks orcA orcB j).length
        (lam q.m (q.runChecks orcA orcB j ++ [q.runTo orcA orcB (q.runChecks orcA orcB j) q.m])) hq.nb_two
        (by have := isState q hend.lt hend.okc; rwa [Dset_self] at this) (by rw [hlen]; exact hj)
      have e1 : UU q V (q.runChecks orcA orcB (j + 1)) [] 0 = Ups V q.nb q.r ((q.runChecks orcA orcB j).length + 1)
          (lam q.m (q.runChecks orcA orcB j ++ [q.runTo orcA orcB (q.runChecks orcA orcB j) q.m])) univ := by
        unfold UU
        rw [lam_append_nil, Dset_zero, hlen', hlen, runChecks_succ]
      have e2 : UU q V (q.runChecks orcA orcB j) (q.runTo orcA orcB (q.runChecks orcA orcB j) q.m) q.m = Ups V q.nb q.r (q.runChecks orcA orcB j).length
          (lam q.m (q.runChecks orcA orcB j ++ [q.runTo orcA orcB (q.runChecks orcA orcB j) q.m])) ∅ := by
        unfold UU
        rw [Dset_self]
      have hp := hend.pot
      rw [e2] at hp
      rw [e1, hlen']
      have hc : (((j + 1) * q.m + 0 : ℕ) : ℚ) = (((q.runChecks orcA orcB j).length * q.m + q.m : ℕ) : ℚ) := by rw [hlen]; push_cast; ring
      rw [hc]
      exact hb.trans hp
end ClauseBound.ParityChecks.Run
