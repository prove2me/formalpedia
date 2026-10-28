-- Prove2me | solution 1 for BitDFT.MachineSequence.branchController_run_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T22:03:40.111349+00:00
-- url     : https://prove2.me/submissions/d3252be5-a017-4b52-9d23-a48980b68253

import Definitions.Def_BitDFT_BranchController
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0

namespace BitDFT.MachineSequence
open IntMul

theorem branchController_select_left {M : MultitapeTM} (source : Fin M.k)
    (test : M.Sym → Bool) (P Q : Controller M) (c : P.machine.Cfg)
    (hentry : c.state = P.entry)
    (h : test (c.cells source (c.head source)) = true) :
    (branchController source test P Q).machine.step
      (⟨Sum.inl (), c.cells, c.head⟩ : (branchController source test P Q).machine.Cfg) =
      branchLeftCfg c := by
  cases c with
  | mk state cells head =>
    change state = P.entry at hentry
    subst state
    simp [branchController, branchLeftCfg, Controller.machine, MultitapeTM.step, h]

theorem branchController_select_right {M : MultitapeTM} (source : Fin M.k)
    (test : M.Sym → Bool) (P Q : Controller M) (c : Q.machine.Cfg)
    (hentry : c.state = Q.entry)
    (h : test (c.cells source (c.head source)) = false) :
    (branchController source test P Q).machine.step
      (⟨Sum.inl (), c.cells, c.head⟩ : (branchController source test P Q).machine.Cfg) =
      branchRightCfg c := by
  cases c with
  | mk state cells head =>
    change state = Q.entry at hentry
    subst state
    simp [branchController, branchRightCfg, Controller.machine, MultitapeTM.step, h]

theorem branchController_left_step {M : MultitapeTM} (source : Fin M.k)
    (test : M.Sym → Bool) (P Q : Controller M) (c : P.machine.Cfg)
    (h : c.state ≠ P.exit) :
    (branchController source test P Q).machine.step (branchLeftCfg c) =
      branchLeftCfg (P.machine.step c) := by
  simp [branchController, branchLeftCfg, Controller.machine, MultitapeTM.step, h]

theorem branchController_right_step {M : MultitapeTM} (source : Fin M.k)
    (test : M.Sym → Bool) (P Q : Controller M) (c : Q.machine.Cfg)
    (h : c.state ≠ Q.exit) :
    (branchController source test P Q).machine.step (branchRightCfg c) =
      branchRightCfg (Q.machine.step c) := by
  simp [branchController, branchRightCfg, Controller.machine, MultitapeTM.step, h]

theorem branchController_left_exit {M : MultitapeTM} (source : Fin M.k)
    (test : M.Sym → Bool) (P Q : Controller M) (c : P.machine.Cfg)
    (h : c.state = P.exit) :
    (branchController source test P Q).machine.step (branchLeftCfg c) =
      branchDoneCfg (source := source) (test := test) (P := P) (Q := Q)
        c.cells c.head := by
  cases c with
  | mk state cells head =>
    change state = P.exit at h
    subst state
    simp [branchController, branchLeftCfg, branchDoneCfg, Controller.machine,
      MultitapeTM.step]

theorem branchController_right_exit {M : MultitapeTM} (source : Fin M.k)
    (test : M.Sym → Bool) (P Q : Controller M) (c : Q.machine.Cfg)
    (h : c.state = Q.exit) :
    (branchController source test P Q).machine.step (branchRightCfg c) =
      branchDoneCfg (source := source) (test := test) (P := P) (Q := Q)
        c.cells c.head := by
  cases c with
  | mk state cells head =>
    change state = Q.exit at h
    subst state
    simp [branchController, branchRightCfg, branchDoneCfg, Controller.machine,
      MultitapeTM.step]

private theorem branchController_left_run_local {M : MultitapeTM} (source : Fin M.k)
    (test : M.Sym → Bool) (P Q : Controller M) (t : ℕ) (c : P.machine.Cfg)
    (hfirst : ∀ s < t, (P.machine.step^[s] c).state ≠ P.exit) :
    (branchController source test P Q).machine.step^[t] (branchLeftCfg c) =
      branchLeftCfg (P.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hsub : ∀ s < t, (P.machine.step^[s] c).state ≠ P.exit := by
        intro s hs
        exact hfirst s (by omega)
      have hstate : (P.machine.step^[t] c).state ≠ P.exit := hfirst t (by omega)
      calc
        (branchController source test P Q).machine.step^[(t + 1)] (branchLeftCfg c) =
            (branchController source test P Q).machine.step
              ((branchController source test P Q).machine.step^[t] (branchLeftCfg c)) := by
                rw [Function.iterate_succ_apply']
        _ = (branchController source test P Q).machine.step
              (branchLeftCfg (P.machine.step^[t] c)) := by rw [ih hsub]
        _ = branchLeftCfg (P.machine.step (P.machine.step^[t] c)) :=
              branchController_left_step source test P Q _ hstate
        _ = branchLeftCfg (P.machine.step^[(t + 1)] c) := by
              rw [Function.iterate_succ_apply']

private theorem branchController_right_run_local {M : MultitapeTM} (source : Fin M.k)
    (test : M.Sym → Bool) (P Q : Controller M) (t : ℕ) (c : Q.machine.Cfg)
    (hfirst : ∀ s < t, (Q.machine.step^[s] c).state ≠ Q.exit) :
    (branchController source test P Q).machine.step^[t] (branchRightCfg c) =
      branchRightCfg (Q.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hsub : ∀ s < t, (Q.machine.step^[s] c).state ≠ Q.exit := by
        intro s hs
        exact hfirst s (by omega)
      have hstate : (Q.machine.step^[t] c).state ≠ Q.exit := hfirst t (by omega)
      calc
        (branchController source test P Q).machine.step^[(t + 1)] (branchRightCfg c) =
            (branchController source test P Q).machine.step
              ((branchController source test P Q).machine.step^[t] (branchRightCfg c)) := by
                rw [Function.iterate_succ_apply']
        _ = (branchController source test P Q).machine.step
              (branchRightCfg (Q.machine.step^[t] c)) := by rw [ih hsub]
        _ = branchRightCfg (Q.machine.step (Q.machine.step^[t] c)) :=
              branchController_right_step source test P Q _ hstate
        _ = branchRightCfg (Q.machine.step^[(t + 1)] c) := by
              rw [Function.iterate_succ_apply']

theorem branchController_run_left {M : MultitapeTM} (source : Fin M.k)
    (test : M.Sym → Bool) (P Q : Controller M) (t : ℕ) (c : P.machine.Cfg)
    (hentry : c.state = P.entry)
    (hselect : test (c.cells source (c.head source)) = true)
    (hfirst : ∀ s < t, (P.machine.step^[s] c).state ≠ P.exit)
    (hexit : (P.machine.step^[t] c).state = P.exit) :
    (branchController source test P Q).machine.step^[(t+2)]
      (branchChooseCfg c.cells c.head) =
        branchDoneCfg (source := source) (test := test) (P := P) (Q := Q)
          (P.machine.step^[t] c).cells (P.machine.step^[t] c).head := by
  have hchoose : (branchController source test P Q).machine.step
      (branchChooseCfg c.cells c.head) = branchLeftCfg c := by
    exact branchController_select_left source test P Q c hentry hselect
  calc
    (branchController source test P Q).machine.step^[(t+2)]
        (branchChooseCfg c.cells c.head) =
      (branchController source test P Q).machine.step^[(t+1)]
        ((branchController source test P Q).machine.step
          (branchChooseCfg c.cells c.head)) := by
            rw [show t+2 = (t+1)+1 by omega, Function.iterate_add_apply,
              Function.iterate_one]
    _ = (branchController source test P Q).machine.step^[(t+1)] (branchLeftCfg c) := by
          rw [hchoose]
    _ = (branchController source test P Q).machine.step
          (branchLeftCfg (P.machine.step^[t] c)) := by
          rw [Function.iterate_succ_apply', branchController_left_run_local source test P Q t c hfirst]
    _ = branchDoneCfg (source := source) (test := test) (P := P) (Q := Q)
          (P.machine.step^[t] c).cells (P.machine.step^[t] c).head :=
          branchController_left_exit source test P Q _ hexit


end BitDFT.MachineSequence
open BitDFT.MachineSequence IntMul
theorem solution {M : MultitapeTM} (source : Fin M.k)
    (test : M.Sym → Bool) (P Q : Controller M) (t : ℕ) (c : Q.machine.Cfg)
    (hentry : c.state = Q.entry)
    (hselect : test (c.cells source (c.head source)) = false)
    (hfirst : ∀ s < t, (Q.machine.step^[s] c).state ≠ Q.exit)
    (hexit : (Q.machine.step^[t] c).state = Q.exit) :
    (branchController source test P Q).machine.step^[(t+2)]
      (branchChooseCfg c.cells c.head) =
        branchDoneCfg (source := source) (test := test) (P := P) (Q := Q)
          (Q.machine.step^[t] c).cells (Q.machine.step^[t] c).head := by
  have hchoose : (branchController source test P Q).machine.step
      (branchChooseCfg c.cells c.head) = branchRightCfg c := by
    exact branchController_select_right source test P Q c hentry hselect
  calc
    (branchController source test P Q).machine.step^[(t+2)]
        (branchChooseCfg c.cells c.head) =
      (branchController source test P Q).machine.step^[(t+1)]
        ((branchController source test P Q).machine.step
          (branchChooseCfg c.cells c.head)) := by
            rw [show t+2 = (t+1)+1 by omega, Function.iterate_add_apply,
              Function.iterate_one]
    _ = (branchController source test P Q).machine.step^[(t+1)] (branchRightCfg c) := by
          rw [hchoose]
    _ = (branchController source test P Q).machine.step
          (branchRightCfg (Q.machine.step^[t] c)) := by
          rw [Function.iterate_succ_apply', branchController_right_run_local source test P Q t c hfirst]
    _ = branchDoneCfg (source := source) (test := test) (P := P) (Q := Q)
          (Q.machine.step^[t] c).cells (Q.machine.step^[t] c).head :=
          branchController_right_exit source test P Q _ hexit
