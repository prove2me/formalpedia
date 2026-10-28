-- Prove2me | solution 1 for BitDFT.parsed_precision_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:06:49.638209+00:00
-- url     : https://prove2.me/submissions/15de2263-e7ff-4776-88ac-37f4c55d8823

import Definitions.Def_BitDFT_ParsedPrecision
import Theorems.Thm_BitDFT_header_setup_correct
import Theorems.Thm_BitDFT_precision_program_correct
import Theorems.Thm_BitDFT_machine_sequence_bound

namespace BitDFT.ParsedPrecision
open IntMul MachineSequence

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

def setupFinished (base : PrecisionProgram.arithmetic.Cfg) (tail w : List Bool) : setupControl.machine.Cfg where
  state := .halt
  cells := (HeaderSetup.frame (setupBase base) .halt [] w.reverse (true::tail) 1 1 1).cells
  head := (HeaderSetup.frame (setupBase base) .halt [] w.reverse (true::tail) 1 1 1).head

theorem setup_correct (base : PrecisionProgram.arithmetic.Cfg) (tail w : List Bool) :
    setupControl.machine.step^[2*w.length+tail.length+5] (setupInitial base tail w) =
      setupFinished base tail w := by
  have h := BitDFT.header_setup_correct (setupBase base) w (true::tail)
  change HeaderSetup.machine.step^[2*w.length+tail.length+5]
    (HeaderSetup.frame (setupBase base) .start w [] (true::tail) 0 (w.length+1) (tail.length+2)) =
    HeaderSetup.frame (setupBase base) .halt [] w.reverse (true::tail) 1 1 1
  simpa only [List.length_cons,Nat.add_assoc] using h

theorem handoff_correct (base : PrecisionProgram.arithmetic.Cfg) (tail w : List Bool) :
    handoff setupControl (native PrecisionProgram.machine) (setupFinished base tail w) =
      PrecisionProgram.initial base tail w := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [handoff,setupFinished,HeaderSetup.frame,setupBase,
      PrecisionProgram.initial,leftCfg,PrecisionProgram.scanInitial,
      TapePermutation.embed,TapeExtension.embed,LogScanner.frame,
      PrecisionProgram.base4,PrecisionProgram.swap24,Equiv.swap_apply_def,TapeExtension.oldTape] <;> rfl
  · funext i
    fin_cases i <;> simp [handoff,setupFinished,HeaderSetup.frame,setupBase,
      PrecisionProgram.initial,leftCfg,PrecisionProgram.scanInitial,
      TapePermutation.embed,TapeExtension.embed,LogScanner.frame,
      PrecisionProgram.base4,PrecisionProgram.swap24,Equiv.swap_apply_def,TapeExtension.oldTape] <;> rfl

end BitDFT.ParsedPrecision
open BitDFT BitDFT.ParsedPrecision IntMul

theorem solution (base : PrecisionProgram.arithmetic.Cfg) (tail w : List Bool)
    (hb : 1 ≤ IntMul.val w) (hw : w.length ≤ IntMul.val w) :
    let q := guardPrecision (IntMul.val (true::tail)) (IntMul.val w)
    ∃ t v, t ≤ 7*q+2*w.length+tail.length+6 ∧ BinaryCounter.value v = q ∧ v.length ≤ q ∧
      machine.step^[t] (initial base tail w) = final base tail v := by
  dsimp only
  obtain ⟨u,v,hu,hv,hlen,hr⟩ := BitDFT.precision_program_correct base tail w hb hw
  have hs := setup_correct base tail w
  have hh : (setupControl.machine.step^[2*w.length+tail.length+5] (setupInitial base tail w)).state = setupControl.exit := by
    rw [hs]; rfl
  obtain ⟨t,ht,he⟩ := BitDFT.machine_sequence_bound setupControl (MachineSequence.native PrecisionProgram.machine)
    (setupInitial base tail w) (2*w.length+tail.length+5) u hh
  rw [hs,handoff_correct] at he
  change machine.step^[t] (initial base tail w) =
    MachineSequence.rightCfg setupControl (MachineSequence.native PrecisionProgram.machine)
      (PrecisionProgram.machine.step^[u] (PrecisionProgram.initial base tail w)) at he
  rw [hr] at he
  exact ⟨t,v,by omega,hv,hlen,he⟩
