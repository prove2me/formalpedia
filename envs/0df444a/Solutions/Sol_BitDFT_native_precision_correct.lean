-- Prove2me | solution 1 for BitDFT.native_precision_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:14:07.108073+00:00
-- url     : https://prove2.me/submissions/f7c08cad-b2d3-4485-8255-c736bd038785

import Definitions.Def_BitDFT_NativePrecision
import Theorems.Thm_BitDFT_request_headers_correct
import Theorems.Thm_BitDFT_parsed_precision_correct
import Theorems.Thm_BitDFT_machine_sequence_bound

noncomputable section
namespace BitDFT.NativePrecision
open IntMul MachineSequence

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem handoff_correct (x tail w : List Bool) :
    handoff (native RequestHeaders.machine) precisionControl (RequestHeaders.final x (true::tail) w) =
      ParsedPrecision.initial (caller x (true::tail) w) tail w := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [handoff,RequestHeaders.final,rightCfg,ParsedPrecision.initial,leftCfg,
      ParsedPrecision.setupInitial,HeaderSetup.frame,ParsedPrecision.setupBase,caller,
      RequestHeaders.secondFinished,TapeExtension.embed,HeaderOffsets.finished,
      MachineSequence.stopCfg,HeaderOffsets.rawFinished] <;> rfl
  · funext i
    fin_cases i <;> simp [handoff,RequestHeaders.final,rightCfg,ParsedPrecision.initial,leftCfg,
      ParsedPrecision.setupInitial,HeaderSetup.frame,ParsedPrecision.setupBase,caller,
      RequestHeaders.secondFinished,TapeExtension.embed,HeaderOffsets.finished,
      MachineSequence.stopCfg,HeaderOffsets.rawFinished]

end BitDFT.NativePrecision
open BitDFT BitDFT.NativePrecision IntMul

theorem solution (tail w rest : List Bool) (hb : 1 ≤ IntMul.val w) (hw : w.length ≤ IntMul.val w) :
    let x := RequestHeaders.header (true::tail) ++ RequestHeaders.header w ++ rest
    let q := guardPrecision (IntMul.val (true::tail)) (IntMul.val w)
    ∃ t v, t ≤ 7*q+3*tail.length+4*w.length+18 ∧ BinaryCounter.value v = q ∧ v.length ≤ q ∧
      machine.step^[t] (machine.initCfg x []) = final x tail w v := by
  dsimp only
  let x := RequestHeaders.header (true::tail) ++ RequestHeaders.header w ++ rest
  obtain ⟨s,hs,hr⟩ := BitDFT.request_headers_correct (true::tail) w rest
  obtain ⟨u,v,hu,hv,hlen,hp⟩ := BitDFT.parsed_precision_correct (caller x (true::tail) w) tail w hb hw
  have hh : ((MachineSequence.native RequestHeaders.machine).machine.step^[s]
      (RequestHeaders.machine.initCfg x [])).state = (MachineSequence.native RequestHeaders.machine).exit := by
    change (RequestHeaders.machine.step^[s] (RequestHeaders.machine.initCfg x [])).state = _
    rw [hr]; rfl
  obtain ⟨t,ht,he⟩ := BitDFT.machine_sequence_bound (MachineSequence.native RequestHeaders.machine) precisionControl
    (RequestHeaders.machine.initCfg x []) s u hh
  change machine.step^[t] (machine.initCfg x []) =
    MachineSequence.rightCfg (MachineSequence.native RequestHeaders.machine) precisionControl
      (ParsedPrecision.machine.step^[u]
        (MachineSequence.handoff (MachineSequence.native RequestHeaders.machine) precisionControl
          (RequestHeaders.machine.step^[s] (RequestHeaders.machine.initCfg x [])))) at he
  rw [hr,handoff_correct,hp] at he
  refine ⟨t,v,?_,hv,hlen,he⟩
  simp only [List.length_cons] at hs
  omega
