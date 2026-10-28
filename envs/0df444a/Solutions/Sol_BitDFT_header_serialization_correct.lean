-- Prove2me | solution 1 for BitDFT.header_serialization_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:32:32.780304+00:00
-- url     : https://prove2.me/submissions/a15122ce-f37b-4304-8d2c-622d4ccef649

import Definitions.Def_BitDFT_HeaderSerialization
import Theorems.Thm_BitDFT_serialize_field_correct
import Theorems.Thm_BitDFT_trim_reverse_correct
import Theorems.Thm_BitDFT_tape_permutation_run
import Theorems.Thm_BitDFT_machine_sequence_bound

noncomputable section
namespace BitDFT.HeaderSerialization
open IntMul MachineSequence

private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem first_run (base : storage.Cfg) (n w out : List Bool) :
    storage.step^[2*n.length+3] (firstInitial base n w out) = firstFinished base n w out := by
  simpa [firstInitial,firstFinished,header,List.append_assoc] using
    BitDFT.serialize_field_correct (inputBase base w) n out

theorem first_handoff (base : storage.Cfg) (n w out : List Bool) :
    handoff (native storage) restControl (firstFinished base n w out) =
      leftCfg trimControl precisionControl (TrimReverse.initial (trimBase base n w out) w) := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [handoff,leftCfg,TrimReverse.initial,TrimReverse.frame,
      trimBase,firstFinished,SerializeField.frame,inputBase] <;> rfl
  · funext i
    fin_cases i <;> simp [handoff,leftCfg,TrimReverse.initial,TrimReverse.frame,
      trimBase,firstFinished,SerializeField.frame,inputBase]

theorem precision_handoff (base : storage.Cfg) (n w out : List Bool) :
    handoff trimControl precisionControl (trimmed base n w out) = precisionInitial base n w out := by
  apply cfg_ext
  · rfl
  · funext i
    fin_cases i <;> simp [handoff,precisionInitial,serializerBase,TapePermutation.embed,
      swap34,Equiv.swap_apply_def,trimmed,TrimReverse.frame,trimBase,firstFinished,
      SerializeField.frame,inputBase] <;> rfl
  · funext i
    fin_cases i <;> simp [handoff,precisionInitial,serializerBase,TapePermutation.embed,
      swap34,Equiv.swap_apply_def,trimmed,TrimReverse.frame,trimBase,firstFinished,
      SerializeField.frame,inputBase]

theorem precision_run (base : storage.Cfg) (n w out : List Bool) :
    precisionControl.machine.step^[2*(BinaryCounter.value w).size+3] (precisionInitial base n w out) =
      precisionFinished base n w out := by
  change routed.step^[_] _ = _
  unfold precisionInitial precisionFinished
  rw [BitDFT.tape_permutation_run]
  have h := BitDFT.serialize_field_correct (serializerBase base n w out)
    (bin (BinaryCounter.value w).size (BinaryCounter.value w)) (out++header n)
  simp only [bin,List.length_ofFn] at h
  simpa [header,bin,List.append_assoc] using congrArg (TapePermutation.embed storage swap34 (by decide)) h

end BitDFT.HeaderSerialization
open BitDFT BitDFT.HeaderSerialization IntMul

theorem solution (base : storage.Cfg) (n w out : List Bool) (hw : 0 < BinaryCounter.value w) :
    ∃ t, t ≤ 2*n.length+2*w.length+2*(BinaryCounter.value w).size+12 ∧
      machine.step^[t] (initial base n w out) = final base n w out := by
  have hr : trimControl.machine.step^[2*w.length+4] (TrimReverse.initial (trimBase base n w out) w) =
      trimmed base n w out := by
    change TrimReverse.machine.step^[_] _ = _
    exact BitDFT.trim_reverse_correct (trimBase base n w out) w hw
  have hh : (trimControl.machine.step^[2*w.length+4] (TrimReverse.initial (trimBase base n w out) w)).state = trimControl.exit := by
    rw [hr]; rfl
  obtain ⟨u,hu,he⟩ := BitDFT.machine_sequence_bound trimControl precisionControl
    (TrimReverse.initial (trimBase base n w out) w) (2*w.length+4) (2*(BinaryCounter.value w).size+3) hh
  rw [hr,precision_handoff,precision_run] at he
  have hf := first_run base n w out
  have hhalt : ((MachineSequence.native storage).machine.step^[2*n.length+3] (firstInitial base n w out)).state =
      (MachineSequence.native storage).exit := by
    change (storage.step^[_] _).state = _
    rw [hf]; rfl
  obtain ⟨t,ht,he'⟩ := BitDFT.machine_sequence_bound (MachineSequence.native storage) restControl
    (firstInitial base n w out) (2*n.length+3) u hhalt
  change machine.step^[t] (initial base n w out) =
    MachineSequence.rightCfg (MachineSequence.native storage) restControl
      (restControl.machine.step^[u]
        (MachineSequence.handoff (MachineSequence.native storage) restControl
          (storage.step^[2*n.length+3] (firstInitial base n w out)))) at he'
  rw [hf,first_handoff,he] at he'
  exact ⟨t,by omega,he'⟩
