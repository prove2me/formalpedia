-- Prove2me | solution 1 for BitDFT.rewound_descriptor_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:12:21.368119+00:00
-- url     : https://prove2.me/submissions/98f2608b-bfce-4c7d-a5ce-28b7874ac39c

import Definitions.Def_BitDFT_RewoundDescriptor
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_descriptor_setup_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Mathlib.Tactic
open BitDFT IntMul MachineSequence

private theorem correct_handoff (base : RewoundDescriptor.storage.Cfg) (y : List Bool) :
    handoff RewoundDescriptor.rewind RewoundDescriptor.copy
      (RewindTape.frame RewoundDescriptor.storage 1 (DescriptorSetup.initial base y) true 1) =
      DescriptorSetup.initial base y := by
  have hhead : Function.update (DescriptorSetup.initial base y).head 1 1 =
      (DescriptorSetup.initial base y).head := by
    simpa [DescriptorSetup.initial] using
      Function.update_eq_self 1 (DescriptorSetup.initial base y).head
  change IntMul.MultitapeTM.Cfg.mk _ _ (Function.update _ 1 1) = _
  rw [hhead]
  rfl

theorem solution (base : RewoundDescriptor.storage.Cfg) (y : List Bool) :
    ∃ t : ℕ, t ≤ 2*y.length+6 ∧
      RewoundDescriptor.machine.step^[t] (RewoundDescriptor.initial base y) =
        RewoundDescriptor.final base y := by
  have hz : (DescriptorSetup.initial base y).cells 1 0 = RewoundDescriptor.storage.startSym := by
    simp [DescriptorSetup.initial,MultitapeTM.tapeOf]
  have hn : ∀ p, 0 < p → (DescriptorSetup.initial base y).cells 1 p ≠ RewoundDescriptor.storage.startSym := by
    intro p hp
    cases p with
    | zero => omega
    | succ p =>
      simp only [DescriptorSetup.initial,ite_true,MultitapeTM.tapeOf,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases h : y[p]? with
      | none => simp [h,RewoundDescriptor.storage]
      | some b => cases b <;> simp [h,MultitapeTM.bitSym,RewoundDescriptor.storage]
  have hr := BitDFT.rewind_tape_correct RewoundDescriptor.storage 1
    (DescriptorSetup.initial base y) hz hn (y.length+1)
  have hhalt : (RewoundDescriptor.rewind.machine.step^[y.length+2]
      (RewindTape.frame RewoundDescriptor.storage 1 (DescriptorSetup.initial base y) false (y.length+1))).state =
      RewoundDescriptor.rewind.exit := by
    rw [show y.length+2 = (y.length+1)+1 by omega,hr]
    rfl
  obtain ⟨t,ht,he⟩ := BitDFT.machine_sequence_bound RewoundDescriptor.rewind RewoundDescriptor.copy
    (RewindTape.frame RewoundDescriptor.storage 1 (DescriptorSetup.initial base y) false (y.length+1))
    (y.length+2) (y.length+3) hhalt
  refine ⟨t,by omega,?_⟩
  change RewoundDescriptor.machine.step^[t] (RewoundDescriptor.initial base y) = _ at he
  rw [show y.length+2 = (y.length+1)+1 by omega,hr,correct_handoff] at he
  change RewoundDescriptor.machine.step^[t] (RewoundDescriptor.initial base y) =
    rightCfg RewoundDescriptor.rewind RewoundDescriptor.copy
      (DescriptorSetup.machine.step^[y.length+3] (DescriptorSetup.initial base y)) at he
  rw [BitDFT.descriptor_setup_correct] at he
  exact he
