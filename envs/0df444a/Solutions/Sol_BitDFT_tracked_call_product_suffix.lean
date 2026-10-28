-- Prove2me | solution 1 for BitDFT.tracked_call_product_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T06:06:30.334379+00:00
-- url     : https://prove2.me/submissions/015af9eb-9db9-4d4b-8cfa-33099005c9e1

import Definitions.Def_IntMul_TrackedBankedCall
import Definitions.Def_IntMul_TrackedOutputShift
import Definitions.Def_BitDFT_RewindTape
import Definitions.Def_BitDFT_BitAdvance
import Definitions.Def_BitDFT_MachineSequence
import Definitions.Def_BitDFT_LiftController
import Theorems.Thm_BitDFT_banked_call_output_shift
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_BitAdvance_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Mathlib.Tactic

set_option autoImplicit false
open IntMul BitDFT BitDFT.MachineSequence

private theorem cfg_ext {N : MultitapeTM} (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem rewind_then_bit_advance_local
    (N : MultitapeTM) (source counter : Fin N.k) (hsc : source ≠ counter)
    (base : N.Cfg) (p L counterHead : ℕ)
    (hcounter : base.head counter = counterHead)
    (hmarker : base.cells source 0 = N.startSym)
    (hsource : ∀ r, 0 < r → base.cells source r ≠ N.startSym)
    (hbits : ∀ r, r < L → base.cells counter (counterHead+r) = N.zero ∨
      base.cells counter (counterHead+r) = N.one)
    (hstop : base.cells counter (counterHead+L) ≠ N.zero ∧
      base.cells counter (counterHead+L) ≠ N.one) :
    ∃ t : ℕ, t ≤ p+L+3 ∧
      (MachineSequence.sequence (RewindTape.control N source)
        (BitAdvance.control N source counter hsc)).machine.step^[t]
        (MachineSequence.leftCfg (RewindTape.control N source)
          (BitAdvance.control N source counter hsc)
          (RewindTape.frame N source base false p)) =
      MachineSequence.rightCfg (RewindTape.control N source)
        (BitAdvance.control N source counter hsc)
        (BitAdvance.frame N source counter hsc base true (L+1) (counterHead+L)) := by
  let P := RewindTape.control N source
  let Q := BitAdvance.control N source counter hsc
  let c₀ := RewindTape.frame N source base false p
  have hrew := BitDFT.rewind_tape_correct N source base hmarker hsource p
  have hhalt : (P.machine.step^[p+1] c₀).state = P.exit := by rw [hrew]; rfl
  obtain ⟨t, ht, hseq⟩ := BitDFT.machine_sequence_bound P Q c₀ (p+1) (L+1) hhalt
  have hhandoff : MachineSequence.handoff P Q
      (RewindTape.frame N source base true 1) =
      BitAdvance.frame N source counter hsc base false 1 counterHead := by
    apply cfg_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i = counter
      · subst i
        have hcs : counter ≠ source := Ne.symm hsc
        simp [MachineSequence.handoff, RewindTape.frame, BitAdvance.frame,
          Function.update, hcs, hcounter]
      · simp [MachineSequence.handoff, RewindTape.frame, BitAdvance.frame,
          Function.update, hi, hcounter]
  have hadv := BitDFT.BitAdvance.correct N source counter hsc base L 1 counterHead hbits hstop
  rw [hrew, hhandoff, hadv] at hseq
  refine ⟨t, ?_, ?_⟩
  · omega
  · simpa [P, Q, c₀, Nat.add_comm] using hseq

/-- A real tracked multiplier return, followed by its output normalizer, can
    be rewound and advanced to the first cell of the serializer's low suffix.
    The counter bits are read from a distinct preserved caller tape. -/
theorem solution (M : MultitapeTM)
    (base : (TrackedBankedCall.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (productWord : List Bool)
    (counter : Fin (TrackedOutputShift.machine M).k)
    (hcounterProduct : counter ≠ ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩)
    (counterHead p L : ℕ)
    (hp : p = productWord.length + 1)
    (hcounterHead :
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).head counter = counterHead)
    (hmarker :
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).cells
        ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩ 0 =
          (TrackedOutputShift.machine M).startSym)
    (hbits : ∀ r, r < L →
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).cells counter
        (counterHead+r) = (TrackedOutputShift.machine M).zero ∨
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).cells counter
        (counterHead+r) = (TrackedOutputShift.machine M).one)
    (hstop :
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).cells counter
        (counterHead+L) ≠ (TrackedOutputShift.machine M).zero ∧
      (TrackedBankedCall.finalFrame M base 1 offset extent c productWord).cells counter
        (counterHead+L) ≠ (TrackedOutputShift.machine M).one) :
    ∃ t : ℕ, t ≤ 4*productWord.length+4 + (p+L+3) + 1 ∧
      let callFrame := TrackedBankedCall.finalFrame M base 1 offset extent c productWord
      let shiftStart : (TrackedOutputShift.machine M).Cfg :=
        ⟨.rewind, callFrame.cells, callFrame.head⟩
      let shifted := TrackedOutputShift.finalFrame M shiftStart productWord
      let P := MachineSequence.native (TrackedOutputShift.machine M)
      let Q := RewindTape.control P.machine ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩
      let R := BitAdvance.control P.machine ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩
        counter (Ne.symm hcounterProduct)
      let V := MachineSequence.sequence Q R
      let Vflat := MachineSequence.liftController P V
      (MachineSequence.sequence P Vflat).machine.step^[t]
        (MachineSequence.leftCfg P Vflat shiftStart) =
      MachineSequence.rightCfg P Vflat
        (MachineSequence.rightCfg Q R
          (BitAdvance.frame P.machine ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩
            counter (Ne.symm hcounterProduct) shifted true (L+1) (counterHead+L))) := by
  let product : Fin (TrackedOutputShift.machine M).k := ⟨1, by dsimp [TrackedOutputShift.machine]; omega⟩
  let callFrame := TrackedBankedCall.finalFrame M base 1 offset extent c productWord
  let shiftStart : (TrackedOutputShift.machine M).Cfg := ⟨.rewind, callFrame.cells, callFrame.head⟩
  let shifted := TrackedOutputShift.finalFrame M shiftStart productWord
  let P := MachineSequence.native (TrackedOutputShift.machine M)
  let Q := RewindTape.control P.machine product
  let R := BitAdvance.control P.machine product counter (Ne.symm hcounterProduct)
  let V := MachineSequence.sequence Q R
  let Vflat := MachineSequence.liftController P V
  let cRewind := RewindTape.frame P.machine product shifted false p
  have hshift := BitDFT.banked_call_output_shift M base offset extent c productWord
  have hshiftRun : (P.machine).step^[4*productWord.length+4] shiftStart = shifted := by
    simpa [P, MachineSequence.native, shiftStart, shifted, callFrame] using hshift
  have hhalt : ((P.machine).step^[4*productWord.length+4] shiftStart).state = P.exit := by
    rw [hshiftRun]
    rfl
  have hmarker' : shifted.cells product 0 = P.machine.startSym := by
    change callFrame.cells product 0 = P.machine.startSym at hmarker
    simpa [shifted, TrackedOutputShift.finalFrame, TrackedOutputShift.outputTape,
      shiftStart, callFrame, product, P, MachineSequence.native] using hmarker
  have hsource' : ∀ j, 0 < j → shifted.cells product j ≠ P.machine.startSym := by
    intro j hj
    have hj0 : j ≠ 0 := by omega
    simpa [shifted, TrackedOutputShift.finalFrame, TrackedOutputShift.outputTape,
      shiftStart, product, hj0, P, MachineSequence.native]
  have hcval : counter.val ≠ 1 := by
    intro hv
    apply hcounterProduct
    exact Fin.ext hv
  have hcounterHead' : shifted.head counter = counterHead := by
    simpa [shifted, TrackedOutputShift.finalFrame, hcval] using hcounterHead
  have hbits' : ∀ r, r < L →
      shifted.cells counter (counterHead+r) = P.machine.zero ∨
      shifted.cells counter (counterHead+r) = P.machine.one := by
    intro r hr
    simpa [shifted, TrackedOutputShift.finalFrame, hcval, P,
      MachineSequence.native] using hbits r hr
  have hstop' : shifted.cells counter (counterHead+L) ≠ P.machine.zero ∧
      shifted.cells counter (counterHead+L) ≠ P.machine.one := by
    simpa [shifted, TrackedOutputShift.finalFrame, hcval, P,
      MachineSequence.native] using hstop
  have hrunV := rewind_then_bit_advance_local P.machine product counter
    (Ne.symm hcounterProduct) shifted p L counterHead hcounterHead'
    hmarker' hsource' hbits' hstop'
  obtain ⟨tv, htv, hv⟩ := hrunV
  have hrewindHead : shifted.head product = p := by
    simp [shifted, TrackedOutputShift.finalFrame, product, hp]
  have hhandoff : MachineSequence.handoff P Vflat shifted =
      MachineSequence.leftCfg Q R cRewind := by
    apply cfg_ext
    · rfl
    · rfl
    · funext i
      by_cases hi : i = product
      · subst i
        simp [MachineSequence.handoff, MachineSequence.leftCfg, cRewind,
          RewindTape.frame, hrewindHead]
      · simp [MachineSequence.handoff, MachineSequence.leftCfg, cRewind,
          RewindTape.frame, hi]
  have hhaltV : (Vflat.machine.step^[tv]
      (MachineSequence.leftCfg Q R cRewind)).state = Vflat.exit := by
    rw [show Vflat.machine.step^[tv] (MachineSequence.leftCfg Q R cRewind) =
        MachineSequence.rightCfg Q R
        (BitAdvance.frame P.machine product counter (Ne.symm hcounterProduct)
          shifted true (L+1) (counterHead+L)) by
        simpa [Vflat, MachineSequence.liftController, cRewind] using hv]
    rfl
  obtain ⟨t, ht, htotal⟩ := BitDFT.machine_sequence_bound P Vflat
    shiftStart (4*productWord.length+4) tv hhalt
  rw [hshiftRun, hhandoff] at htotal
  have hrunVflat : Vflat.machine.step^[tv]
      (MachineSequence.leftCfg Q R cRewind) =
      MachineSequence.rightCfg Q R
        (BitAdvance.frame P.machine product counter (Ne.symm hcounterProduct)
          shifted true (L+1) (counterHead+L)) := by
    simpa [Vflat, MachineSequence.liftController, cRewind] using hv
  rw [hrunVflat] at htotal
  refine ⟨t, ?_, ?_⟩
  · omega
  · simpa [P, Q, R, V, Vflat, cRewind, product,
      MachineSequence.native, shifted, shiftStart, callFrame] using htotal
