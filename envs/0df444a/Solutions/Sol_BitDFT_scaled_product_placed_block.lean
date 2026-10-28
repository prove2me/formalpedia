-- Prove2me | solution 1 for BitDFT.scaled_product_placed_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T23:17:32.759926+00:00
-- url     : https://prove2.me/submissions/24c80583-c45a-4ffc-8d46-94dc0f4f2106

import Definitions.Def_BitDFT_SignedBlockPlacement
import Theorems.Thm_BitDFT_counted_block_correct
import Theorems.Thm_BitDFT_signed_block_correct
import Theorems.Thm_BitDFT_work_relocation_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
import Theorems.Thm_BitDFT_alphabet_embedding_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_tape_permutation_run
import Mathlib.Tactic

set_option autoImplicit false
open IntMul BitDFT.MachineSequence

private theorem block_run (c : BitDFT.SignedBlock.storage.Cfg) (t : ℕ) :
    BitDFT.SignedBlock.blockControl.machine.step^[t]
        (BitDFT.SignedBlock.blockFrame c) =
      BitDFT.SignedBlock.blockFrame (BitDFT.SignedBlock.storage.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    rfl

private theorem right_run {M : MultitapeTM} (P Q : Controller M)
    (c : Q.machine.Cfg) (t : ℕ) :
    (BitDFT.MachineSequence.sequence P Q).machine.step^[t]
        (BitDFT.MachineSequence.rightCfg P Q c) =
      BitDFT.MachineSequence.rightCfg P Q (Q.machine.step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    rw [show t + 1 = Nat.succ t by omega, Function.iterate_succ_apply']
    rfl

theorem solution (N : MultitapeTM) (k : ℕ)
    (cells : Fin (5+(k+3)) → ℕ → N.Sym) (heads : Fin (5+(k+3)) → ℕ)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (pre out : List Bool) (sign : Bool) (x descriptor : List Bool)
    (hx : val descriptor + 1 ≤ x.length) :
    ∃ t : ℕ, t ≤ 6*(val descriptor+1)+4*descriptor.length+2 ∧
      (BitDFT.SignedBlockPlacement.machine N k).step^[t]
        (BitDFT.SignedBlockPlacement.embed N k cells heads
          (BitDFT.WorkRelocation.embed BitDFT.SignedBlock.machine rootCells rootHead
            (BitDFT.MachineSequence.rightCfg BitDFT.SignedBlock.signControl
              BitDFT.SignedBlock.blockControl
              (BitDFT.SignedBlock.blockFrame
                (BitDFT.CountedBlock.frame pre (out++[sign]) x descriptor
                  descriptor.reverse 0 .emit))))) =
      BitDFT.SignedBlockPlacement.embed N k cells heads
        (BitDFT.WorkRelocation.embed BitDFT.SignedBlock.machine rootCells rootHead
          (BitDFT.MachineSequence.rightCfg BitDFT.SignedBlock.signControl
            BitDFT.SignedBlock.blockControl
            (BitDFT.SignedBlock.blockFrame
              (BitDFT.CountedBlock.frame pre (out++[sign]) x descriptor
                descriptor.reverse (val descriptor+1) .halt)))) := by
  obtain ⟨t, ht, hcount⟩ := BitDFT.counted_block_correct pre (out++[sign]) x descriptor hx
  let c0 : BitDFT.SignedBlock.machine.Cfg :=
    BitDFT.MachineSequence.rightCfg BitDFT.SignedBlock.signControl
      BitDFT.SignedBlock.blockControl
      (BitDFT.SignedBlock.blockFrame
        (BitDFT.CountedBlock.frame pre (out++[sign]) x descriptor descriptor.reverse 0 .emit))
  let c1 : BitDFT.SignedBlock.machine.Cfg :=
    BitDFT.MachineSequence.rightCfg BitDFT.SignedBlock.signControl
      BitDFT.SignedBlock.blockControl
      (BitDFT.SignedBlock.blockFrame
        (BitDFT.CountedBlock.frame pre (out++[sign]) x descriptor descriptor.reverse
          (val descriptor+1) .halt))
  have hblock : BitDFT.SignedBlock.machine.step^[t] c0 = c1 := by
    rw [right_run BitDFT.SignedBlock.signControl BitDFT.SignedBlock.blockControl]
    rw [block_run]
    exact congrArg (BitDFT.MachineSequence.rightCfg BitDFT.SignedBlock.signControl
      BitDFT.SignedBlock.blockControl)
      (congrArg BitDFT.SignedBlock.blockFrame hcount)
  let storage0 := BitDFT.WorkRelocation.embed BitDFT.SignedBlock.machine
    rootCells rootHead c0
  let storage1 := BitDFT.WorkRelocation.embed BitDFT.SignedBlock.machine
    rootCells rootHead c1
  have hstorage :
      BitDFT.SignedBlockPlacement.storage.step^[t] storage0 = storage1 := by
    have hr := (BitDFT.work_relocation_correct BitDFT.SignedBlock.machine
      rootCells rootHead c0 t).1
    rw [hblock] at hr
    simpa [storage0, storage1, BitDFT.SignedBlockPlacement.storage] using hr
  have houter :
      (BitDFT.SignedBlockPlacement.machine N k).step^[t]
        (BitDFT.SignedBlockPlacement.embed N k cells heads storage0) =
      BitDFT.SignedBlockPlacement.embed N k cells heads storage1 := by
    unfold BitDFT.SignedBlockPlacement.embed
    rw [BitDFT.tape_permutation_run,
      (BitDFT.tape_extension_correct (BitDFT.SignedBlockPlacement.lifted N) (k+3)).1,
      (BitDFT.alphabet_embedding_correct BitDFT.SignedBlockPlacement.storage N
        (BitDFT.SignedBlockPlacement.alphabetMap N)).1,
      hstorage]
  refine ⟨t, ht, ?_⟩
  simpa [c0, c1, storage0, storage1] using houter
