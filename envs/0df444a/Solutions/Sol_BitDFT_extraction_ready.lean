-- Prove2me | solution 1 for BitDFT.extraction_ready
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:53:43.100697+00:00
-- url     : https://prove2.me/submissions/7c097c4b-dc7a-484f-aafa-cdcb77d7da05

import Definitions.Def_BitDFT_ExtractionReady
import Theorems.Thm_BitDFT_tape_count_transport_correct
import Theorems.Thm_BitDFT_tape_extension_correct
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
namespace BitDFT.ExtractionReady
open IntMul

theorem prepared_run (M : MultitapeTM) (c : (VectorReady.machine M).Cfg) (t : ℕ) :
    (preparation M).step^[t] (prepared M c) =
      prepared M ((VectorReady.machine M).step^[t] c) := by
  unfold prepared
  rw [BitDFT.tape_count_transport_correct,
    (BitDFT.tape_extension_correct (VectorReady.machine M) 1).1]

theorem fresh_tapes (M : MultitapeTM) (c : (VectorReady.machine M).Cfg)
    (i : Fin (5+(M.k+3))) (hi : M.k+7 ≤ i.val) :
    (prepared M c).cells i = (VectorReady.machine M).tapeOf [] ∧
    (prepared M c).head i = 0 := by
  have hn : ¬i.val < (VectorReady.machine M).k := by change ¬i.val < 4+(M.k+3); omega
  simp [prepared,TapeCountTransport.embed,TapeExtension.embed,hn]



private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

private theorem extension_init (M : MultitapeTM) (r : ℕ) (x y : List Bool) :
    (TapeExtension.machine M r).initCfg x y =
      TapeExtension.embed M r (fun _ => M.tapeOf []) (fun _ => 0) (M.initCfg x y) := by
  apply cfg_ext
  · rfl
  · funext i
    by_cases hi : i.val < M.k
    · simp [MultitapeTM.initCfg,MultitapeTM.inTape,TapeExtension.embed,hi,Fin.ext_iff]
      rfl
    · have hz : i.val ≠ 0 := by have := M.two_le_k; omega
      simp [MultitapeTM.initCfg,MultitapeTM.inTape,TapeExtension.embed,hi,Fin.ext_iff,hz]
      rfl
  · funext i; simp [MultitapeTM.initCfg,TapeExtension.embed]

private theorem transport_init (M : MultitapeTM) (n : ℕ) (h : M.k = n) (x y : List Bool) :
    (TapeCountTransport.machine M n h).initCfg x y =
      TapeCountTransport.embed M n h (M.initCfg x y) := by
  subst n
  rfl

theorem prepared_init (M : MultitapeTM) (x y : List Bool) :
    (preparation M).initCfg x y = prepared M ((VectorReady.machine M).initCfg x y) := by
  unfold prepared
  rw [← extension_init,← transport_init]

theorem old_tape (M : MultitapeTM) (c : (VectorReady.machine M).Cfg)
    (j : Fin (VectorReady.machine M).k) :
    let i : Fin (5+(M.k+3)) := ⟨j.val,by have hj : j.val < 4+(M.k+3) := j.isLt; omega⟩
    (prepared M c).cells i = c.cells j ∧ (prepared M c).head i = c.head j := by
  simp [prepared,TapeCountTransport.embed,TapeExtension.embed,j.isLt]


private theorem correct_handoff (M : MultitapeTM) (c : (VectorReady.machine M).Cfg) :
    MachineSequence.handoff (MachineSequence.native (preparation M)) (advance M) (prepared M c) =
      RewindTape.frame (preparation M) (scratch M) (prepared M c) false 0 := by
  have hp := (fresh_tapes M c (scratch M) (by rfl)).2
  have hh : Function.update (prepared M c).head (scratch M) 0 = (prepared M c).head := by
    rw [← hp]
    exact Function.update_eq_self _ _
  change MultitapeTM.Cfg.mk _ _ _ = MultitapeTM.Cfg.mk _ _ (Function.update _ _ _)
  rw [hh]
  rfl
end BitDFT.ExtractionReady
open BitDFT.ExtractionReady BitDFT IntMul MachineSequence

theorem solution (M : MultitapeTM) (x y : List Bool) (t : ℕ)
    (halt : ((VectorReady.machine M).step^[t] ((VectorReady.machine M).initCfg x y)).state =
      (VectorReady.machine M).qHalt) :
    ∃ u : ℕ, u ≤ t+2 ∧
      (machine M).step^[u] ((machine M).initCfg x y) =
        final M ((VectorReady.machine M).step^[t] ((VectorReady.machine M).initCfg x y)) := by
  let c := (VectorReady.machine M).step^[t] ((VectorReady.machine M).initCfg x y)
  have hr : (preparation M).step^[t] ((preparation M).initCfg x y) = prepared M c := by
    rw [prepared_init,prepared_run]
  have hh : ((preparation M).step^[t] ((preparation M).initCfg x y)).state =
      (native (preparation M)).exit := by rw [hr]; exact halt
  have hf := (fresh_tapes M c (scratch M) (by rfl)).1
  have hz : (prepared M c).cells (scratch M) 0 = (preparation M).startSym := by rw [hf]; rfl
  have hn : ∀ p, 0 < p → (prepared M c).cells (scratch M) p ≠ (preparation M).startSym := by
    intro p hp
    rw [hf]
    cases p with
    | zero => omega
    | succ p =>
      change (preparation M).blank ≠ (preparation M).startSym
      have hd := (preparation M).syms_distinct
      aesop
  have hs := BitDFT.rewind_tape_correct (preparation M) (scratch M) (prepared M c) hz hn 0
  obtain ⟨u,hu,he⟩ := BitDFT.machine_sequence_bound (native (preparation M)) (advance M)
    ((preparation M).initCfg x y) t 1 hh
  change (machine M).step^[u] ((machine M).initCfg x y) =
    rightCfg (native (preparation M)) (advance M)
      ((advance M).machine.step^[1] (handoff (native (preparation M)) (advance M)
        ((preparation M).step^[t] ((preparation M).initCfg x y)))) at he
  rw [hr,correct_handoff] at he
  change (machine M).step^[u] ((machine M).initCfg x y) =
    rightCfg (native (preparation M)) (advance M)
      ((RewindTape.machine (preparation M) (scratch M)).step^[0+1]
        (RewindTape.frame (preparation M) (scratch M) (prepared M c) false 0)) at he
  rw [hs] at he
  exact ⟨u,by omega,he⟩
