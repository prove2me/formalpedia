-- Prove2me | solution 1 for BitDFT.child_call_with_precision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T18:35:03.553988+00:00
-- url     : https://prove2.me/submissions/378d6d79-bb09-44b1-99a0-5c93dc16a8ef

import Definitions.Def_BitDFT_ChildCall
import Theorems.Thm_BitDFT_vector_encoding_length
import Mathlib.Tactic.Linarith
import Theorems.Thm_BitDFT_caller_ready_with_precision
import Theorems.Thm_BitDFT_machine_sequence_bound
import Theorems.Thm_IntMul_TrackedBankedCall_call_correct

noncomputable section
namespace BitDFT.CallerInitialFrame
open IntMul

private theorem tagged_getD (M : MultitapeTM) (w : List M.Sym) (p : ℕ) :
    (w.map (fun a => some (a,true))).getD p (some (M.blank,false)) =
      some (w.getD p M.blank,decide (p < w.length)) := by
  by_cases hp : p < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hp),List.getD_eq_getElem _ _ hp]
    simp [hp]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hp),List.getD_eq_default _ _ (Nat.le_of_not_gt hp)]
    simp [hp]

theorem source_tape (M : MultitapeTM) (base : ℕ → TrackedBankedSimulation.Sym M)
    (hbase : base 0 = none) (w : List M.Sym) :
    TrackedBankPreparation.sourceTape M base 1 w =
      (TrackedBankPreparation.machine M).tapeOf
        (some (M.blank,false)::w.map (fun a => some (a,true))) := by
  funext p
  cases p with
  | zero => simp [TrackedBankPreparation.sourceTape,MultitapeTM.tapeOf,hbase]
  | succ p =>
    cases p with
    | zero => simp [TrackedBankPreparation.sourceTape,MultitapeTM.tapeOf]
    | succ p =>
      simpa [TrackedBankPreparation.sourceTape,MultitapeTM.tapeOf] using (tagged_getD M w p).symm

theorem fresh_tape (M : MultitapeTM) (base : ℕ → TrackedBankedSimulation.Sym M)
    (hbase : base 0 = none) :
    TrackedBankPreparation.freshTape M base 1 =
      (TrackedBankPreparation.machine M).tapeOf [] := by
  funext p
  cases p <;> simp [TrackedBankPreparation.freshTape,MultitapeTM.tapeOf,hbase]


theorem binary_source (M : MultitapeTM) (base : ℕ → TrackedBankedSimulation.Sym M)
    (hbase : base 0 = none) (w : List Bool) :
    TrackedBankPreparation.sourceTape M base 1 (TrackedBankPreparation.inputWord M w []) =
      (TrackedBankPreparation.machine M).tapeOf
        ([(TrackedBankPreparation.machine M).blank]++
          w.map (TrackedBankPreparation.machine M).bitSym++[(TrackedBankPreparation.machine M).sep]) := by
  rw [source_tape M base hbase]
  congr 1
  simp only [TrackedBankPreparation.inputWord,List.map_append,List.map_cons,List.map_nil,List.map_map]
  congr 1
  have he : (fun b => some (M.bitSym b,true)) = (TrackedBankPreparation.machine M).bitSym := by
    funext b
    cases b <;> rfl
  simp only [Function.comp_def,he]
  rfl


private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem initial_frame (M : MultitapeTM) (base : (TrackedBankedCall.machine M).Cfg) (w : List Bool)
    (hs : base.state = (TrackedBankedCall.machine M).qStart)
    (ho : base.cells (TrackedBankedCall.machine M).outTape =
      (TrackedBankedCall.machine M).tapeOf
        ([(TrackedBankedCall.machine M).blank]++w.map (TrackedBankedCall.machine M).bitSym++[(TrackedBankedCall.machine M).sep]))
    (hh : base.head (TrackedBankedCall.machine M).outTape = 1)
    (hb : ∀ i : Fin (M.k+2), 2 ≤ i.val →
      base.cells i = (TrackedBankedCall.machine M).tapeOf [] ∧ base.head i = 1) :
    TrackedBankedCall.initialFrame M base 1 (fun _ => 1) w [] = base := by
  apply cfg_ext
  · exact hs.symm
  · funext i
    by_cases hi : 2 ≤ i.val
    · simp only [TrackedBankedCall.initialFrame,TrackedBankedCall.liftPreparation,TrackedBankPreparation.initialFrame,hi,dite_true,TrackedBankedCall.preparationBase]
      change TrackedBankPreparation.freshTape M (base.cells i) 1 = base.cells i
      rw [(hb i hi).1]
      exact fresh_tape M _ rfl
    · have hz : i.val = 0 ∨ i.val = 1 := by omega
      rcases hz with hz | hz
      · have he : i = ⟨0,by omega⟩ := Fin.ext hz
        rw [he]
        rfl
      · have he : i = (TrackedBankedCall.machine M).outTape := Fin.ext hz
        rw [he]
        change TrackedBankPreparation.sourceTape M (base.cells (TrackedBankedCall.machine M).outTape) 1
          (TrackedBankPreparation.inputWord M w []) = base.cells (TrackedBankedCall.machine M).outTape
        have hm : base.cells (TrackedBankedCall.machine M).outTape 0 = none := by rw [ho]; rfl
        exact (binary_source M _ hm w).trans ho.symm
  · funext i
    by_cases hi : 2 ≤ i.val
    · simp only [TrackedBankedCall.initialFrame,TrackedBankedCall.liftPreparation,TrackedBankPreparation.initialFrame,hi,dite_true]
      change 1 = base.head i
      exact (hb i hi).2.symm
    · have hz : i.val = 0 ∨ i.val = 1 := by omega
      rcases hz with hz | hz
      · have he : i = ⟨0,by omega⟩ := Fin.ext hz
        rw [he]
        rfl
      · have he : i = (TrackedBankedCall.machine M).outTape := Fin.ext hz
        rw [he]
        exact hh.symm

end BitDFT.CallerInitialFrame

namespace BitDFT.ChildCall
open IntMul
private theorem cfg_ext {M : MultitapeTM} (c d : M.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c; cases d; cases hs; cases hc; cases hh; rfl

theorem step_embed (M : MultitapeTM) (base : (preparation M).Cfg) (c : (child M).Cfg) :
    (machine M).step (embed M base c) = embed M base ((child M).step c) := by
  have hread : (fun j => (embed M base c).cells (oldTape M j)
      ((embed M base c).head (oldTape M j))) = (fun j => c.cells j (c.head j)) := by
    funext j
    simp [embed,oldTape,j.isLt]
  apply cfg_ext
  · change ((child M).δ c.state _).1 = ((child M).δ c.state _).1
    rw [hread]
  · funext i
    by_cases hi : i.val < (child M).k
    · simp [MultitapeTM.step,control,transition,embed,oldTape,hi]
    · simp [MultitapeTM.step,control,transition,embed,oldTape,hi]
  · funext i
    by_cases hi : i.val < (child M).k
    · simp [MultitapeTM.step,control,transition,embed,oldTape,hi]
    · simp [MultitapeTM.step,control,transition,embed,oldTape,hi]

theorem run_embed (M : MultitapeTM) (base : (preparation M).Cfg) (c : (child M).Cfg) (t : ℕ) :
    (machine M).step^[t] (embed M base c) = embed M base ((child M).step^[t] c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih,step_embed,Function.iterate_succ_apply']

theorem embed_project (M : MultitapeTM) (base : (preparation M).Cfg) :
    embed M base (project M base) =
      MachineSequence.handoff (MachineSequence.native (preparation M)) (control M) base := by
  apply cfg_ext
  · rfl
  · funext i
    by_cases hi : i.val < (child M).k <;> simp [embed,project,oldTape,hi,MachineSequence.handoff]
  · funext i
    by_cases hi : i.val < (child M).k <;> simp [embed,project,oldTape,hi,MachineSequence.handoff]


open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

theorem call_from_prepared (M : MultitapeTM) (base : (preparation M).Cfg) (x : List Bool)
    (ho : base.cells (preparation M).outTape = (preparation M).tapeOf
      ([(preparation M).blank]++x.map (preparation M).bitSym++[(preparation M).sep]))
    (hh : base.head (preparation M).outTape = 1)
    (hb : ∀ i : Fin (preparation M).k, 2 ≤ i.val → i.val < M.k+2 →
      base.cells i = (child M).tapeOf [] ∧ base.head i = 1)
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x [])).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x [])).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T+5*span M (extents M (M.initCfg x []) (initialExtent M x []) T)+2*(inputWord M x []).length+13 ∧
      (machine M).step^[t] (MachineSequence.handoff (MachineSequence.native (preparation M)) (control M) base) =
        embed M base (TrackedBankedCall.finalFrame M (project M base) 1 (fun _ => 1)
          (extents M (M.initCfg x []) (initialExtent M x []) T) (M.step^[T] (M.initCfg x [])) w) := by
  have hp : TrackedBankedCall.initialFrame M (project M base) 1 (fun _ => 1) x [] = project M base := by
    apply CallerInitialFrame.initial_frame M (project M base) x rfl
    · exact ho
    · exact hh
    · intro i hi
      exact hb (oldTape M i) hi i.isLt
  obtain ⟨t,ht,hr⟩ := TrackedBankedCall.call_correct M (project M base) 1 (fun _ => 1)
    (fun _ => by decide) x [] T halt w out
  refine ⟨t,ht,?_⟩
  rw [hp] at hr
  rw [← embed_project,run_embed,hr]

end BitDFT.ChildCall

open BitDFT.ChildCall BitDFT IntMul MachineSequence
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

open IntMul.TrackedBankedSimulation (nextExtent)
private lemma clean_head_bound (M : MultitapeTM) (x y : List Bool) (t : ℕ) :
    ∀ i, (M.step^[t] (M.initCfg x y)).head i ≤ t := by
  induction t with
  | zero => simp [MultitapeTM.initCfg]
  | succ t ih =>
    intro i
    rw [Function.iterate_succ_apply']
    simp only [MultitapeTM.step]
    split <;> have hi := ih i <;> omega

private lemma clean_extent_bound (M : MultitapeTM) (x y : List Bool) (t : ℕ) :
    ∀ i, extents M (M.initCfg x y) (initialExtent M x y) t i ≤
      (inputWord M x y).length + t := by
  induction t with
  | zero =>
    intro i
    simp only [extents, initialExtent]
    split <;> omega
  | succ t ih =>
    intro i
    have he := ih i
    have hh := clean_head_bound M x y t i
    simp only [extents, nextExtent]
    split <;> (try simp only [max_le_iff]) <;> omega

private lemma clean_span_bound (M : MultitapeTM) (x y : List Bool) (t : ℕ) :
    span M (extents M (M.initCfg x y) (initialExtent M x y) t) ≤
      (inputWord M x y).length + t := by
  exact Finset.sup_le fun i _ => clean_extent_bound M x y t i


private theorem input_length (n b : ℕ) (hn : 1 ≤ n) (U : Fin n → ℤ × ℤ) :
    (fourierInput (guardPrecision n b) U).length ≤ 12*n*guardPrecision n b := by
  let q := guardPrecision n b
  have hq : 1 ≤ q := by unfold q guardPrecision; omega
  have hnsize : n.size ≤ lg n+1 := by
    apply Nat.size_le.mpr
    have hnp : n ≤ 2^lg n := (Nat.le_pow_clog (by decide : 1<2) n).trans
      (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
    have hpos := Nat.two_pow_pos (lg n)
    rw [pow_succ]
    omega
  have hns : n.size ≤ q := by unfold q guardPrecision; omega
  have hqs : q.size ≤ q := Nat.size_le.mpr Nat.lt_two_pow_self
  have hlenr : (encVector (q+1) U).length = 2*n*(q+2) := by
    simpa [Nat.add_assoc] using BitDFT.vector_encoding_length (q+1) U
  have hl : (fourierInput q U).length = 2*n.size+1+(2*q.size+1)+2*n*(q+2) := by
    simp only [fourierInput,List.length_append,hlenr]
    simp [encNat,bin]
    omega
  change (fourierInput q U).length ≤ 12*n*q
  rw [hl]
  have hnq : n ≤ n*q := by nlinarith
  have hqn : q ≤ n*q := by nlinarith
  have hp : 1 ≤ n*q := by nlinarith
  nlinarith


theorem solution (M : MultitapeTM) (n b : ℕ) (hn : 1 ≤ n) (hb : 1 ≤ b) (U : Fin n → ℤ × ℤ)
    (T : ℕ)
    (halt : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).state = M.qHalt)
    (w : List Bool)
    (out : (M.step^[T] (M.initCfg (fourierInput (guardPrecision n b) U) [])).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    let q := guardPrecision n b
    let x := fourierInput q U
    ∃ t v, t ≤ 176*n*q+6*T ∧ BinaryCounter.value v = q ∧
      (program M).step^[t] ((program M).initCfg (requestedInput b U) []) =
        final M (CallerReady.final (child M) M.k (RewriteInput.final n b (encVector (q+1) U) v) x) x T w := by
  dsimp only
  let q := guardPrecision n b
  let x := fourierInput q U
  obtain ⟨s,v,hs,hv,hr,ho,hh,hbanks⟩ := BitDFT.caller_ready_with_precision (child M) M.k n b hn hb U
  let base := CallerReady.final (child M) M.k (RewriteInput.final n b (encVector (q+1) U) v) x
  obtain ⟨u,hu,hcall⟩ := call_from_prepared M base x ho hh hbanks T halt w out
  have hhalt : ((preparation M).step^[s] ((preparation M).initCfg (requestedInput b U) [])).state =
      (native (preparation M)).exit := by
    rw [hr]
    rfl
  obtain ⟨t,ht,he⟩ := BitDFT.machine_sequence_bound (native (preparation M)) (control M)
    ((preparation M).initCfg (requestedInput b U) []) s u hhalt
  change (program M).step^[t] ((program M).initCfg (requestedInput b U) []) =
    rightCfg (native (preparation M)) (control M)
      ((machine M).step^[u] (handoff (native (preparation M)) (control M)
        ((preparation M).step^[s] ((preparation M).initCfg (requestedInput b U) [])))) at he
  rw [hr] at he
  change (program M).step^[t] ((program M).initCfg (requestedInput b U) []) =
    rightCfg (native (preparation M)) (control M)
      ((machine M).step^[u] (handoff (native (preparation M)) (control M) base)) at he
  rw [hcall] at he
  refine ⟨t,v,?_,hv,he⟩
  have hext := clean_span_bound M x [] T
  have hlen : (inputWord M x []).length = x.length+1 := by simp [inputWord]
  rw [hlen] at hext hu
  have hx := input_length n b hn U
  have hq : 1 ≤ q := by unfold q guardPrecision; omega
  have hp : 1 ≤ n*q := by nlinarith
  change s ≤ 71*n*q at hs
  change x.length ≤ 12*n*q at hx
  change t ≤ 176*n*q+6*T
  nlinarith
