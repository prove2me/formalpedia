-- Prove2me | solution 1 for DetDLP.scalar_contraction_local_stepper_copy_v4
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T09:30:17.064644+00:00
-- url     : https://prove2.me/submissions/90d193bf-39db-41d4-b82b-b021ba37cc0b

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_OAIQ081S023
import Mathlib.Data.Nat.Size

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace DetDLP.StepperCopyV4
open OAI.Algorithms.SubexponentialSAT
open BitProgram StackRoutines

/-- Across an iteration, the word in flight either occupies a stack or is
    carried by the value register between a pop and a push. -/
private def controlBound (pc : Option (Fin 8)) (present : Bool)
    (source spare dest cap : ℕ) : Prop :=
  match pc with
  | none => source + spare ≤ cap ∧ dest + spare ≤ cap
  | some l => match l.val with
    | 0 => source + spare ≤ cap ∧ dest = 0
    | 1 => source + spare + present.toNat ≤ cap ∧ dest = 0
    | 2 => source + spare + 1 ≤ cap ∧ dest = 0
    | 3 => source + spare ≤ cap ∧ dest + spare ≤ cap
    | 4 => source + spare + present.toNat ≤ cap ∧ dest + spare + present.toNat ≤ cap
    | 5 => source + spare + 1 ≤ cap ∧ dest + spare + 1 ≤ cap
    | 6 => source + spare ≤ cap ∧ dest + spare + 1 ≤ cap
    | _ => source + spare ≤ cap ∧ dest + spare ≤ cap

private def invariant {n : ℕ} (src dst tmp : Fin n) (cap : ℕ) (c : Cfg 8 n 8) : Prop :=
  (∀ i, i ≠ src → i ≠ dst → i ≠ tmp → (c.stacks i).length ≤ cap) ∧
  controlBound c.pc (c.regs 1) (c.stacks src).length (c.stacks tmp).length (c.stacks dst).length cap

private theorem control_le (pc : Option (Fin 8)) (p : Bool) (x t y U : ℕ)
    (h : controlBound pc p x t y U) : x ≤ U ∧ t ≤ U ∧ y ≤ U := by
  cases pc with
  | none => simp only [controlBound] at h; omega
  | some l =>
    fin_cases l <;> cases p <;> simp [controlBound] at h <;> omega

private theorem invariant_step {n : ℕ} (src dst tmp : Fin n)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (U : ℕ)
    (pc : Fin 8) (regs : Fin 8 → Bool) (stk : Fin n → List Bool)
    (h : invariant src dst tmp U ⟨some pc, regs, stk⟩) :
    invariant src dst tmp U
      (execInstr ((copyProgram src dst tmp (0 : Fin 8) 1).code pc) ⟨some pc,regs,stk⟩) := by
  obtain ⟨other, hb⟩ := h
  constructor
  · intro i his hid hit
    have hi := other i his hid hit
    fin_cases pc <;>
      simpa [copyProgram, execInstr, his, hid, hit] using hi
  · change controlBound (some pc) (regs 1) _ _ _ _ at hb
    fin_cases pc
    · cases v : stk src <;>
        simp [execInstr, controlBound, readRegs, v, hsd.symm, hst.symm] at hb ⊢ <;>
        exact ⟨by omega, hb.2⟩
    · cases v : regs 1
      · simp [execInstr, controlBound, v] at hb ⊢
        exact ⟨hb.1, by rw [hb.2]; simp; omega⟩
      · simpa [execInstr, controlBound, v] using hb
    · simp [execInstr, controlBound, hst, htd.symm] at hb ⊢
      exact ⟨by omega, hb.2⟩
    · cases v : stk tmp <;>
        simp [execInstr, controlBound, readRegs, v, hst, htd.symm] at hb ⊢ <;> omega
    · cases v : regs 1 <;> simpa [execInstr, controlBound, v] using hb
    · simp [execInstr, controlBound, hsd.symm, hst.symm] at hb ⊢ <;> omega
    · simp [execInstr, controlBound, hsd, htd] at hb ⊢ <;> omega
    · simpa [execInstr, controlBound] using hb

private theorem invariant_trace {n : ℕ} (src dst tmp : Fin n)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (U : ℕ)
    {j : ℕ} {a b : Cfg 8 n 8}
    (tr : BitProgram.Trace (copyProgram src dst tmp (0 : Fin 8) 1) j a b)
    (h : invariant src dst tmp U a) : invariant src dst tmp U b := by
  induction tr with
  | refl => exact h
  | @cons _ a b c hs _ ih =>
    apply ih
    obtain ⟨pc,regs,stk⟩ := a
    cases pc with
    | none => simp [BitProgram.step] at hs
    | some l =>
      have he := Option.some.inj hs
      subst b
      exact invariant_step src dst tmp hsd hst htd U l regs stk h

private theorem lengths_of_invariant {n : ℕ} {src dst tmp : Fin n} {U : ℕ}
    {c : Cfg 8 n 8} (h : invariant src dst tmp U c) : ∀ i, (c.stacks i).length ≤ U := by
  obtain ⟨ho,hb⟩ := h
  obtain ⟨hs,ht,hd⟩ := control_le _ _ _ _ _ _ hb
  intro i
  by_cases h₁ : i = src
  · simpa [h₁] using hs
  by_cases h₂ : i = dst
  · simpa [h₂] using hd
  by_cases h₃ : i = tmp
  · simpa [h₃] using ht
  exact ho _ h₁ h₂ h₃

private def sourceSlot {s : ℕ} (hs : 0 < s) : Fin (20 + s) := Fin.natAdd 20 ⟨0, hs⟩
private def argumentSlot (s : ℕ) : Fin (20 + s) := Fin.castAdd s (Fin.natAdd 8 (7 : Fin 12))
private def spareSlot (s : ℕ) : Fin (20 + s) := Fin.castAdd s (Fin.castAdd 12 (0 : Fin 8))

private def frame {s : ℕ} (context : Fin s → List Bool) (q a b stack val : ℕ) :
    Fin (20 + s) → List Bool :=
  let v : Fin 12 → ℕ := ![q, 1, 0, a, b, stack, 0, val, 0, 0, 0, 0]
  Fin.addCases (m := 20) (n := s)
    (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits)) context

private theorem replace_head {n : ℕ} (x y : ℕ) (rest : Fin n → ℕ) :
    ∀ i : Fin (n+1), i ≠ 0 → Matrix.vecCons x rest i = Matrix.vecCons y rest i := by
  intro i
  induction i using Fin.cases with
  | zero => intro h; exact (h rfl).elim
  | succ i => intro _; simp only [Matrix.cons_val_succ]

private theorem preserve_head {n : ℕ} {f g : Fin n → ℕ} {j : Fin n} (x : ℕ)
    (h : ∀ i, i ≠ j → f i = g i) :
    ∀ i : Fin (n+1), i ≠ j.succ → Matrix.vecCons x f i = Matrix.vecCons x g i := by
  intro i
  induction i using Fin.cases with
  | zero => intro _; simp only [Matrix.cons_val_zero]
  | succ i => intro hn; apply (Matrix.cons_val_succ ..).trans
              exact (h i (fun e => hn (congrArg Fin.succ e))).trans (Matrix.cons_val_succ ..).symm

private theorem same_other_field (q a b stack val : ℕ) (i : Fin 12) (h : i ≠ 7) :
    ![q, 1, 0, a, b, stack, 0, 0, 0, 0, 0, 0] i =
      ![q, 1, 0, a, b, stack, 0, val, 0, 0, 0, 0] i := by
  have base := replace_head 0 val (![0,0,0,0] : Fin 4 → ℕ)
  have throughStack := preserve_head stack (preserve_head 0 base)
  have throughArgs := preserve_head a (preserve_head b throughStack)
  exact preserve_head q (preserve_head 1 (preserve_head 0 throughArgs)) i h

private theorem frame_update {s : ℕ} (context : Fin s → List Bool) (q a b stack val : ℕ) :
    Function.update (frame context q a b stack 0) (argumentSlot s) val.bits =
      frame context q a b stack val := by
  funext i
  by_cases h : i = argumentSlot s
  · subst i
    simp only [Function.update_self, frame, argumentSlot, Fin.addCases_left, Fin.addCases_right] <;> rfl
  · rw [Function.update_of_ne h]
    induction i using Fin.addCases with
    | right j => simp [frame]
    | left j =>
      induction j using Fin.addCases (m := 8) (n := 12) with
      | left k => simp [frame]
      | right k =>
        have hn : k ≠ (7 : Fin 12) := by rintro rfl; exact h rfl
        simp only [frame, Fin.addCases_left, Fin.addCases_right]
        exact congrArg Nat.bits (same_other_field q a b stack val k hn)

private theorem fold_bounds (xs : List ℕ) (z : ℕ) :
    z ≤ xs.foldl max z ∧ ∀ k ∈ xs, k ≤ xs.foldl max z := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hi, hm⟩ := ih (max z x)
    refine ⟨(le_max_left z x).trans hi, ?_⟩
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact (le_max_right z _).trans hi
    · exact hm _ hk

private theorem bitLength_mono {a b : ℕ} (h : a ≤ b) : a.bits.length ≤ b.bits.length := by
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h

private theorem frame_lengths {s : ℕ} (context : Fin s → List Bool)
    {q a b stack L : ℕ} (hq : q.bits.length ≤ L) (ha : a.bits.length ≤ L)
    (hb : b.bits.length ≤ L) (ht : stack.bits.length ≤ L) (hL : 1 ≤ L)
    (hc : ∀ i, (context i).length ≤ L) : ∀ i, (frame context q a b stack 0 i).length ≤ L := by
  intro i
  induction i using Fin.addCases with
  | right j => simpa [frame] using hc j
  | left i =>
    induction i using Fin.addCases (m := 8) (n := 12) with
    | left j => simp only [frame, Fin.addCases_left, List.length_nil, Nat.zero_le]
    | right j =>
      simp only [frame, Fin.addCases_left, Fin.addCases_right]
      fin_cases j <;> first | exact hq | exact ha | exact hb | exact ht | exact hL | simp [hL]

open DetDLP.ContinuationSchedule

private theorem stepper_run (s : ℕ) (hs : 0 < s) (answer B depth : ℕ)
    (context : Fin s → List Bool) (hB : 0 < B) (_haB : answer < B)
    (hcontext : context ⟨0, hs⟩ = answer.bits) :
    let M := (List.ofFn (fun i => (context i).length)).foldl Nat.max 0
    let U := M + (((B+1)^(depth+1)).bits.length) + 4
    (∀ i, (context i).length ≤ U) ∧
    ∀ (a b stack : ℕ) (r : Fin 8 → Bool),
      a < B → b < B → stack < (B+1)^(depth+1) →
      let p := copyProgram (sourceSlot hs) (argumentSlot s) (spareSlot s) (0 : Fin 8) 1
      let start : Cfg 8 (20+s) 8 := ⟨some p.entry,r,frame context (B+1) a b stack 0⟩
      ∃ (steps : ℕ) (r' : Fin 8 → Bool), steps ≤ 7 * answer.bits.length + 5 ∧
        BitProgram.Trace p steps start ⟨none,r',frame context (B+1) a b stack answer⟩ ∧
        ∀ j c, j ≤ steps → BitProgram.Trace p j start c → ∀ i, (c.stacks i).length ≤ U := by
  intro M U
  have hM (i : Fin s) : (context i).length ≤ M :=
    (fold_bounds _ 0).2 _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hC (i : Fin s) : (context i).length ≤ U := (hM i).trans (by dsimp [U]; omega)
  refine ⟨hC, ?_⟩
  intro a b stack regs ha hb hstack p start
  let src := sourceSlot hs
  let dst := argumentSlot s
  let tmp := spareSlot s
  let stk := frame context (B+1) a b stack 0
  have hsd : src ≠ dst := by
    intro e; have := congrArg Fin.val e; norm_num [src, dst, sourceSlot, argumentSlot] at this
  have hst : src ≠ tmp := by
    intro e; have := congrArg Fin.val e; norm_num [src, tmp, sourceSlot, spareSlot] at this
  have htd : tmp ≠ dst := by
    intro e; have := congrArg Fin.val e; norm_num [tmp, dst, spareSlot, argumentSlot] at this
  have hin : stk src = answer.bits := by simpa only [stk, frame, src, sourceSlot, Fin.addCases_right] using hcontext
  have hout : stk dst = [] := by simp only [stk, frame, dst, argumentSlot, Fin.addCases_left, Fin.addCases_right] <;> rfl
  have htmp : stk tmp = [] := by simp only [stk, frame, tmp, spareSlot, Fin.addCases_left]
  have hcopy := copyProgram_trace src dst tmp (0 : Fin 8) 1 hsd hst htd (by decide) regs stk htmp
  have halt := halt_after_trace _ hcopy 7 rfl rfl
  have hframe : copyStacks src dst stk = frame context (B+1) a b stack answer := by
    simpa only [copyStacks,hin,hout,List.append_nil] using
      (show Function.update stk dst answer.bits = _ from frame_update context (B+1) a b stack answer)
  refine ⟨7 * answer.bits.length + 5, readRegs regs 0 1 none, le_rfl, ?_, ?_⟩
  · simpa only [copyResult, hframe, hin, Nat.add_assoc] using halt
  · have hp : B+1 ≤ (B+1)^(depth+1) := by
      calc B+1 = (B+1)^1 := (pow_one _).symm
           _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    have hq : ((B+1)^(depth+1)).bits.length ≤ U := by dsimp [U]; omega
    have hh : ∀ i, (stk i).length ≤ U :=
      frame_lengths context ((bitLength_mono hp).trans hq)
        ((bitLength_mono (le_trans (by omega : a ≤ B+1) hp)).trans hq)
        ((bitLength_mono (le_trans (by omega : b ≤ B+1) hp)).trans hq)
        ((bitLength_mono hstack.le).trans hq) (by dsimp [U]; omega) hC
    have hinit : invariant src dst tmp U start := by
      refine ⟨fun i _ _ _ => hh i, ?_⟩
      change (stk src).length + (stk tmp).length ≤ U ∧ (stk dst).length = 0
      simp [htmp,hout,hh]
    intro j c _ tr
    exact lengths_of_invariant (invariant_trace src dst tmp hsd hst htd U tr hinit)

end DetDLP.StepperCopyV4

namespace DetDLP

open DetDLP.ContinuationSchedule OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem _root_.solution
    (s : ℕ) (hs : 0 < s) :
    ∃ (lc : ℕ) (stepper : BitProgram.Program 8 (20 + s) lc),
      ∀ (answer B depth : ℕ) (context : Fin s → List Bool),
        0 < B → answer < B → context ⟨0, hs⟩ = answer.bits →
        let M := (List.ofFn (fun i => (context i).length)).foldl Nat.max 0
        let F : ℕ → ℕ → Answer := fun _ _ => .value answer
        let q := B + 1
        let pack (a b stack tag arg save : ℕ) : Fin (20 + s) → List Bool :=
          let v : Fin 12 → ℕ := ![q, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0]
          Fin.addCases (m := 20) (n := s)
            (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits)) context
        let small (z : Answer) := match z with
          | .value v => v < B
          | .call a b => a < B ∧ b < B
        let returned (a b stack : ℕ) (z : Answer) := match z with
          | .value v => pack a b stack 0 v 0
          | .call save child => pack a b stack 1 child save
        ∃ (T U : ℕ),
          (∀ i, (context i).length ≤ U) ∧
          T ≤ 100 * (answer.bits.length + 1) ∧
          U ≤ M + ((q ^ (depth + 1)).bits.length) + 4 ∧
          ∀ (a b stack : ℕ) (r : Fin 8 → Bool),
            a < B → b < B → stack < q ^ (depth + 1) → small (F a b) →
            let start : BitProgram.Cfg 8 (20 + s) lc :=
              ⟨some stepper.entry, r, pack a b stack 0 0 0⟩
            ∃ (steps : ℕ) (r' : Fin 8 → Bool), steps ≤ T ∧
              BitProgram.Trace stepper steps start ⟨none, r', returned a b stack (F a b)⟩ ∧
              ∀ j c, j ≤ steps → BitProgram.Trace stepper j start c →
                ∀ i, (c.stacks i).length ≤ U := by
  refine ⟨8, StackRoutines.copyProgram (StepperCopyV4.sourceSlot hs)
    (StepperCopyV4.argumentSlot s) (StepperCopyV4.spareSlot s) (0 : Fin 8) 1, ?_⟩
  intro answer B depth context hB haB hc M F q pack small returned
  have run := StepperCopyV4.stepper_run s hs answer B depth context hB haB hc
  refine ⟨7 * answer.bits.length + 5, M + ((q ^ (depth + 1)).bits.length) + 4,
    run.1, by omega, le_rfl, ?_⟩
  intro a b stack regs ha hb ht _
  exact run.2 a b stack regs ha hb ht

end DetDLP
