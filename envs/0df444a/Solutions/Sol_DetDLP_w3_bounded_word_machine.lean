-- Prove2me | solution 1 for DetDLP.w3_bounded_word_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T00:35:15.017873+00:00
-- url     : https://prove2.me/submissions/8a7c294e-bdde-42a0-a129-80a2d7fd03c7

import Definitions.Def_DetDLP_PolyTBridge

set_option autoImplicit false
open DetDLP
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace OAI.Algorithms.SubexponentialSAT.StructuredProgram

private def DetDLP.w3_emit : List Bool → Cmd 2 1
  | [] => .skip
  | b::bs => .seq (w3_emit bs) (.seq (.atom (.set 0 b)) (.atom (.push 0 0)))

private theorem DetDLP.w3_emit_eval (z : List Bool) (s : State 2 1) :
    ∃ d, Eval (w3_emit z) (2*z.length) s d ∧ d.stacks 0 = z ++ s.stacks 0 := by
  induction z with
  | nil => exact ⟨s,.skip _,rfl⟩
  | cons b bs ih =>
    obtain ⟨d,hd,hout⟩ := ih
    have h := hd.seq ((Eval.atom (.set 0 b) d).seq (Eval.atom (.push 0 0) _))
    refine ⟨_,by simpa [w3_emit,Nat.mul_add] using h,?_⟩
    simp [Atom.eval,Atom.instr,State.ofCfg,State.withPC,BitProgram.execInstr,hout]

private def DetDLP.w3_branchWord (f : List Bool → List Bool) : ℕ → List Bool → Cmd 2 1
  | 0, a => w3_emit (f a)
  | k+1, a => .seq (.atom (.pop 0 0 1)) (.ite 1
      (.ite 0 (w3_branchWord f k (a++[true])) (w3_branchWord f k (a++[false]))) (w3_emit (f a)))

private theorem DetDLP.w3_branchWord_eval (f : List Bool → List Bool) (k : ℕ) (a w : List Bool)
    (s : State 2 1) (hs : s.stacks 0 = w) (hk : w.length ≤ k) :
    ∃ n d, Eval (w3_branchWord f k a) n s d ∧ d.stacks 0 = f (a++w) ∧
      n ≤ 3*k+2*(f (a++w)).length := by
  induction k generalizing a w s with
  | zero =>
    have hw := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hk)
    obtain ⟨d,hd,ho⟩ := w3_emit_eval (f a) s
    exact ⟨_,d,hd,by simpa [hs,hw] using ho,by simp [hw]⟩
  | succ k ih =>
    let t := (Atom.pop (r := 2) (s := 1) 0 0 1).eval s
    have hst : t.stacks 0 = w.tail := by simp [t,Atom.eval,Atom.instr,State.ofCfg,State.withPC,BitProgram.execInstr,hs]
    have hp : t.regs 1 = w.head?.isSome := by simp [t,Atom.eval,Atom.instr,State.ofCfg,State.withPC,BitProgram.execInstr,hs]
    have hv : t.regs 0 = w.head?.getD false := by simp [t,Atom.eval,Atom.instr,State.ofCfg,State.withPC,BitProgram.execInstr,hs,BitProgram.readRegs_value _ _ _ _ (by decide : (0:Fin 2) ≠ 1)]
    cases w with
    | nil =>
      obtain ⟨d,hd,ho⟩ := w3_emit_eval (f a) t
      refine ⟨_,d,(Eval.atom (.pop 0 0 1) s).seq (.ite_false hp hd),by simpa [hst] using ho,?_⟩
      simp; omega
    | cons b bs =>
      obtain ⟨n,d,hd,ho,hb⟩ := ih (a++[b]) bs t hst (by simpa using hk)
      have he : Eval (.ite 0 (w3_branchWord f k (a++[true])) (w3_branchWord f k (a++[false]))) (n+1) t d := by
        cases b with
        | true => exact .ite_true hv hd
        | false => exact .ite_false hv hd
      refine ⟨_,d,(Eval.atom (.pop 0 0 1) s).seq (.ite_true hp he),by simpa using ho,?_⟩
      simp at hb; omega

theorem solution (L : ℕ) (f : List Bool → List Bool) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount), ∀ w : List Bool, w.length ≤ L →
      RunsWithin M out w (f w) ((7*(3*L+2*(f w).length+1) : ℕ) : ℝ)
        ((2*L+(3*L+2*(f w).length+1)+15 : ℕ) : ℝ) := by
  let c := w3_branchWord f L []
  let p := compiled c 0 0
  refine ⟨GuardedCompiler.primitive p,p.outputStack,?_⟩
  intro w hw
  obtain ⟨n,d,he,ho,hn⟩ := w3_branchWord_eval f L [] w (ioState 0 w) (by simp [ioState]) hw
  simp only [List.nil_append] at ho hn
  have ht := compiled_halt_trace he 0 0
  have hr := CompileSpace.compile_runsWithin_from_time p (output := f w) ht rfl ho
  exact PolyTBridge.runsWithin_mono_local hr (by exact_mod_cast (show 7*(n+1) ≤ 7*(3*L+2*(f w).length+1) by omega))
    (by exact_mod_cast (show 1*(w.length+(n+1)+w.length+15) ≤ 2*L+(3*L+2*(f w).length+1)+15 by omega))
