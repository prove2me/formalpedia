-- Prove2me | solution 1 for DetDLP.m89_prime_predecessor_factor_oracle
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T17:32:36.443124+00:00
-- url     : https://prove2.me/submissions/eebc6357-edaa-4174-8dc8-4e54304cbf96

import Definitions.Def_DetDLP_M89_CompileSpace
import Definitions.Def_DetDLP_M89_MachineComp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP DetDLP.MachineComposition
namespace DetDLP.M89FactorOracle

def machine (A : PrimitiveMachine) (out : Fin A.tapeCount) : PrimitiveMachine where
  tapeCount := A.tapeCount
  stateCount := 5 + A.stateCount
  start := Fin.castAdd _ 0
  inputTape := A.inputTape
  scan := Fin.append (fun q : Fin 5 => if q.val = 3 then out else A.inputTape) A.scan
  transition := Fin.append (fun q : Fin 5 => fun sym => match q.val with
    | 0 => if sym = some true then .inr (Fin.natAdd 5 A.start,.write (some false))
           else .inr (Fin.castAdd _ 1,.move .right)
    | 1 => .inr (Fin.castAdd _ 2,.write none)
    | 2 => .inr (Fin.castAdd _ 3,.move .left)
    | 3 => .inr (Fin.castAdd _ 4,.write (some false))
    | _ => .inl true)
    (fun q sym => match A.transition q sym with
      | .inl b => .inl b
      | .inr (q',act) => .inr (Fin.natAdd 5 q',act))

private def liftC (A : PrimitiveMachine) (o : Fin A.tapeCount) (c : LocatedCfg A) : LocatedCfg (machine A o) where
  config := ⟨c.config.state.elim Sum.inl (fun q => .inr (Fin.natAdd 5 q)),c.config.tapes⟩
  position := c.position
  lower := c.lower
  upper := c.upper

private theorem liftStep (A : PrimitiveMachine) (o : Fin A.tapeCount) (c d : LocatedCfg A)
    (hs : locatedStep A c = some d) : locatedStep (machine A o) (liftC A o c) = some (liftC A o d) := by
  rcases c with ⟨⟨state,tapes⟩,pos,lo,hi⟩
  cases state with
  | inl b => simp [locatedStep, PrimitiveMachine.step] at hs
  | inr q =>
    cases ht : A.transition q (tapes (A.scan q)).head with
    | inl b =>
      simp [locatedStep,PrimitiveMachine.step,LocatedCfg.monitor,ht] at hs
      subst d; simp [locatedStep,PrimitiveMachine.step,LocatedCfg.monitor,liftC,machine,ht]
    | inr pair =>
      rcases pair with ⟨q',act⟩; cases act <;>
        simp [locatedStep,PrimitiveMachine.step,LocatedCfg.monitor,ht] at hs <;> subst d <;>
        simp [locatedStep,PrimitiveMachine.step,LocatedCfg.monitor,liftC,machine,ht]

private theorem oddStart (A : PrimitiveMachine) (o : Fin A.tapeCount) (tail : List Bool) :
    locatedStep (machine A o) (locatedInit (machine A o) (true::tail)) =
      some (liftC A o (locatedInit A (false::tail))) := by
  have wr : (Turing.Tape.mk₁ ((true::tail).map some)).write (some false) = Turing.Tape.mk₁ ((false::tail).map some) := rfl
  have hd : (Turing.Tape.mk₁ (some true :: tail.map some)).head = some true := rfl
  simp [locatedStep,LocatedCfg.monitor,PrimitiveMachine.step,PrimitiveMachine.init,locatedInit,machine,liftC,headDisplacement,hd]
  funext i; by_cases hi : i = A.inputTape <;> simp [hi,Function.update_apply] <;> rfl

private theorem oddRun (A : PrimitiveMachine) (o : Fin A.tapeCount) (tail output : List Bool) {t s : ℝ}
    (ha : RunsWithin A o (false::tail) output t s) :
    RunsWithin (machine A o) o (true::tail) output (t+1) s := by
  obtain ⟨n,c,h,⟨b,hb⟩,hout,hn,hs⟩ := (runsWithin_iff_final_space ..).mp ha
  apply (runsWithin_iff_final_space ..).mpr
  refine ⟨n+1,liftC A o c,.cons (oddStart A o tail) (MachineComposition.Trace.map _ (liftStep A o) h),⟨b,?_⟩,hout,?_,hs⟩
  · simp [liftC,hb]
  · push_cast; linarith

private theorem twoRun (A : PrimitiveMachine) (o : Fin A.tapeCount) :
    RunsWithin (machine A o) o [false,true] [false] 5 ((13*A.tapeCount : ℕ) : ℝ) := by
  let B := machine A o
  let blank := Turing.Tape.mk₁ ([] : List (Option Bool))
  let word := Turing.Tape.mk₁ ([some false] : List (Option Bool))
  let src := Turing.Tape.mk₁ ([some false,some true] : List (Option Bool))
  let ts := fun i : Fin A.tapeCount => if i = A.inputTape then src else blank
  let ts1 := Function.update ts A.inputTape (src.move .right)
  let ts2 := Function.update ts1 A.inputTape ((src.move .right).write none)
  let ts3 := Function.update ts2 A.inputTape word
  let ts4 := Function.update ts3 o word
  let st := fun (q : Fin 5) (t : Fin A.tapeCount → Turing.Tape (Option Bool)) => (⟨.inr (Fin.castAdd A.stateCount q),t⟩ : B.Cfg)
  have h0 : B.step (st 0 ts) = some (st 1 ts1) := by simp [B,st,ts1,PrimitiveMachine.step,machine,ts]; rfl
  have h1 : B.step (st 1 ts1) = some (st 2 ts2) := by simp [B,st,ts1,ts2,PrimitiveMachine.step,machine]
  have erase : ((src.move .right).write none).move .left = word := by
    change Turing.Tape.mk₂ [] [some false, none] = Turing.Tape.mk₂ [] [some false]
    unfold Turing.Tape.mk₂
    congr 1
    change ((Turing.ListBlank.mk ([] : List (Option Bool))).cons none).cons (some false) = _
    have hblank : (Turing.ListBlank.mk ([] : List (Option Bool))).cons none = Turing.ListBlank.mk [] := by
      simpa [show (default : Option Bool) = none from rfl] using Turing.ListBlank.cons_head_tail (Turing.ListBlank.mk ([] : List (Option Bool)))
    rw [hblank]; rfl
  have h2 : B.step (st 2 ts2) = some (st 3 ts3) := by simp [B,st,ts2,ts3,PrimitiveMachine.step,machine,erase]
  have wo : (ts3 o).write (some false) = word := by
    by_cases ho : o = A.inputTape <;> simp [ts3,ts2,ts1,ts,ho,Function.update_apply] <;> rfl
  have h3 : B.step (st 3 ts3) = some (st 4 ts4) := by simp [B,st,ts4,PrimitiveMachine.step,machine,wo]
  have h4 : B.step (st 4 ts4) = some ⟨.inl true,ts4⟩ := by simp [B,st,PrimitiveMachine.step,machine]
  have trace : Computation.Trace B.step 5 (locatedInit B [false,true]).config ⟨.inl true,ts4⟩ :=
    .cons h0 (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.refl _)))))
  obtain ⟨c,ht,hc⟩ := locatedTrace_lift trace
  apply (runsWithin_iff_final_space ..).mpr
  refine ⟨5,c,ht,⟨true,by rw [hc]⟩,by rw [hc]; simp [ts4,word],by norm_num,?_⟩
  have hb := locatedTrace_space_le_of_length ht
  exact_mod_cast (by simpa [B,machine,Nat.mul_comm] using hb : visitedSpace c ≤ 13*A.tapeCount)

end DetDLP.M89FactorOracle

open DetDLP.M89FactorOracle

theorem solution (A : PrimitiveMachine) (o : Fin A.tapeCount) (T S : ℕ → ℝ)
    (hf : ∀ N : ℕ, 2 ≤ N → RunsWithin A o (countWord N) (encodeNatListBin N.primeFactorsList) (T N) (S N)) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount), ∀ (p : ℕ), p.Prime →
      RunsWithin M out (countWord p) (encodeNatListBin (p-1).primeFactorsList)
        (if p = 2 then 5 else T (p-1)+1) (if p = 2 then (13*A.tapeCount : ℕ) else S (p-1)) := by
  refine ⟨machine A o,o,?_⟩
  intro p hp
  by_cases h2 : p = 2
  · subst p; simp only [ite_true, Nat.reduceSub, Nat.primeFactorsList_one]; exact twoRun A o
  · have hm := hp.mod_two_eq_one_iff_ne_two.mpr h2
    have hp2 := hp.two_le
    have ht : 0 < p/2 := by omega
    have h1 : p = Nat.bit true (p/2) := by simp [Nat.bit]; omega
    have h0 : p-1 = Nat.bit false (p/2) := by simp [Nat.bit]; omega
    have w1 : countWord p = true :: (p/2).bits := by
      rw [countWord,if_neg hp.ne_zero]; conv_lhs => rw [h1]; exact Nat.bits_append_bit _ _ (by simp)
    have w0 : countWord (p-1) = false :: (p/2).bits := by
      rw [countWord,if_neg (by omega : p-1 ≠ 0)]; conv_lhs => rw [h0]; exact Nat.bits_append_bit _ _ (by omega)
    have hor := hf (p-1) (by omega)
    rw [w0] at hor
    simpa [h2,w1] using oddRun A o _ _ hor

#print axioms solution
