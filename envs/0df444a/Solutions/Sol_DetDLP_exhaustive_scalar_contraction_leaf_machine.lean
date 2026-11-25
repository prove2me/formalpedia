-- Prove2me | solution 1 for DetDLP.exhaustive_scalar_contraction_leaf_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T19:58:17.756929+00:00
-- url     : https://prove2.me/submissions/3dfc7447-38ae-4bcd-a457-6b3cd7bb38f9

import Definitions.Def_OAIQ081S023
import Definitions.Def_DetDLP_Machine
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S045
import Definitions.Def_DetDLP_FilterAndCoset
import Definitions.Def_DetDLP_BorderedHermite
import Definitions.Def_DetDLP_BTN
import Theorems.Thm_DetDLP_contraction_input_and_port_address_machines
import Theorems.Thm_DetDLP_reusable_primitive_tensor_entry_call

noncomputable section
namespace DetDLP.BoundedProgramLoop
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking
/-- A time-indexed run annotated at every visited configuration. -/
inductive SafeTrace {S : Type} (step : S → Option S) (ok : S → Prop) : ℕ → S → S → Prop
  | refl (s : S) : ok s  →  SafeTrace step ok 0 s s
  | cons {s t u k} : ok s  →  step s=some t  →  SafeTrace step ok k t u  →  SafeTrace step ok (k+1) s u
namespace SafeTrace
variable {S T : Type} {f : S → Option S} {g : T → Option T} {P : S → Prop} {Q : T → Prop}
theorem forget {k s t} (tr : SafeTrace f P k s t) : Computation.Trace f k s t := by
  induction tr with
  | refl s _ => exact .refl _
  | cons _ hs _ ih => exact .cons hs ih
theorem trans {n m a b c} (tr : SafeTrace f P n a b) (u : SafeTrace f P m b c) : SafeTrace f P (n+m) a c := by
  induction tr with
  | refl => simpa using u
  | cons h hs _ ih => exact (Nat.succ_add _ _).symm ▸ SafeTrace.cons h hs (ih u)
theorem within {n s t} (tr : SafeTrace f P n s t) :
    ∀ j c,j≤n → Computation.Trace f j s c → P c := by
  induction tr with
  | refl _ h =>
    intro j c hj hp
    obtain rfl : j=0 := by omega
    cases hp; exact h
  | cons h step tail ih =>
    intro j c hj hp; cases hp with
    | refl => exact h
    | cons hs ht => obtain rfl := Option.some.inj (step.symm.trans hs); exact ih _ _ (by omega) ht
theorem of_trace {n s t} (tr : Computation.Trace f n s t)
    (cap : ∀ j c,j≤n → Computation.Trace f j s c → P c) : SafeTrace f P n s t := by
  induction tr with
  | refl => exact .refl _ (cap _ _ (by omega) (.refl _))
  | cons step tail ih =>
    exact .cons (cap _ _ (by omega) (.refl _)) step (ih (fun j c hj tr => cap _ c (by omega) (.cons step tr)))
theorem map {n a b} (tr : SafeTrace f P n a b) (E : S → T)
    (next : ∀ x y,f x=some y → g (E x)=some (E y)) (safe : ∀ x,P x → Q (E x)) : SafeTrace g Q n (E a) (E b) := by
  induction tr with
  | refl _ h => exact .refl _ (safe _ h)
  | cons h hs _ ih => exact .cons (safe _ h) (next _ _ hs) ih
end SafeTrace

variable {r s l : ℕ} (p : Program r s l) (flag : Fin r)
def head : Fin (2+l) := Fin.castAdd l 0
def donePc : Fin (2+l) := Fin.castAdd l 1
def address (i : Fin l) : Fin (2+l) := Fin.natAdd 2 i
def loop : Program r s (2+l) where
  inputStack := p.inputStack
  outputStack := p.outputStack
  entry := head
  code := Fin.addCases (fun i : Fin 2 => if i=0 then .branch flag headBody donePc else .halt)
    (fun i => relocateInstr id id address (some head) (p.code i))
where headBody := address p.entry

def cap {L : ℕ} (W : ℕ) (c : Cfg r s L) := ∀ i,(c.stacks i).length≤W
def embed (c : Cfg r s l) : Cfg r s (2+l) := ⟨relocatePc address (some head) c.pc,c.regs,c.stacks⟩
theorem block {n x y W} (tr : SafeTrace (step p) (cap W) n x y) :
    SafeTrace (step (loop p flag)) (cap W) n (embed x) (embed y) := by
  let frame : Cfg r s (2+l) := ⟨some head,x.regs,x.stacks⟩
  have eq (z : Cfg r s l) : embed z=embedCfg id id address (some head) frame z := by
    cases z; simp [embed,embedCfg,Function.extend_id]
  apply tr.map embed _ (fun _ h => h)
  intro u v h; rw [eq,eq]
  apply relocate_step p _ id id address (some head) frame Function.injective_id Function.injective_id _ h
  intro j; simp [loop,address]

theorem test (z : Cfg r s (2+l)) (hz : z.pc=some head) :
    step (loop p flag) z=some {z with pc:=some (if z.regs flag then address p.entry else donePc)} := by
  rw [step,hz]; simp [loop,head,loop.headBody,execInstr]

theorem halt (z : Cfg r s (2+l)) (hz : z.pc=some donePc) :
    step (loop p flag) z=some {z with pc:=none} := by
  rw [step,hz]; simp [loop,donePc,execInstr]

end DetDLP.BoundedProgramLoop
end

noncomputable section
namespace DetDLP.BoundedProgramLink
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BoundedProgramLoop
variable {r s l m : ℕ} (p : Program r s l) (q : Program r s m)
theorem relabel {L : ℕ} (Q : Program r s L) (labels : Fin l → Fin L) (ret : Option (Fin L))
    (code : CodeEmbedding p Q id id labels ret) {t x y W} (tr : SafeTrace (step p) (cap W) t x y) :
    SafeTrace (step Q) (cap W) t (relabelCfg labels ret x) (relabelCfg labels ret y) := by
  apply tr.map (relabelCfg labels ret) _ (fun _ h => h)
  intro a b h
  let frame := relabelCfg labels ret a
  simpa only [embedCfg_id] using relocate_step p Q id id labels ret frame Function.injective_id Function.injective_id code h

theorem join {n m' W : ℕ} {u v w : Fin r→Bool} {a b c : Fin s→List Bool}
    (left : SafeTrace (step p) (cap W) n ⟨some p.entry,u,a⟩ ⟨none,v,b⟩)
    (right : SafeTrace (step q) (cap W) m' ⟨some q.entry,v,b⟩ ⟨none,w,c⟩) :
    SafeTrace (step (link p q)) (cap W) (n+m') ⟨some (link p q).entry,u,a⟩ ⟨none,w,c⟩ := by
  have tr := relabel p (link p q) (Fin.castAdd m) (some (Fin.natAdd l q.entry)) (linkInto_leftCode p q id id id id) left
  have thenTr := relabel q (link p q) (Fin.natAdd l) none (linkInto_rightCode p q id id id id) right
  exact tr.trans thenTr

/-- Each callback may use fresh register values. Its own prefix bound is preserved through arbitrarily many full iterations. -/
theorem repeatBounded {S : Type} (flag : Fin r) (f : S→S) (ongoing : S→Bool) (V : S→Fin s→List Bool)
    (W : ℕ) (budget : S→ℕ) (n : ℕ) (z : S) (reg : Fin r→Bool)
    (flag0 : reg flag=ongoing z) (stop : ongoing (f^[n] z)=false)
    (mem : ∀ j,j≤n → ∀ i,(V (f^[j] z) i).length≤W)
    (blocks : ∀ j,j<n → let s := f^[j] z
      ongoing s=true ∧ ∀ r0 : Fin r→Bool,r0 flag=true →
        ∃ t r1,t ≤ budget s ∧ r1 flag=ongoing (f s) ∧
          SafeTrace (step p) (cap W) t ⟨some p.entry,r0,V s⟩ ⟨none,r1,V (f s)⟩) :
    ∃ t rf,t ≤ 2+n+∑ j∈Finset.range n,budget (f^[j] z) ∧
      SafeTrace (step (loop p flag)) (cap W) t
        ⟨some (loop p flag).entry,reg,V z⟩ ⟨none,rf,V (f^[n] z)⟩ := by
  induction n generalizing z reg with
  | zero =>
    have space := mem 0 (by omega)
    let c : Cfg r s (2+l) := ⟨some head,reg,V z⟩
    have h := test p flag c rfl
    change ongoing z=false at stop
    simp only [c,flag0,stop,Bool.false_eq_true,if_false] at h
    exact ⟨2,reg,by simp,.cons space h (.cons space (halt p flag _ rfl) (.refl _ space))⟩
  | succ n ih =>
    obtain ⟨yes,call⟩ := blocks 0 (by omega)
    obtain ⟨t,reg',cost,hreg,tr⟩ := call reg (flag0.trans yes)
    let c : Cfg r s (2+l) := ⟨some head,reg,V z⟩
    have h := test p flag c rfl
    have yes' : ongoing z=true := yes
    simp only [c,flag0,yes',if_true] at h
    have before := SafeTrace.cons (show cap W c from mem 0 (by omega)) h (block p flag tr)
    obtain ⟨k,rf,time,rest⟩ := ih (f z) reg' hreg (by simpa only [Function.iterate_succ_apply] using stop)
      (fun j hj => by simpa only [Function.iterate_succ_apply] using mem (j+1) (by omega))
      (fun j hj => by simpa only [Function.iterate_succ_apply] using blocks (j+1) (by omega))
    refine ⟨(t+1)+k,rf,?_,before.trans rest⟩
    rw [Finset.sum_range_succ']; simp only [Function.iterate_succ_apply,Function.iterate_zero_apply] at *
    omega
end DetDLP.BoundedProgramLink
end

noncomputable section
namespace DetDLP.CallOnPorts
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BoundedProgramLoop
variable {r s l R S : ℕ} (p : Program r s l) (reg : Fin r→Fin R) (ports : Fin s→Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective ports)
include hr hs in
theorem run {W n : ℕ} (a b : Fin S→List Bool) (small big : Fin s→List Bool) (r₀ : Fin R→Bool) (rf : Fin r→Bool)
    (pre : ∀ i,a (ports i)=small i) (post : ∀ i,b (ports i)=big i)
    (frameEq : ∀ i,(¬∃ j,ports j=i)→b i=a i)
    (room : ∀ i,(¬∃ j,ports j=i)→(a i).length≤W)
    (tr : SafeTrace (step p) (cap W) n ⟨some p.entry,r₀ ∘ reg,small⟩ ⟨none,rf,big⟩) :
    ∃ r',SafeTrace (step (liftProgram p reg ports)) (cap W) n
      ⟨some (liftProgram p reg ports).entry,r₀,a⟩ ⟨none,r',b⟩ := by
  classical
  let Q := liftProgram p reg ports
  let start : Cfg R S l := ⟨some Q.entry,r₀,a⟩
  let emb := embedCfg reg ports id none start
  have applyTr := tr.map emb (g:=step Q) (Q:=cap W) (by
    intro u v eq
    exact relocate_step p Q reg ports id none start hr hs (fun _ => rfl) eq)
    (by intro c hc i; by_cases mem : ∃ j,ports j=i
        · obtain ⟨j,rfl⟩ := mem; dsimp only [emb]; rw [embedCfg_stack _ _ _ _ _ _ hs]; exact hc j
        · dsimp only [emb]; rw [embedCfg_stack_frame _ _ _ _ _ _ _ mem]; exact room i mem)
  let r' := Function.extend reg rf r₀
  have e₀ : emb ⟨some p.entry,r₀ ∘ reg,small⟩=start := by
    apply embedCfg_eq_of_ports _ _ _ _ _ _ _ hr hs
    · rfl
    · intro i; rfl
    · intro i hi; rfl
    · exact pre
    · intro i hi; rfl
  have e₁ : emb ⟨none,rf,big⟩=⟨none,r',b⟩ := by
    apply embedCfg_eq_of_ports _ _ _ _ _ _ _ hr hs
    · rfl
    · intro i; exact hr.extend_apply .. 
    · intro i hi; exact Function.extend_apply' _ _ _ hi
    · exact post
    · exact frameEq
  rw [e₀,e₁] at applyTr
  exact ⟨r',applyTr⟩
end DetDLP.CallOnPorts
end

noncomputable section

namespace DetDLP.BitTracePolynomial
open OAI.Algorithms.SubexponentialSAT

private theorem instr_grows {r s l : ℕ} (op : BitProgram.Instr r s l) (a : BitProgram.Cfg r s l) (i : Fin s) :
    ((BitProgram.execInstr op a).stacks i).length ≤ (a.stacks i).length+1 := by
  cases op <;> simp [BitProgram.execInstr,Function.update_apply] <;>
    split_ifs <;> simp_all <;> omega

theorem trace_grows {r s l : ℕ} {p : BitProgram.Program r s l} {a b : BitProgram.Cfg r s l}
    {k : ℕ} (h : BitProgram.Trace p k a b) (i : Fin s) :
    (b.stacks i).length ≤ (a.stacks i).length+k := by
  induction h with
  | refl => simp
  | @cons k a c b hs tr ih =>
    obtain ⟨lab,_,he⟩ := Option.map_eq_some_iff.mp hs
    subst c
    have := instr_grows (p.code lab) a i
    omega



end DetDLP.BitTracePolynomial
end

noncomputable section
namespace DetDLP.EntryCallPreparation
def size (desc vert bits : List Bool) := desc.length+vert.length+bits.length
end DetDLP.EntryCallPreparation
namespace DetDLP.EntryEvaluatorCall
open OAI.Algorithms.SubexponentialSAT BitProgram BoundedProgramLoop
def budget (e s U : ℕ) := (e+4)*(20*(s+U+10))
theorem mono {r s l W W' : ℕ} {p : Program r s l} {n : ℕ} {x y : Cfg r s l}
    (h : SafeTrace (step p) (cap W) n x y) (le : W ≤ W') : SafeTrace (step p) (cap W') n x y :=
  h.map id (fun _ _ h => h) (fun _ h i => (h i).trans le)
end DetDLP.EntryEvaluatorCall
end

noncomputable section

namespace DetDLP.BitNormalize
open OAI.Algorithms.SubexponentialSAT BitProgram

/-- Remove high-order padding from a little-endian integer on stack zero. -/
def program : Program 2 2 10 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 3, .push 1 0 0,
    .pop 1 0 1 4, .branch 1 5 9, .branch 0 6 3, .push 0 0 7,
    .pop 1 0 1 8, .branch 1 6 9, .halt]

private def cf (pc : Option (Fin 10)) (r : Fin 2 → Bool) (x y : List Bool) : Cfg 2 2 10 :=
  ⟨pc,r,![x,y]⟩

private def regs (v p : Bool) : Fin 2 → Bool := ![v,p]

private theorem reg (r : Fin 2 → Bool) (o : Option Bool) :
    readRegs r 0 1 o = regs (o.getD false) o.isSome := by funext i; fin_cases i <;> simp [readRegs,regs]
private theorem u0 (x y z : List Bool) : Function.update ![x,y] (0 : Fin 2) z = ![z,y] := by
  funext i; fin_cases i <;> simp [Function.update_apply]
private theorem u1 (x y z : List Bool) : Function.update ![x,y] (1 : Fin 2) z = ![x,z] := by
  funext i; fin_cases i <;> simp [Function.update_apply]

private theorem reverse_phase (xs ys : List Bool) (r : Fin 2 → Bool) :
    Trace program (3*xs.length+2) (cf (some 0) r xs ys)
      (cf (some 3) (regs false false) [] (xs.reverse++ys)) := by
  induction xs generalizing r ys with
  | nil =>
    refine .cons (b := cf (some 1) (regs false false) [] ys) ?_ (.cons (by rfl) (.refl _))
    simp [step,execInstr,cf,program,reg,u0]
  | cons b xs ih =>
    rw [List.length_cons,show 3*(xs.length+1)+2=(3*xs.length+2)+1+1+1 by omega]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    refine .cons (b := cf (some 1) (regs b true) xs ys) ?_
      (.cons (b := cf (some 2) (regs b true) xs ys) (by rfl) (.cons ?_ (ih (b::ys) (regs b true))))
    · simp [step,execInstr,cf,program,reg,u0]
    · simp [step,execInstr,cf,program,regs,u1]

private theorem restore_phase (xs ys : List Bool) (r : Fin 2 → Bool) :
    Trace program (3*ys.length+3) (cf (some 7) r xs ys)
      (cf none (regs false false) (ys.reverse++xs) []) := by
  induction ys generalizing r xs with
  | nil =>
    refine .cons (b := cf (some 8) (regs false false) xs []) ?_ (.cons (b := cf (some 9) (regs false false) xs []) (by rfl) (.cons (by rfl) (.refl _)))
    simp [step,execInstr,cf,program,reg,u1]
  | cons b ys ih =>
    rw [List.length_cons,show 3*(ys.length+1)+3=(3*ys.length+3)+1+1+1 by omega]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
    refine .cons (b := cf (some 8) (regs b true) xs ys) ?_
      (.cons (b := cf (some 6) (regs b true) xs ys) (by rfl) (.cons ?_ (ih (b::xs) (regs b true))))
    · simp [step,execInstr,cf,program,reg,u1]
    · simp [step,execInstr,cf,program,regs,u0]

private def dropZeros : List Bool → List Bool
  | [] => []
  | false::xs => dropZeros xs
  | true::xs => true::xs

private theorem strip_phase (ys : List Bool) (r : Fin 2 → Bool) :
    ∃ k ≤ 3*ys.length+5, Trace program k (cf (some 3) r [] ys)
      (cf none (regs false false) (dropZeros ys).reverse []) := by
  induction ys generalizing r with
  | nil =>
    refine ⟨3,by decide,.cons (b := cf (some 4) (regs false false) [] []) ?_
      (.cons (b := cf (some 9) (regs false false) [] []) (by rfl) (.cons (by rfl) (.refl _)))⟩
    simp [step,execInstr,cf,program,reg,u1]
  | cons b ys ih =>
    cases b with
    | false =>
      obtain ⟨k,hk,tr⟩ := ih (regs false true)
      refine ⟨k+3,by simp; omega,.cons (b := cf (some 4) (regs false true) [] ys) ?_
        (.cons (b := cf (some 5) (regs false true) [] ys) (by rfl) (.cons (by rfl) tr))⟩
      simp [step,execInstr,cf,program,reg,u1]
    | true =>
      have ht := restore_phase [true] ys (regs true true)
      rw [← List.reverse_cons] at ht
      refine ⟨3*ys.length+3+4,by simp; omega,.cons (b := cf (some 4) (regs true true) [] ys) ?_
        (.cons (b := cf (some 5) (regs true true) [] ys) (by rfl)
          (.cons (b := cf (some 6) (regs true true) [] ys) (by rfl) (.cons ?_ ht)))⟩
      · simp [step,execInstr,cf,program,reg,u1]
      · simp [step,execInstr,cf,program,regs,u0]


private theorem canon_high (ys : List Bool) :
    (dropZeros ys).reverse = (BinaryArithmetic.toNat ys.reverse).bits := by
  induction ys using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys b ih =>
    rw [List.reverse_append,List.reverse_singleton,List.singleton_append]
    have hstep : BinaryArithmetic.toNat (b::ys.reverse) = Nat.bit b (BinaryArithmetic.toNat ys.reverse) := by
      cases b <;> simp [Nat.bit,BinaryArithmetic.toNat_cons] <;> omega
    rw [hstep]
    by_cases hy : dropZeros ys = []
    · have hz : BinaryArithmetic.toNat ys.reverse = 0 := by
        have hx := ih.symm; rw [hy] at hx
        have hl := congrArg List.length hx
        rw [Nat.size_eq_bits_len] at hl
        exact Nat.size_eq_zero.mp hl
      have ha : dropZeros (ys++[b]) = dropZeros [b] := by
        clear ih hz hstep
        induction ys with
        | nil => rfl
        | cons v ys ih =>
          cases v with
          | false => exact ih hy
          | true => simp [dropZeros] at hy
      rw [ha,hz]; cases b <;> decide
    · have hv : BinaryArithmetic.toNat ys.reverse ≠ 0 := by
        intro hz; rw [hz] at ih; simp_all
      have ha : dropZeros (ys++[b]) = dropZeros ys++[b] := by
        clear ih hv hstep
        induction ys with
        | nil => contradiction
        | cons v ys ih =>
          cases v with
          | false => exact ih hy
          | true => rfl
      rw [ha,List.reverse_append,List.reverse_singleton,List.singleton_append,ih,Nat.bits_append_bit _ _ (fun e => (hv e).elim)]

/-- Canonical output and a linear instruction bound for every word, including padded zero. -/
theorem normalizes (xs : List Bool) (r : Fin 2 → Bool) :
    ∃ k ≤ 6*xs.length+7, Trace program k (cf (some 0) r xs [])
      (cf none (regs false false) (BinaryArithmetic.toNat xs).bits []) := by
  have h := reverse_phase xs [] r; simp only [List.append_nil] at h
  obtain ⟨k,hk,hh⟩ := strip_phase xs.reverse (regs false false)
  rw [canon_high,List.reverse_reverse] at hh
  exact ⟨_,by simp only [List.length_reverse] at hk; omega,h.trans hh⟩

end DetDLP.BitNormalize
end

noncomputable section

namespace DetDLP.BitNormalize
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking

private theorem cfg_eq {r s l : ℕ} {a b : Cfg r s l} (hp : a.pc=b.pc) (hr : a.regs=b.regs)
    (hs : a.stacks=b.stacks) : a=b := by cases a; cases b; simp_all

private def regMap : Fin 2 → Fin 8 := Fin.castAdd 6
private def ports (k t : Fin 8) : Fin 2 → Fin 8 := ![k,t]
private theorem ports_inj {k t : Fin 8} (h : k ≠ t) : Function.Injective (ports k t) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp_all [ports,Ne.symm h]

def atPort (k t : Fin 8) := liftProgram program regMap (ports k t)

theorem atPort_runs (k t : Fin 8) (hk : k ≠ t) (r : Fin 8 → Bool) (stk : Fin 8 → List Bool)
    (ht : stk t = []) :
    ∃ rf : Fin 8 → Bool, RunsIn (atPort k t) (6*(stk k).length+7)
      ⟨some 0,r,stk⟩ ⟨none,rf,Function.update stk k (BinaryArithmetic.toNat (stk k)).bits⟩ := by
  let frame : Cfg 8 8 10 := ⟨none,r,stk⟩
  have hr : Function.Injective regMap := Fin.castAdd_injective _ _
  have hs := ports_inj hk
  obtain ⟨n,hn,h⟩ := normalizes (stk k) (r ∘ regMap)
  change Trace program n ⟨some 0,r ∘ regMap,![stk k,[]]⟩
      ⟨none,![false,false],![(BinaryArithmetic.toNat (stk k)).bits,[]]⟩ at h
  have tr := liftProgram_trace program regMap (ports k t) frame hr hs h
  let start : Cfg 2 2 10 := ⟨some 0,r ∘ regMap,![stk k,[]]⟩
  let finish : Cfg 2 2 10 := ⟨none,![false,false],![(BinaryArithmetic.toNat (stk k)).bits,[]]⟩
  have e0 : embedCfg regMap (ports k t) id none frame start = ⟨some 0,r,stk⟩ := by
    refine cfg_eq rfl ?_ ?_
    · funext j
      by_cases hj : ∃ x,regMap x = j
      · obtain ⟨x,rfl⟩ := hj; exact hr.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ hj
    · funext j
      by_cases hj : ∃ x,ports k t x = j
      · obtain ⟨x,rfl⟩ := hj
        rw [embedCfg_stack _ _ _ _ _ _ hs]; fin_cases x <;> simp [ports,start,ht]
      · exact Function.extend_apply' _ _ _ hj
  let final := embedCfg regMap (ports k t) id none frame finish
  have e1 : final = ⟨none,final.regs,Function.update stk k (BinaryArithmetic.toNat (stk k)).bits⟩ := by
    refine cfg_eq rfl rfl ?_
    funext j
    by_cases hj : ∃ x, ports k t x = j
    · obtain ⟨x,rfl⟩ := hj
      dsimp only [final]
      rw [embedCfg_stack _ _ _ _ _ _ hs]
      fin_cases x <;> simp [ports,finish,Function.update_apply,hk,hk.symm,ht]
    · have hjk : j ≠ k := fun h => hj ⟨0,by simp [ports,h]⟩
      change final.stacks j = Function.update stk k (BinaryArithmetic.toNat (stk k)).bits j
      rw [Function.update_of_ne hjk]
      exact Function.extend_apply' _ _ _ hj
  refine ⟨final.regs,n,hn,?_⟩
  change Trace (atPort k t) n (embedCfg regMap (ports k t) id none frame start) final at tr
  rw [e0,e1] at tr
  exact tr

end DetDLP.BitNormalize
end

noncomputable section

namespace DetDLP.BitEuclidDivision
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking ModularQuotientPrograms

private def cleanup := link (BitNormalize.atPort 0 1) (BitNormalize.atPort 7 1)
def divide := link quotientProgram cleanup

/-- Both results have canonical binary lengths before they are used by the next Euclidean iteration. -/
theorem divide_correct (regs : Fin 8 → Bool) (m x : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    ∃ rf, RunsIn divide (125*(m.length+x.length+1)^2)
        ⟨some 0,regs,quotientStacks [] m x []⟩
        ⟨none,rf,quotientStacks (BinaryArithmetic.toNat x % BinaryArithmetic.toNat m).bits m []
                  (BinaryArithmetic.toNat x / BinaryArithmetic.toNat m).bits⟩ := by
  obtain ⟨r1,q,b,hdiv,hq,hb,vq,vb⟩ := quotient_value regs m x hm
  let stk := quotientStacks b m [] q
  obtain ⟨r2,hbtr⟩ := BitNormalize.atPort_runs 0 1 (by decide) r1 stk rfl
  let b' := (BinaryArithmetic.toNat b).bits
  have e0 : Function.update stk 0 b' = quotientStacks b' m [] q := by
    funext i; fin_cases i <;> simp [stk,quotientStacks,Function.update_apply]
  change RunsIn (BitNormalize.atPort 0 1) (6*b.length+7)
      ⟨some 0,r1,stk⟩ ⟨none,r2,Function.update stk 0 b'⟩ at hbtr
  rw [e0] at hbtr
  obtain ⟨r3,hqtr⟩ := BitNormalize.atPort_runs 7 1 (by decide) r2 (quotientStacks b' m [] q) rfl
  let q' := (BinaryArithmetic.toNat q).bits
  have e7 : Function.update (quotientStacks b' m [] q) 7 q' = quotientStacks b' m [] q' := by
    funext i; fin_cases i <;> simp [quotientStacks,Function.update_apply]
  change RunsIn (BitNormalize.atPort 7 1) (6*q.length+7)
      ⟨some 0,r2,quotientStacks b' m [] q⟩ ⟨none,r3,Function.update (quotientStacks b' m [] q) 7 q'⟩ at hqtr
  rw [e7] at hqtr
  have hclean := link_runsIn _ _ hbtr rfl hqtr
  change RunsIn cleanup _ ⟨some 0,r1,stk⟩ ⟨none,r3,quotientStacks b' m [] q'⟩ at hclean
  have h := link_runsIn _ _ hdiv rfl hclean
  change RunsIn divide _ ⟨some 0,regs,quotientStacks [] m x []⟩ ⟨none,r3,quotientStacks b' m [] q'⟩ at h
  dsimp only [b',q'] at h; rw [vq,vb] at h
  refine ⟨r3,h.mono ?_⟩
  rw [hq,hb]; nlinarith only [Nat.zero_le m.length,Nat.zero_le x.length,Nat.zero_le (m.length*x.length),
    Nat.zero_le (x.length^2),Nat.zero_le (m.length^2)]
end DetDLP.BitEuclidDivision
end

noncomputable section

namespace DetDLP.BoundedExtendedEuclid

/-- Two successive remainders and their signed coefficient rows. -/
structure State where
  r : ℕ
  u : ℤ
  v : ℤ
  oldR : ℕ
  oldU : ℤ
  oldV : ℤ
  deriving Repr

def step (s : State) : State :=
  if s.r = 0 then s else
    let q : ℤ := s.oldR/s.r
    ⟨s.oldR%s.r,s.oldU-q*s.u,s.oldV-q*s.v,s.r,s.u,s.v⟩

def run : ℕ → State → State
  | 0,s => s
  | k+1,s => run k (step s)

private def result (s : State) := Nat.xgcdAux s.r s.u s.v s.oldR s.oldU s.oldV






private def Bounded (M A : ℕ) (s : State) :=
  s.r ≤ M ∧ s.oldR ≤ M ∧ s.u.natAbs ≤ A ∧ s.v.natAbs ≤ A ∧ s.oldU.natAbs ≤ A ∧ s.oldV.natAbs ≤ A



def init (x y : ℕ) : State := ⟨x,1,0,y,0,1⟩

end DetDLP.BoundedExtendedEuclid
end

noncomputable section

namespace DetDLP.BitEuclidLoop
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls ModularQuotientPrograms
open StackRoutines

abbrev Code := Cmd 8 8
abbrev Data := State 8 8
abbrev regs := Fin 8 → Bool
abbrev Stk := Fin 8 → List Bool

theorem nat_bits (n : ℕ) : BinaryArithmetic.toNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit _ _ h,BinaryArithmetic.toNat_cons,ih]
    cases b <;> simp [Nat.bit] <;> omega

private abbrev transfer (src dst : Fin 8) : Code := .call (transferProgram src dst 0 1)
private def move (src dst : Fin 8) : Code := .seq (transfer src 1) (transfer 1 dst)


private def peek : Code := .base (.atom (.peek 5 0 1))
private abbrev peekR (r : regs) (w : List Bool) := readRegs r 0 1 w.head?

private def body : Code := .seq (.call BitEuclidDivision.divide)
  (.seq (ArithmeticExpressionSupport.clearCmd 7)
    (.seq (move 5 6) (.seq (move 0 5) peek)))
def code : Code := .seq peek (.while 1 body)

private abbrev store (d x : ℕ) : Stk := quotientStacks [] d.bits x.bits []



open BoundedExtendedEuclid in

open BoundedExtendedEuclid in

/-- Fixed eight-stack GCD table, including the zero case. Every division returns
canonical words before the next guard is tested. -/
def program := compiled code 5 6

end DetDLP.BitEuclidLoop
end

noncomputable section

namespace DetDLP.BitArithmeticUnit
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls ModularQuotientPrograms
open ArithmeticExpressionSupport
abbrev Code := Cmd 8 8
abbrev Data := State 8 8
abbrev Regs := Fin 8 → Bool

inductive Op where | add | mul | quot | rem
  deriving DecidableEq, Repr

def Op.eval : Op → ℕ → ℕ → ℕ
  | .add,m,x => m+x
  | .mul,m,x => m*x
  | .quot,m,x => x/m
  | .rem,m,x => x%m

def Op.Valid (op : Op) (m : ℕ) := (op = .quot ∨ op = .rem) → 0 < m

private def ports : ArithmeticCalls.Ports 8 where
  left := 5
  right := 6
  out := 7
  work := ⟨Fin.castAdd 3,Fin.castAdd_injective 5 3⟩
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by decide
  work_ne_right := by decide
  work_ne_out := by decide

private def normalize : Code := .call (BitNormalize.atPort 7 1)
private def posop (op : Bool) : Code := .seq
  (if op then ArithmeticCalls.multiplyAt ports else ArithmeticCalls.addAt ports)
  (.seq (clearCmd 5) (.seq (clearCmd 6) normalize))

private theorem posop_correct (op : Bool) (r : Regs) (m x : ℕ) :
    ∃ n rf, n ≤ 160*(m.size+x.size+1)^2 ∧
      Eval (posop op) n ⟨r,quotientStacks [] m.bits x.bits []⟩
        ⟨rf,quotientStacks [] [] [] (if op then m*x else m+x).bits⟩ := by
  let d : Data := ⟨r,quotientStacks [] m.bits x.bits []⟩
  have hv : ArithmeticCalls.Valid ports d := ⟨rfl,by intro i; fin_cases i <;> rfl⟩
  have he : ∃ t rf word,
      Eval (if op then ArithmeticCalls.multiplyAt ports else ArithmeticCalls.addAt ports) t d
        ⟨rf,Function.update d.stacks ports.out word⟩ ∧
      BinaryArithmetic.toNat word = (if op then m*x else m+x) ∧
      word.length ≤ m.bits.length+x.bits.length+1 ∧ t ≤ 100*(m.bits.length+x.bits.length+1)^2 := by
    cases op
    · simpa [d,ports,BitEuclidLoop.nat_bits] using ArithmeticCalls.addAt_eval ports d hv
    · simpa [d,ports,BitEuclidLoop.nat_bits] using ArithmeticCalls.multiplyAt_eval ports d hv
  obtain ⟨n,r₁,w,he,hw,hl,hn⟩ := he
  have e1 : Function.update d.stacks ports.out w = quotientStacks [] m.bits x.bits w := by funext i; fin_cases i <;> rfl
  rw [e1] at he
  have h₂ := clear_eval 5 (⟨r₁,quotientStacks [] m.bits x.bits w⟩ : Data)
  have e2 : Function.update (quotientStacks [] m.bits x.bits w) 5 [] = quotientStacks [] [] x.bits w := by funext i; fin_cases i <;> rfl
  rw [e2] at h₂
  have h₃ := clear_eval 6 (⟨readRegs r₁ 0 1 none,quotientStacks [] [] x.bits w⟩ : Data)
  have e3 : Function.update (quotientStacks [] [] x.bits w) 6 [] = quotientStacks [] [] [] w := by funext i; fin_cases i <;> rfl
  rw [e3] at h₃
  obtain ⟨r₄,k,hk,ht⟩ := BitNormalize.atPort_runs 7 1 (by decide)
    (readRegs (readRegs r₁ 0 1 none) 0 1 none) (quotientStacks [] [] [] w) rfl
  change Trace _ k _ ⟨none,r₄,Function.update (quotientStacks [] [] [] w) 7 (BinaryArithmetic.toNat w).bits⟩ at ht
  have e4 : Function.update (quotientStacks [] [] [] w) 7 (BinaryArithmetic.toNat w).bits =
      quotientStacks [] [] [] (if op then m*x else m+x).bits := by rw [hw]; funext i; fin_cases i <;> rfl
  rw [e4] at ht
  have ht' : Eval normalize k ⟨_,quotientStacks [] [] [] w⟩ ⟨r₄,quotientStacks [] [] [] (if op then m*x else m+x).bits⟩ := .call _ ht
  refine ⟨_,_,?_,.seq he (.seq h₂ (.seq h₃ ht'))⟩
  change n+(2*m.bits.length+3+(2*x.bits.length+3+k)) ≤ _
  change k ≤ 6*w.length+7 at hk
  simp only [Nat.size_eq_bits_len] at hn hl ⊢
  nlinarith only [hn,hl,hk,Nat.zero_le (m.size^2),Nat.zero_le (x.size^2),Nat.zero_le (m.size*x.size),Nat.zero_le m.size,Nat.zero_le x.size]

private def divop (remainder : Bool) : Code :=
  .seq (.call BitEuclidDivision.divide) (.seq (clearCmd 5)
    (if remainder then .seq (clearCmd 7) (ArithmeticCalls.copyAt 0 7 1) else clearCmd 0))

private def divClean (remainder : Bool) : Code := .seq (divop remainder) (clearCmd 0)

private theorem divop_correct (rem : Bool) (r : Regs) (m x : ℕ) (hm : 0 < m) :
    ∃ n rf, n ≤ 160*(m.size+x.size+1)^2 ∧
      Eval (divClean rem) n ⟨r,quotientStacks [] m.bits x.bits []⟩
        ⟨rf,quotientStacks [] [] [] (if rem then x%m else x/m).bits⟩ := by
  obtain ⟨r₁,n,hn,ht⟩ := BitEuclidDivision.divide_correct r m.bits x.bits (by simpa [BitEuclidLoop.nat_bits] using hm)
  simp only [BitEuclidLoop.nat_bits] at ht
  let a := (x%m).bits
  let b := (x/m).bits
  have hd : Eval (.call BitEuclidDivision.divide) n ⟨r,quotientStacks [] m.bits x.bits []⟩ ⟨r₁,quotientStacks a m.bits [] b⟩ := .call _ ht
  have hc := clear_eval 5 (⟨r₁,quotientStacks a m.bits [] b⟩ : Data)
  have e : Function.update (quotientStacks a m.bits [] b) 5 [] = quotientStacks a [] [] b := by funext i; fin_cases i <;> rfl
  rw [e] at hc
  let r₂ := readRegs r₁ 0 1 none
  have ha : a.length ≤ x.size := by dsimp [a]; rw [Nat.size_eq_bits_len]; exact Nat.size_le_size (Nat.mod_le ..)
  have hb : b.length ≤ x.size := by dsimp [b]; rw [Nat.size_eq_bits_len]; exact Nat.size_le_size (Nat.div_le_self ..)
  rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len] at hn
  cases rem with
  | false =>
    have h₃ := clear_eval 0 (⟨r₂,quotientStacks a [] [] b⟩ : Data)
    have e₃ : Function.update (quotientStacks a [] [] b) 0 [] = quotientStacks [] [] [] b := by funext i; fin_cases i <;> rfl
    rw [e₃] at h₃
    have h₄ := clear_eval 0 (⟨readRegs r₂ 0 1 none,quotientStacks [] [] [] b⟩ : Data)
    rw [show Function.update (quotientStacks [] [] [] b) 0 [] = quotientStacks [] [] [] b by funext i; fin_cases i <;> rfl] at h₄
    refine ⟨_,_,?_,.seq (.seq hd (.seq hc h₃)) h₄⟩
    change n+(2*m.bits.length+3+(2*a.length+3))+3 ≤ _
    rw [Nat.size_eq_bits_len]
    nlinarith only [hn,ha,Nat.zero_le (m.size^2),Nat.zero_le (x.size^2),Nat.zero_le (m.size*x.size),Nat.zero_le m.size,Nat.zero_le x.size]
  | true =>
    have h₃ := clear_eval 7 (⟨r₂,quotientStacks a [] [] b⟩ : Data)
    have e₃ : Function.update (quotientStacks a [] [] b) 7 [] = quotientStacks a [] [] [] := by funext i; fin_cases i <;> rfl
    rw [e₃] at h₃
    have h₄ := ArithmeticCalls.copyAt_eval 0 7 1 (⟨readRegs r₂ 0 1 none,quotientStacks a [] [] []⟩ : Data)
      (by decide) (by decide) (by decide) rfl rfl
    have e₄ : Function.update (quotientStacks a [] [] []) 7 a = quotientStacks a [] [] a := by funext i; fin_cases i <;> rfl
    change Eval _ (7*a.length+5) _ ⟨_,Function.update (quotientStacks a [] [] []) 7 a⟩ at h₄
    rw [e₄] at h₄
    have h₅ := clear_eval 0 (⟨readRegs (readRegs r₂ 0 1 none) 0 1 none,quotientStacks a [] [] a⟩ : Data)
    rw [show Function.update (quotientStacks a [] [] a) 0 [] = quotientStacks [] [] [] a by funext i; fin_cases i <;> rfl] at h₅
    refine ⟨_,_,?_,.seq (.seq hd (.seq hc (.seq h₃ h₄))) h₅⟩
    change n+(2*m.bits.length+3+(2*b.length+3+(7*a.length+5)))+(2*a.length+3) ≤ _
    rw [Nat.size_eq_bits_len]
    nlinarith only [hn,ha,hb,Nat.zero_le (m.size^2),Nat.zero_le (x.size^2),Nat.zero_le (m.size*x.size),Nat.zero_le m.size,Nat.zero_le x.size]

def code : Op → Code
  | .add => posop false
  | .mul => posop true
  | .quot => divClean false
  | .rem => divClean true

theorem correct (op : Op) (r : Regs) (m x : ℕ) (hv : op.Valid m) :
    ∃ n rf, n ≤ 160*(m.size+x.size+1)^2 ∧
      Eval (code op) n ⟨r,quotientStacks [] m.bits x.bits []⟩ ⟨rf,quotientStacks [] [] [] (op.eval m x).bits⟩ := by
  cases op with
  | add => exact posop_correct false r m x
  | mul => exact posop_correct true r m x
  | quot => exact divop_correct false r m x (hv (Or.inl rfl))
  | rem => exact divop_correct true r m x (hv (Or.inr rfl))
end DetDLP.BitArithmeticUnit
end

noncomputable section
namespace DetDLP.BitRegisterBank
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls ModularQuotientPrograms
open ArithmeticExpressionSupport BitArithmeticUnit

abbrev Vars (n : ℕ) := Fin n → ℕ
abbrev S (n : ℕ) := Fin (8+n)
abbrev Code (n : ℕ) := Cmd 8 (8+n)
abbrev low {n : ℕ} (i : Fin 8) : S n := Fin.castAdd n i
abbrev port {n : ℕ} (i : Fin n) : S n := Fin.natAdd 8 i

theorem low_ne_port {n : ℕ} (i : Fin 8) (j : Fin n) : low i ≠ port j := by
  intro he; have hh := congrArg Fin.val he
  change i.val = 8+j.val at hh; omega
def store {n : ℕ} (work : Fin 8 → List Bool) (v : Vars n) : S n → List Bool :=
  Fin.addCases work (fun j => (v j).bits)
@[simp] theorem store_low {n} (w : Fin 8 → List Bool) (v : Vars n) (i : Fin 8) :
    store w v (low i) = w i := Fin.addCases_left ..
@[simp] theorem store_port {n} (w : Fin 8 → List Bool) (v : Vars n) (i : Fin n) :
    store w v (port i) = (v i).bits := Fin.addCases_right ..

private theorem upd_low {n} (w : Fin 8 → List Bool) (v : Vars n) (i : Fin 8) (xs : List Bool) :
    Function.update (store w v) (low i) xs = store (Function.update w i xs) v := by
  funext j; refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · change Function.update (store w v) (low i) xs (low l) = store _ _ (low l)
    simp [Function.update_apply,apply_ite,Fin.castAdd_inj]
    split <;> simp_all
  · change Function.update (store w v) (low i) xs (port l) = store _ _ (port l)
    simp [Function.update_of_ne (low_ne_port i l).symm]
private theorem upd_port {n} (w : Fin 8 → List Bool) (v : Vars n) (i : Fin n) (x : ℕ) :
    Function.update (store w v) (port i) x.bits = store w (Function.update v i x) := by
  funext j; refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · change Function.update (store w v) (port i) x.bits (low l) = store _ _ (low l)
    simp [Function.update_of_ne (low_ne_port l i)]
  · change Function.update (store w v) (port i) x.bits (port l) = store _ _ (port l)
    by_cases hl : l=i
    · subst l; simp
    · have he : port l ≠ port i := fun h => hl (Fin.natAdd_injective _ _ h)
      simp [Function.update_of_ne he,Function.update_of_ne hl]

private def alu {n : ℕ} (op : Op) : Code n :=
  .call (ProgramLinking.liftProgram (compiled (BitArithmeticUnit.code op) 5 7) id low)
private def empty : Fin 8 → List Bool := fun _ => []

def assign {n : ℕ} (op : Op) (a b dst : Fin n) : Code n :=
  .seq (ArithmeticCalls.copyAt (port a) (low 5) (low 1))
    (.seq (ArithmeticCalls.copyAt (port b) (low 6) (low 1))
      (.seq (alu op) (.seq (clearCmd (port dst))
        (.seq (ArithmeticCalls.copyAt (low 7) (port dst) (low 1)) (clearCmd (low 7))))))

private theorem alu_eval {n : ℕ} (op : Op) (r : Regs) (a b : ℕ) (v : Vars n) (hv : op.Valid a) :
    ∃ t rf, t ≤ 160*(a.size+b.size+1)^2+1 ∧
      Eval (alu op) t ⟨r,store (quotientStacks [] a.bits b.bits []) v⟩
        ⟨rf,store (quotientStacks [] [] [] (op.eval a b).bits) v⟩ := by
  obtain ⟨t,rf,ht,he⟩ := BitArithmeticUnit.correct op r a b hv
  let frame : State 8 (8+n) := ⟨r,store empty v⟩
  have hh := eval_call_lifted _ id (@low n) frame Function.injective_id (Fin.castAdd_injective 8 n)
    (compiled_halt_trace he 5 7)
  have hframe (r' : Regs) (w : Fin 8 → List Bool) :
      embedState id (@low n) frame ⟨r',w⟩ = ⟨r',store w v⟩ := by
    apply embedState_eq_of_ports id _ frame _ _ Function.injective_id (Fin.castAdd_injective 8 n)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; simp
    · intro j; refine Fin.addCases (fun i hi => (hi ⟨i,rfl⟩).elim) (fun i _ => ?_) j
      change store w v (port i) = store empty v (port i); simp
  rw [hframe,hframe] at hh
  exact ⟨_,rf,by omega,hh⟩
private theorem copyIn {n} (w : Fin 8 → List Bool) (v : Vars n) (a : Fin n) (i : Fin 8)
    (hn : i ≠ 1) (hw : w i = []) (ht : w 1 = []) (r : Regs) :
    ∃ rf, Eval (ArithmeticCalls.copyAt (port a) (low i) (low 1)) (7*(v a).bits.length+5)
      ⟨r,store w v⟩ ⟨rf,store (Function.update w i (v a).bits) v⟩ := by
  have hi : (@low n 1) ≠ low i := fun h => hn (Fin.castAdd_injective 8 n h.symm)
  have hh := ArithmeticCalls.copyAt_eval (port a) (low i) (low 1) (⟨r,store w v⟩ : State 8 (8+n))
    (low_ne_port i a).symm (low_ne_port 1 a).symm hi (by simpa using hw) (by simpa using ht)
  refine ⟨readRegs r 0 1 none,?_⟩
  simpa [ArithmeticCalls.afterCopy,upd_low] using hh

theorem assign_eval {n : ℕ} (op : Op) (a b dst : Fin n) (v : Vars n) (r : Regs)
    (hv : op.Valid (v a)) :
    let y := op.eval (v a) (v b)
    ∃ t rf, t ≤ 160*((v a).size+(v b).size+1)^2 +
        10*((v a).size+(v b).size+(v dst).size+y.size+4) ∧
      Eval (assign op a b dst) t ⟨r,store empty v⟩ ⟨rf,store empty (Function.update v dst y)⟩ := by
  intro y
  obtain ⟨r₁,e₁⟩ := copyIn empty v a 5 (by decide) rfl rfl r
  have hw1 : Function.update empty 5 (v a).bits = quotientStacks [] (v a).bits [] [] := by
    funext i; fin_cases i <;> rfl
  rw [hw1] at e₁
  obtain ⟨r₂,e₂⟩ := copyIn (quotientStacks [] (v a).bits [] []) v b 6 (by decide) rfl rfl r₁
  have hw2 : Function.update (quotientStacks [] (v a).bits [] []) 6 (v b).bits =
      quotientStacks [] (v a).bits (v b).bits [] := by funext i; fin_cases i <;> rfl
  rw [hw2] at e₂
  obtain ⟨t,r₃,ht,e₃⟩ := alu_eval op r₂ (v a) (v b) v hv
  let w := quotientStacks [] [] [] y.bits
  change Eval _ t _ ⟨r₃,store w v⟩ at e₃
  have e₄ := clear_eval (port dst) (⟨r₃,store w v⟩ : State 8 (8+n))
  rw [show Function.update (store w v) (port dst) [] = store w (Function.update v dst 0) from upd_port w v dst 0] at e₄
  let r₄ := readRegs r₃ 0 1 none
  let v' := Function.update v dst 0
  have e₅ := ArithmeticCalls.copyAt_eval (low 7) (port dst) (low 1) (⟨r₄,store w v'⟩ : State 8 (8+n))
    (low_ne_port 7 dst) (fun h => (by decide : (7:Fin 8) ≠ 1) (Fin.castAdd_injective 8 n h)) (low_ne_port 1 dst)
    (by simp [v']) (by simp [w])
  change Eval _ (7*(store w v' (low 7)).length+5) _ ⟨readRegs r₄ 0 1 none,Function.update (store w v') (port dst) (store w v' (low 7))⟩ at e₅
  rw [store_low] at e₅
  change Eval _ (7*y.bits.length+5) _ ⟨_,Function.update (store w v') (port dst) y.bits⟩ at e₅
  rw [upd_port] at e₅
  have hv' : Function.update v' dst y = Function.update v dst y := Function.update_idem ..
  rw [hv'] at e₅
  let r₅ := readRegs r₄ 0 1 none
  have e₆ := clear_eval (low 7) (⟨r₅,store w (Function.update v dst y)⟩ : State 8 (8+n))
  rw [upd_low] at e₆
  have hw6 : Function.update w 7 [] = empty := by funext i; fin_cases i <;> rfl
  rw [hw6] at e₆
  refine ⟨_,_,?_,.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))))⟩
  simp only [store_low,store_port,Nat.size_eq_bits_len]
  change 7*(v a).size+5+(7*(v b).size+5+(t+(2*(v dst).size+3+(7*y.size+5+(2*y.bits.length+3))))) ≤ _
  rw [Nat.size_eq_bits_len]; omega
end DetDLP.BitRegisterBank
end

noncomputable section
namespace DetDLP.BitRegisterCode
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls BitArithmeticUnit
open BitRegisterBank

structure Instr (n : ℕ) where
  op : Op
  a : Fin n
  b : Fin n
  dst : Fin n

def Instr.step {n} (s : Instr n) (v : Vars n) : Vars n :=
  Function.update v s.dst (s.op.eval (v s.a) (v s.b))

def run {n} : List (Instr n) → Vars n → Vars n
  | [],v => v
  | i::is,v => run is (i.step v)
def Valid {n} : List (Instr n) → Vars n → Prop
  | [],_ => True
  | i::is,v => i.op.Valid (v i.a) ∧ Valid is (i.step v)
def compile {n} : List (Instr n) → BitRegisterBank.Code n
  | [] => .base .skip
  | s::ss => .seq (assign s.op s.a s.b s.dst) (compile ss)
abbrev frame {n} (v : Vars n) := store (fun _ => []) v

private theorem size_op (op : Op) (a b W : ℕ) (ha : a.size ≤ W) (hb : b.size ≤ W) :
    (op.eval a b).size ≤ 2*W+1 := by
  have h1 := Nat.size_le.mp ha
  have h2 := Nat.size_le.mp hb
  have hpow : 2^W ≤ 2^(2*W) := Nat.pow_le_pow_right (by decide) (by omega)
  cases op with
  | add =>
    apply Nat.size_le.mpr; change a+b < 2^(2*W+1); rw [pow_succ]; omega
  | mul =>
    have hh := Nat.mul_lt_mul_of_lt_of_le h1 h2.le (by positivity : 0 < 2^W)
    apply Nat.size_le.mpr
    change a*b < 2^(2*W+1)
    rw [two_mul,pow_succ,pow_add]; nlinarith only [hh,Nat.zero_le (2^W*2^W)]
  | quot => exact (Nat.size_le_size (Nat.div_le_self b a)).trans (by omega)
  | rem => exact (Nat.size_le_size (Nat.mod_le b a)).trans (by omega)

theorem run_eval {n} (c : List (Instr n)) (v : Vars n) (r : Regs) (W : ℕ) (hW : ∀ j, (v j).size ≤ W)
    (hv : Valid c v) :
    ∃ t rf, t ≤ 1000^(c.length+1)*(W+2)^2 ∧
      Eval (compile c) t ⟨r,frame v⟩ ⟨rf,frame (run c v)⟩ := by
  induction c generalizing v r W with
  | nil => exact ⟨0,r,Nat.zero_le _,.base (.skip _)⟩
  | cons s ss ih =>
    obtain ⟨t₁,r₁,ht₁,e₁⟩ := assign_eval s.op s.a s.b s.dst v r hv.1
    let y := s.op.eval (v s.a) (v s.b)
    have hy : y.size ≤ 2*W+1 := size_op s.op _ _ _ (hW s.a) (hW s.b)
    have hm (j : Fin n) : ((s.step v) j).size ≤ 2*W+1 := by
      by_cases h : j=s.dst
      · subst j; simpa [Instr.step] using hy
      · simp [Instr.step,h]; exact (hW j).trans (by omega)
    obtain ⟨t₂,rf,ht₂,e₂⟩ := ih (s.step v) r₁ (2*W+1) hm hv.2
    refine ⟨_,_,?_,.seq e₁ e₂⟩
    have hab := Nat.pow_le_pow_left (show (v s.a).size+(v s.b).size+1 ≤ 2*(W+2) by have := hW s.a; have := hW s.b; omega) 2
    have hsq := Nat.pow_le_pow_left (show 2*W+1+2 ≤ 2*(W+2) by omega) 2
    have hbr : 1 ≤ 1000^(ss.length+1) := Nat.one_le_pow _ _ (by decide)
    have hstep : t₁ ≤ 700*(W+2)^2 := by
      change t₁ ≤ _ + 10*( (v s.a).size + (v s.b).size + (v s.dst).size + y.size+4) at ht₁
      nlinarith only [ht₁,hab,hW s.a,hW s.b,hW s.dst,hy,Nat.zero_le (W^2),Nat.zero_le W]
    have hsub := Nat.mul_le_mul_left (1000^(ss.length+1)) hsq
    have hr := Nat.mul_le_mul_right ((W+2)^2) hbr
    change t₁+t₂ ≤ 1000^(ss.length+1+1)*(W+2)^2
    rw [pow_succ]
    nlinarith only [hstep,ht₂,hsub,hr,Nat.zero_le (1000^(ss.length+1)*(W+2)^2)]

def peek {n} (i : Fin n) : BitRegisterBank.Code n := .base (.atom (.peek (port i) 0 1))
theorem peek_eval {n} (i : Fin n) (v : Vars n) (r : Regs) :
    ∃ rf, Eval (peek i) 1 ⟨r,frame v⟩ ⟨rf,frame v⟩ ∧ rf 1 = decide (v i ≠ 0) := by
  refine ⟨readRegs r 0 1 (frame v (port i)).head?,.base (.atom _ _),?_⟩
  simp only [readRegs,Function.update_self,frame,store_port]
  cases hw : (v i).bits with
  | nil =>
    have h := (Nat.size_eq_zero (n:=v i)).mp (by rw [← Nat.size_eq_bits_len,hw]; rfl)
    simp [h]
  | cons b bs =>
    have h : v i ≠ 0 := fun e => by simp [e] at hw
    simp [h]
end DetDLP.BitRegisterCode
end

noncomputable section

namespace DetDLP.BitRegisterCall
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode

def wiring {n N : ℕ} (e : Fin n ↪ Fin N) : S n → S N :=
  Fin.addCases (@low N) (fun i => port (e i))

@[simp] private theorem wire_low {n N} (e : Fin n ↪ Fin N) (i : Fin 8) :
    wiring e (low i) = low i := Fin.addCases_left ..
@[simp] private theorem wire_port {n N} (e : Fin n ↪ Fin N) (i : Fin n) :
    wiring e (port i) = port (e i) := Fin.addCases_right ..

private theorem injective {n N} (e : Fin n ↪ Fin N) : Function.Injective (wiring e) := by
  intro x y
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) y
  · simp only [wire_low]; exact fun h => congrArg low (Fin.castAdd_injective _ _ h)
  · simp only [wire_low,wire_port]; exact fun h => (low_ne_port _ _ h).elim
  · simp only [wire_low,wire_port]; exact fun h => (low_ne_port _ _ h.symm).elim
  · simp only [wire_port]; exact fun h => congrArg port (e.injective (Fin.natAdd_injective _ _ h))

def subroutine {n N l : ℕ} (P : Program 8 (8+n) l) (e : Fin n ↪ Fin N) : Code N :=
  .call (ProgramLinking.liftProgram P id (wiring e))

private theorem emb {n N} (e : Fin n ↪ Fin N) (r r' : Regs) (v z : Vars N) (a : Vars n)
    (hport : ∀ i, z (e i) = a i) (hrest : ∀ i, (¬ ∃ j, e j = i) → z i = v i) :
    embedState id (wiring e) ⟨r,frame v⟩ ⟨r',frame a⟩ = ⟨r',frame z⟩ := by
  apply embedState_eq_of_ports id (wiring e) _ _ _ Function.injective_id (injective e)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro x; refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;>
      simp only [wire_low,wire_port,frame,store_low,store_port,hport]
  · intro x; refine Fin.addCases (fun i hi => ?_) (fun i hi => ?_) x
    · exact (hi ⟨low i,wire_low e i⟩).elim
    · change frame z (port i) = frame v (port i)
      have h : ¬ ∃ j,e j=i := by rintro ⟨j,rfl⟩; exact hi ⟨port j,wire_port e j⟩
      simp [frame,hrest i h]

theorem call_trace {n N l : ℕ} (P : Program 8 (8+n) l) (e : Fin n ↪ Fin N)
    (v z : Vars N) (a b : Vars n) (r r' : Regs) (k : ℕ)
    (ev : Trace P k ⟨some P.entry,r,frame a⟩ ⟨none,r',frame b⟩)
    (hin : ∀ i,v (e i)=a i) (hout : ∀ i,z (e i)=b i)
    (hrest : ∀ i, (¬ ∃ j,e j=i) → z i=v i) :
    Eval (subroutine P e) k ⟨r,frame v⟩ ⟨r',frame z⟩ := by
  have hh := eval_call_lifted P id (wiring e) ⟨r,frame v⟩ Function.injective_id (injective e)
    (a:=⟨r,frame a⟩) (b:=⟨r',frame b⟩) ev
  rw [emb e r r v v a hin (by simp),emb e r r' v z b hout hrest] at hh
  exact hh
def left {n u : ℕ} : Fin n ↪ Fin (n+u) := ⟨Fin.castAdd u,Fin.castAdd_injective _ _⟩
def right {n u : ℕ} : Fin u ↪ Fin (n+u) := ⟨Fin.natAdd n,Fin.natAdd_injective _ _⟩

theorem call_left {n u l : ℕ} (P : Program 8 (8+n) l) (a b : Vars n) (c : Vars u)
    (r r' : Regs) (k : ℕ) (ev : Trace P k ⟨some P.entry,r,frame a⟩ ⟨none,r',frame b⟩) :
    Eval (subroutine P (@left n u)) k ⟨r,frame (Fin.addCases a c)⟩ ⟨r',frame (Fin.addCases b c)⟩ := by
  apply call_trace P left _ _ a b r r' k ev
  · exact fun _ => Fin.addCases_left ..
  · exact fun _ => Fin.addCases_left ..
  · intro i; refine Fin.addCases (fun j h => (h ⟨j,rfl⟩).elim) (fun j _ => ?_) i
    simp only [Fin.addCases_right]

theorem call_right {n u l : ℕ} (P : Program 8 (8+u) l) (a b : Vars u) (c : Vars n)
    (r r' : Regs) (k : ℕ) (ev : Trace P k ⟨some P.entry,r,frame a⟩ ⟨none,r',frame b⟩) :
    Eval (subroutine P (@right n u)) k ⟨r,frame (Fin.addCases c a)⟩ ⟨r',frame (Fin.addCases c b)⟩ := by
  apply call_trace P right _ _ a b r r' k ev
  · exact fun _ => Fin.addCases_right ..
  · exact fun _ => Fin.addCases_right ..
  · intro i; refine Fin.addCases (fun j _ => ?_) (fun j h => (h ⟨j,rfl⟩).elim) i
    simp only [Fin.addCases_left]
end DetDLP.BitRegisterCall
end

noncomputable section
namespace DetDLP.LeafScanControl
open Finset OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BoundedProgramLoop StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode
abbrev I := BitRegisterCode.Instr 11
def innerOps : List I :=
  [⟨.mul,4,6,4⟩,⟨.add,3,8,3⟩,⟨.add,3,8,9⟩,⟨.quot,9,1,10⟩,⟨.add,7,7,6⟩]
def outerOps : List I :=
  [⟨.add,5,4,5⟩,⟨.add,2,8,2⟩,⟨.add,2,8,9⟩,⟨.quot,9,0,10⟩,⟨.add,7,7,3⟩,⟨.add,7,8,4⟩]
theorem div_test (n k : ℕ) : (decide (n/(k+1)≠0))=decide (k<n) := by
  apply decide_eq_decide.mpr; rw [←Nat.pos_iff_ne_zero,Nat.div_pos_iff]; omega
def finish (ops : List I) := compiled ((compile ops).seq ((peek (10:Fin 11)).seq (.base .skip))) (port (0:Fin 11)) (port (4:Fin 11))
def core (K J k j prod acc factor tmp flag : ℕ) : Vars 11 :=
  ![K,J,k,j,prod,acc,factor,0,1,tmp,flag]
def inner := finish innerOps
def outer := finish outerOps
def time (ops : List I) (W : ℕ) := 1000^(ops.length+1)*(W+2)^2+2
theorem step_run (ops : List I) (v z : Vars 11) (W : ℕ) (r : Regs) (bd : ∀ i,(v i).size ≤ W)
    (valid : Valid ops v) (eq : run ops v=z) :
    ∃ n rf,n ≤ time ops W ∧ rf 1=decide (z 10≠0) ∧
      SafeTrace (step (finish ops)) (cap (W+time ops W)) n ⟨some (finish ops).entry,r,frame v⟩ ⟨none,rf,frame z⟩ := by
  obtain ⟨n,rf,hn,body⟩ := run_eval ops v r W bd valid
  rw [eq] at body
  obtain ⟨r',probe,flag⟩ := peek_eval (10:Fin 11) z rf
  have tr := compiled_halt_trace (Eval.seq body (Eval.seq probe (Eval.base (StructuredProgram.Eval.skip _)))) (port (0:Fin 11)) (port (4:Fin 11))
  refine ⟨_,r',by change n+(1+0)+1 ≤ 1000^(ops.length+1)*(W+2)^2+2; omega,flag,SafeTrace.of_trace tr ?_⟩
  intro k c hk pref i
  have start : (frame v i).length ≤ W := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [frame,store]
    · simpa [frame,store,Nat.size_eq_bits_len] using bd j
  apply (BitTracePolynomial.trace_grows pref i).trans (Nat.add_le_add start _)
  change k ≤ 1000^(ops.length+1)*(W+2)^2+2; omega
theorem product_step (K J k j p z f tmp flag W : ℕ) (r : Regs)
    (bd : ∀ i,(core K J k j p z f tmp flag i).size ≤ W) :
    ∃ n rf,n ≤ time innerOps W ∧ rf 1=decide (j+1<J) ∧ SafeTrace (step inner) (cap (W+time innerOps W)) n
      ⟨some inner.entry,r,frame (core K J k j p z f tmp flag)⟩
      ⟨none,rf,frame (core K J k (j+1) (p*f) z 0 (j+2) (J/(j+2)))⟩ := by
  let s := core K J k j p z f tmp flag
  let s' := core K J k (j+1) (p*f) z 0 (j+2) (J/(j+2))
  have valid : Valid innerOps s := by simp [Valid,innerOps,Op.Valid,Instr.step,s,core,Op.eval] <;> omega
  have eq : run innerOps s=s' := by funext l; fin_cases l <;> rfl
  obtain ⟨n,rf,hn,hflag,tr⟩ := step_run innerOps s s' W r bd valid eq
  exact ⟨n,rf,hn,hflag.trans (div_test _ _),tr⟩
theorem sum_step (K J k j p z tmp flag W : ℕ) (r : Regs)
    (bd : ∀ i,(core K J k j p z 0 tmp flag i).size ≤ W) :
    ∃ n rf,n ≤ time outerOps W ∧ rf 1=decide (k+1<K) ∧ SafeTrace (step outer) (cap (W+time outerOps W)) n
      ⟨some outer.entry,r,frame (core K J k j p z 0 tmp flag)⟩
      ⟨none,rf,frame (core K J (k+1) 0 1 (z+p) 0 (k+2) (K/(k+2)))⟩ := by
  let s := core K J k j p z 0 tmp flag
  let s' := core K J (k+1) 0 1 (z+p) 0 (k+2) (K/(k+2))
  have valid : Valid outerOps s := by simp [Valid,outerOps,Op.Valid,Instr.step,s,core,Op.eval] <;> omega
  have eq : run outerOps s=s' := by funext l; fin_cases l <;> rfl
  obtain ⟨n,rf,hn,hflag,tr⟩ := step_run outerOps s s' W r bd valid eq
  exact ⟨n,rf,hn,hflag.trans (div_test _ _),tr⟩
end DetDLP.LeafScanControl
end

noncomputable section
namespace DetDLP.LeafScanFrame
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BoundedProgramLoop StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode LeafScanControl
abbrev Bank (n : ℕ) := Fin n→List Bool
def wide {s e : ℕ} (a : Bank s) (c : Bank e) : Bank (s+e) := Fin.addCases a c
def enlarged {l n : ℕ} (p : Program 8 n l) (e : ℕ) := liftProgram p id (Fin.castAdd e)
theorem keep {l n e W t : ℕ} (p : Program 8 n l) (a b : Bank n) (c : Bank e) (r rf : Regs)
    (bd : ∀ j,(c j).length ≤ W)
    (tr : SafeTrace (step p) (cap W) t ⟨some p.entry,r,a⟩ ⟨none,rf,b⟩) :
    ∃ r',SafeTrace (step (enlarged p e)) (cap W) t ⟨some (enlarged p e).entry,r,wide a c⟩ ⟨none,r',wide b c⟩ ∧ r'=rf := by
  let big : Cfg 8 (n+e) l := ⟨some (enlarged p e).entry,r,wide a c⟩
  let emb := embedCfg id (Fin.castAdd e) id none big
  have lifted := tr.map emb (g:=step (enlarged p e)) (Q:=cap W) (by
    intro u v eq; exact relocate_step p _ id (Fin.castAdd e) id none big Function.injective_id
      (Fin.castAdd_injective ..) (fun _ => rfl) eq)
    (by intro b hb j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · dsimp only [emb]; rw [embedCfg_stack _ _ _ _ _ _ (Fin.castAdd_injective ..)]; exact hb i
        · dsimp only [emb]
          rw [embedCfg_stack_frame _ _ _ _ _ _ _ (by rintro ⟨k,h⟩; have z := congrArg Fin.val h; change k.val=n+i.val at z; have := k.isLt; omega)]
          change ((Fin.addCases (motive:=fun _=>List Bool) a c) (Fin.natAdd n i)).length ≤ _
          simpa using bd i)
  have eq₀ : emb ⟨some p.entry,r,a⟩=big := by
    apply embedCfg_eq_of_ports _ _ _ _ _ _ _ Function.injective_id (Fin.castAdd_injective ..)
    · rfl
    · intro j; rfl
    · intro j _; rfl
    · intro j; simp [big,wide]
    · intro j _; rfl
  have eq₁ : emb ⟨none,rf,b⟩=⟨none,rf,wide b c⟩ := by
    apply embedCfg_eq_of_ports _ _ _ _ _ _ _ Function.injective_id (Fin.castAdd_injective ..)
    · rfl
    · intro j; rfl
    · intro j h; exact False.elim (h ⟨j,rfl⟩)
    · intro j; simp [wide]
    · intro j; refine Fin.addCases (fun j h => False.elim (h ⟨j,rfl⟩)) (fun i _ => ?_) j
      change Fin.addCases (motive:=fun _=>List Bool) b c (Fin.natAdd n i)=Fin.addCases a c (Fin.natAdd n i)
      simp
  rw [eq₀,eq₁] at lifted; exact ⟨rf,lifted,rfl⟩
def test (i : Fin 11) := compiled (peek i) (port (0:Fin 11)) (port i)
theorem probe (i : Fin 11) (v : Vars 11) (r : Regs) (W : ℕ) (bd : ∀ j,(v j).size ≤ W) :
    ∃ rf,rf 1=decide (v i≠0) ∧ SafeTrace (step (test i)) (cap (W+2)) 2
      ⟨some (test i).entry,r,frame v⟩ ⟨none,rf,frame v⟩ := by
  obtain ⟨rf,tr,flag⟩ := peek_eval i v r
  have full := compiled_halt_trace tr (port (0:Fin 11)) (port i)
  refine ⟨rf,flag,SafeTrace.of_trace full ?_⟩
  intro j b hj pref k
  have base : (frame v k).length ≤ W := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp [frame,store]
    · simpa [frame,store,Nat.size_eq_bits_len] using bd i
  exact (BitTracePolynomial.trace_grows pref k).trans (Nat.add_le_add base hj)

theorem forNat {l s : ℕ} (p : Program 8 s l) (mem : ℕ→Bank s) (n T W : ℕ) (r : Regs)
    (flag : r 1=decide (0<n)) (space : ∀ j,j ≤ n → ∀ i,(mem j i).length ≤ W)
    (body : ∀ j,j<n → ∀ r0 : Regs,r0 1=true → ∃ k rf,k ≤ T ∧ rf 1=decide (j+1<n) ∧
      SafeTrace (step p) (cap W) k ⟨some p.entry,r0,mem j⟩ ⟨none,rf,mem (j+1)⟩) :
    ∃ k rf,k ≤ 2+n*(T+1) ∧ SafeTrace (step (loop p 1)) (cap W) k
      ⟨some (loop p 1).entry,r,mem 0⟩ ⟨none,rf,mem n⟩ := by
  let f := Nat.succ
  have iter (j : ℕ) : f^[j] 0=j := by induction j with | zero => rfl | succ j ih => rw [Function.iterate_succ_apply',ih]
  obtain ⟨k,rf,cost,tr⟩ := BoundedProgramLink.repeatBounded p (1:Fin 8) f (fun j => decide (j<n))
    mem W (fun _ => T) n 0 r flag (by simp [iter]) (fun j hj => by simpa only [iter] using space j hj)
    (fun j hj => by simp only [iter,decide_eq_true_eq]; exact ⟨hj,body j hj⟩)
  rw [iter] at tr
  exact ⟨k,rf,by simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cost,tr⟩
end DetDLP.LeafScanFrame
end

noncomputable section

namespace DetDLP.BitWordFrames
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode SqrtLogSpace
abbrev I := BitRegisterCode.Instr 10
abbrev V := Vars 10

/-- The high one preserves every zero at the end of a serialized payload. -/
def word : List Bool → ℕ
  | [] => 1
  | b::xs => b.toNat+2*word xs
theorem word_pos (xs : List Bool) : 0 < word xs := by
  induction xs with
  | nil => decide
  | cons b xs ih => simp only [word]; omega

theorem bits (xs : List Bool) : (word xs).bits=xs++[true] := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    cases b
    · simp [word,Nat.bit0_bits _ (word_pos xs).ne',ih]
    · simp only [word,Bool.toNat_true,Nat.add_comm 1,Nat.bit1_bits,ih,List.cons_append]

def value : List Bool → ℕ
  | [] => 0
  | b::xs => b.toNat+2*value xs

theorem word_value (xs : List Bool) : word xs=value xs+2^xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [word,value,List.length_cons,pow_succ',ih]; ring

theorem value_bits (n : ℕ) : value n.bits=n := by
  have h (xs : List Bool) : value xs=BinaryArithmetic.toNat xs := by
    induction xs with
    | nil => rfl
    | cons b xs ih => rw [value,BinaryArithmetic.toNat_cons,ih]; cases b <;> rfl
  rw [h,BitEuclidLoop.nat_bits]

theorem value_count (n : ℕ) : value (countWord n)=n := by
  unfold countWord; split
  · subst n; rfl
  · exact value_bits _

theorem value_lt (xs : List Bool) : value xs < 2^xs.length := by
  induction xs with
  | nil => decide
  | cons b xs ih => cases b <;> simp only [value,List.length_cons,pow_succ',Bool.toNat_false,Bool.toNat_true] <;> omega

/-- stream, low accumulator, next digit place, frame marker, four scratch cells,
and constants one and two. -/
def state (s u z : ℕ) : V := ![s,u,z,s%2,0,0,0,0,1,2]
def before : List I := [⟨.quot,9,0,0⟩,⟨.rem,9,0,3⟩]
def stepCode : List I :=
  [⟨.quot,9,0,0⟩,⟨.rem,9,0,4⟩,⟨.mul,4,2,4⟩,⟨.add,1,4,1⟩,
   ⟨.mul,9,2,2⟩,⟨.quot,9,0,0⟩,⟨.rem,9,0,3⟩,⟨.add,7,7,4⟩]
def body : Code 10 := (compile stepCode).seq (peek (3:Fin 10))
def finish : List I := [⟨.quot,9,0,0⟩,⟨.rem,9,0,3⟩]
def read : Code 10 := (compile before).seq ((peek (3:Fin 10)).seq ((Cmd.while 1 body).seq (compile finish)))

private theorem setup (s : ℕ) : Valid before (state (1+2*s) 0 1) ∧ run before (state (1+2*s) 0 1)=state s 0 1 := by
  have e : (1+2*s)/2=s := by omega
  constructor
  · simp [before,Valid,Op.Valid,BitRegisterCode.Instr.step,state]
  · funext i; fin_cases i <;> first | rfl | simp [before,run,BitRegisterCode.Instr.step,state,Op.eval,e]

private theorem step_ok (b : Bool) (s u z : ℕ) :
    let x := 1+2*(b.toNat+2*s)
    Valid stepCode (state x u z) ∧ run stepCode (state x u z)=state s (u+b.toNat*z) (2*z) := by
  intro x
  have X : x/2=b.toNat+2*s := by dsimp [x]; omega
  have B : b.toNat < 2 := by cases b <;> decide
  have Y : (b.toNat+2*s)/2=s := by omega
  have A : (b.toNat+2*s)%2=b.toNat := by omega
  constructor
  · simp [stepCode,Valid,Op.Valid,BitRegisterCode.Instr.step,state]
  · funext i; fin_cases i <;> first | rfl | simp [stepCode,run,BitRegisterCode.Instr.step,state,Op.eval,X,Y,A]

private theorem end_ok (s u z : ℕ) : Valid finish (state (2*s) u z) ∧ run finish (state (2*s) u z)=state s u z := by
  constructor
  · simp [finish,Valid,Op.Valid,BitRegisterCode.Instr.step,state]
  · funext i; fin_cases i <;> first | rfl | simp [finish,run,BitRegisterCode.Instr.step,state,Op.eval]

def oneCost (c : List I) (N : ℕ) := 1000^(c.length+1)*(N.size+2)^2

private theorem eval_list (c : List I) (s u z N : ℕ) (a : V) (r : Regs)
    (h2 : 2 ≤ N) (hs : s ≤ N) (hu : u ≤ N) (hz : z ≤ N) (H : Valid c (state s u z) ∧ run c (state s u z)=a) :
    ∃ t rf,t ≤ oneCost c N ∧ Eval (compile c) t ⟨r,frame (state s u z)⟩ ⟨rf,frame a⟩ := by
  have hm := (Nat.mod_le s 2).trans hs
  have hb (i : Fin 10) : state s u z i ≤ N := by fin_cases i <;> simp [state] <;> omega
  obtain ⟨t,rf,ht,he⟩ := run_eval _ _ r N.size (fun i => Nat.size_le_size (hb i)) H.1
  exact ⟨t,rf,ht,H.2 ▸ he⟩

private theorem frame_cons (b : Bool) (xs tail : List Bool) :
    word (Encoding.frame (b::xs)++tail)=1+2*(b.toNat+2*word (Encoding.frame xs++tail)) := rfl

theorem scan_eval (xs tail : List Bool) (u z N : ℕ) (hu : u < z)
    (h2 : 2 ≤ N) (hN : word (Encoding.frame xs++tail) ≤ N) (hz : z*2^xs.length ≤ N) (r : Regs)
    (hg : r 1=decide ((word (Encoding.frame xs++tail))%2≠0)) :
    ∃ k rf,k ≤ xs.length*(oneCost stepCode N+2)+1 ∧ Eval (.while 1 body) k
      ⟨r,frame (state (word (Encoding.frame xs++tail)) u z)⟩
      ⟨rf,frame (state (2*word tail) (u+z*value xs) (z*2^xs.length))⟩ := by
  induction xs generalizing u z r with
  | nil =>
    have e : word (Encoding.frame []++tail)=2*word tail := by simp [Encoding.frame,word]
    have h : r 1=false := by rw [hg,e]; simp
    refine ⟨1,r,by simp,?_⟩
    simpa only [e,value,List.length_nil,pow_zero,mul_one,mul_zero,add_zero] using
      (Eval.while_false (a:=⟨r,frame (state (2*word tail) u z)⟩) (body:=body) h)
  | cons b xs ih =>
    let s := word (Encoding.frame xs++tail)
    have E := frame_cons b xs tail
    have hz' : (2*z)*2^xs.length ≤ N := by simpa only [List.length_cons,pow_succ',mul_left_comm,mul_assoc] using hz
    have hzN : z ≤ N := (Nat.le_mul_of_pos_right z (pow_pos (by decide) _)).trans hz
    have B : b.toNat ≤ 1 := by cases b <;> decide
    have hpre : u+b.toNat*z < 2*z := by have := Nat.mul_le_mul_right z B; omega
    have hS : s ≤ N := by rw [E] at hN; change _ ≤ N at hN; dsimp only [s]; omega
    have hy : r 1=true := by rw [hg,E]; simp
    obtain ⟨t,rt,ht,et⟩ := eval_list stepCode _ _ _ N _ r h2 (E ▸ hN) (hu.le.trans hzN) hzN (step_ok b s u z)
    obtain ⟨rq,eq,hq⟩ := peek_eval (3:Fin 10) (state s (u+b.toNat*z) (2*z)) rt
    obtain ⟨k,rf,hk,ek⟩ := ih (u+b.toNat*z) (2*z) hpre hS hz' rq hq
    refine ⟨(t+1)+k+1,rf,?_,?_⟩
    · rw [List.length_cons,Nat.succ_mul]; omega
    · rw [E,List.length_cons,value,pow_succ',show u+z*(b.toNat+2*value xs)=u+b.toNat*z+2*z*value xs by ring,
        show z*(2*2^xs.length)=2*z*2^xs.length by ring]
      exact .while_true hy (.seq et eq) ek

theorem read_eval (xs tail : List Bool) (N : ℕ) (hN : word (true::(Encoding.frame xs++tail)) ≤ N)
    (hz : 2^xs.length ≤ N) (r : Regs) :
    ∃ k rf,k ≤ oneCost before N+xs.length*(oneCost stepCode N+2)+oneCost finish N+4 ∧
      Eval read k ⟨r,frame (state (word (true::(Encoding.frame xs++tail))) 0 1)⟩
        ⟨rf,frame (state (word tail) (value xs) (2^xs.length))⟩ := by
  let s := word (Encoding.frame xs++tail)
  have hs := word_pos (Encoding.frame xs++tail)
  change 1+2*s ≤ N at hN
  have h2 : 2 ≤ N := by change 0<s at hs; omega
  obtain ⟨a,ra,ha,ea⟩ := eval_list before _ _ _ N _ r h2 hN (by omega) (by omega) (setup s)
  obtain ⟨rq,eq,hq⟩ := peek_eval (3:Fin 10) (state s 0 1) ra
  obtain ⟨b,rb,hb,eb⟩ := scan_eval xs tail 0 1 N (by decide) h2 (by change s ≤ N; omega) (by simpa using hz) rq hq
  simp only [one_mul,zero_add] at eb
  have bound (ys : List Bool) : 2*word tail ≤ word (Encoding.frame ys++tail) := by
    induction ys with
    | nil => simp [Encoding.frame,word]
    | cons x ys ih => rw [frame_cons]; omega
  have ht : 2*word tail ≤ s := bound xs
  obtain ⟨c,rf,hc,ec⟩ := eval_list finish _ _ _ N _ rb h2 (by omega) ((value_lt xs).le.trans hz) hz (end_ok (word tail) _ _)
  exact ⟨a+(1+(b+c)),rf,by omega,.seq ea (.seq eq (.seq eb ec))⟩

end DetDLP.BitWordFrames
end

noncomputable section

namespace DetDLP.BitWordBridge
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls StackRoutines
open BitArithmeticUnit

abbrev C (n : ℕ) := Cmd 8 n
abbrev Stk (n : ℕ) := Fin n → List Bool
def transfer {n} (i j : Fin n) : C n := .call (transferProgram i j 0 1)
def mark {n} (i : Fin n) : C n := (.base (.atom (.set 2 true)) : C n).seq (.base (.atom (.push i 2)))
def pop {n} (i : Fin n) : C n := .base (.atom (.pop i 0 1))
def encode {n} (src tmp : Fin n) : C n := (transfer src tmp).seq ((mark src).seq (transfer tmp src))
def decode {n} (src tmp : Fin n) : C n := (transfer src tmp).seq ((pop tmp).seq (transfer tmp src))

theorem mark_eval {n} (i : Fin n) (r : Regs) (s : Stk n) :
    Eval (mark i) 2 ⟨r,s⟩ ⟨Function.update r 2 true,Function.update s i (true::s i)⟩ := by
  apply Eval.seq (n:=1) (m:=1) (.base (.atom _ _))
  simpa only [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,StructuredProgram.State.withPC,StructuredProgram.State.ofCfg,execInstr,Function.update_self] using
    (Eval.base (StructuredProgram.Eval.atom (.push i 2) ⟨Function.update r 2 true,s⟩))

theorem pop_eval {n} (i : Fin n) (r : Regs) (s : Stk n) {xs} (h : s i=true::xs) :
    Eval (pop i) 1 ⟨r,s⟩ ⟨readRegs r 0 1 (some true),Function.update s i xs⟩ := by
  simpa [pop,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,StructuredProgram.State.withPC,StructuredProgram.State.ofCfg,execInstr,h] using
    (Eval.base (StructuredProgram.Eval.atom (.pop i 0 1) ⟨r,s⟩))

theorem encode_eval {n} (src tmp : Fin n) (h : src≠tmp) (r : Regs) (s : Stk n) (hs : s tmp=[]) :
    ∃ rf,Eval (encode src tmp) (6*(s src).length+8) ⟨r,s⟩
      ⟨rf,Function.update s src (BitWordFrames.word (s src)).bits⟩ := by
  have A := ArrayUpdatePrograms.transfer_eval src tmp 0 1 h (by decide : (0:Fin 8)≠1) r s
  let t := transferStacks src tmp s
  let r' := readRegs r 0 1 none
  have B := mark_eval src r' t
  let u := Function.update t src (true::t src)
  have D := ArrayUpdatePrograms.transfer_eval tmp src 0 1 h.symm (by decide : (0:Fin 8)≠1) (Function.update r' 2 true) u
  have ht : u tmp=(s src).reverse := by simp [u,t,transferStacks,h.symm,hs]
  have hu : transferStacks tmp src u=Function.update s src (BitWordFrames.word (s src)).bits := by
    funext i
    by_cases he : i=src
    · subst i; simp [BitWordFrames.bits,transferStacks,ht,u,t,Function.update_apply,h,hs,h.symm]
    by_cases hi : i=tmp
    · subst i; simp [transferStacks,he,hs]
    · simp [transferStacks,u,t,Function.update_apply,hi,he]
  obtain ⟨rf,he⟩ : ∃ rf, Eval (encode src tmp) ((3*(s src).length+3)+(2+(3*(u tmp).length+3)))
      ⟨r,s⟩ ⟨rf,transferStacks tmp src u⟩ := ⟨_,.seq A (.seq B D)⟩
  rw [hu,ht,List.length_reverse] at he
  exact ⟨rf,by convert he using 1 <;> omega⟩

theorem decode_eval {n} (src tmp : Fin n) (h : src≠tmp) (xs : List Bool) (r : Regs) (s : Stk n)
    (hv : s src=(BitWordFrames.word xs).bits) (hs : s tmp=[]) :
    ∃ rf,Eval (decode src tmp) (6*xs.length+10) ⟨r,s⟩ ⟨rf,Function.update s src xs⟩ := by
  have A := ArrayUpdatePrograms.transfer_eval src tmp 0 1 h (by decide : (0:Fin 8)≠1) r s
  let t := transferStacks src tmp s
  let r' := readRegs r 0 1 none
  have ht : t tmp=true::xs.reverse := by simp [t,transferStacks,hv,BitWordFrames.bits,hs]
  have B := pop_eval tmp r' t ht
  let u := Function.update t tmp xs.reverse
  have D := ArrayUpdatePrograms.transfer_eval tmp src 0 1 h.symm (by decide : (0:Fin 8)≠1) (readRegs r' 0 1 (some true)) u
  have hu : transferStacks tmp src u=Function.update s src xs := by
    funext i
    by_cases he : i=src
    · subst i; simp [transferStacks,u,t,Function.update_apply,h,hs,h.symm]
    by_cases hi : i=tmp
    · subst i; simp [transferStacks,he,hs]
    · simp [transferStacks,u,t,Function.update_apply,hi,he]
  obtain ⟨rf,he⟩ : ∃ rf, Eval (decode src tmp) ((3*(s src).length+3)+(1+(3*(u tmp).length+3)))
      ⟨r,s⟩ ⟨rf,transferStacks tmp src u⟩ := ⟨_,.seq A (.seq B D)⟩
  have eu : u tmp=xs.reverse := Function.update_self ..
  rw [hu,eu,hv,BitWordFrames.bits,List.length_append,List.length_reverse] at he
  exact ⟨rf,by convert he using 1 <;> simp <;> omega⟩

end DetDLP.BitWordBridge
end

noncomputable section
namespace DetDLP.EntryScratchReset
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls StackRoutines
open ArithmeticExpressionSupport BitArithmeticUnit
def sweep {n : ℕ} : List (Fin n)→Cmd 8 n
  | [] => .base .skip
  | i::is => (clearCmd i).seq (sweep is)
def swept {n : ℕ} (is : List (Fin n)) (s : Fin n→List Bool) (j : Fin n) := if j∈is then [] else s j
theorem sweep_eval {n : ℕ} (is : List (Fin n)) (s : Fin n→List Bool) (r : Regs) (U : ℕ) (bound : ∀ i,(s i).length≤U) :
    ∃ t rf,t ≤ is.length*(2*U+3) ∧ Eval (sweep is) t ⟨r,s⟩ ⟨rf,swept is s⟩ := by
  induction is generalizing s r with
  | nil =>
    have eq : swept [] s=s := by funext j; simp [swept]
    rw [eq]; exact ⟨0,r,by simp,by simpa [swept,sweep] using Eval.base (StructuredProgram.Eval.skip (⟨r,s⟩ : State 8 n))⟩
  | cons i is ih =>
    let s' := Function.update s i []
    have bd (j) : (s' j).length≤U := by by_cases h : j=i <;> simp [s',h,bound]
    have c := clear_eval i (⟨r,s⟩ : State 8 n)
    obtain ⟨t,rf,ht,tail⟩ := ih s' (readRegs r 0 1 none) bd
    have eq : swept is s'=swept (i::is) s := by
      funext j; by_cases h : j=i <;> by_cases k : j∈is <;> simp [swept,s',h,k]
    rw [eq] at tail
    refine ⟨_,rf,?_,.seq c tail⟩
    change 2*(s i).length+3+t ≤ (is.length+1)*(2*U+3)
    rw [Nat.add_mul,one_mul]; have := bound i; omega
def reset {e : ℕ} := sweep ((List.finRange e).map (Fin.castAdd 3))
theorem reset_eval {e : ℕ} (q : Fin e→List Bool) (c : Fin 3→List Bool) (r : Regs) (U : ℕ)
    (bq : ∀ i,(q i).length≤U) (bc : ∀ i,(c i).length≤U) :
    ∃ n rf,n ≤ e*(2*U+3) ∧ Eval (reset (e:=e)) n ⟨r,Fin.addCases q c⟩ ⟨rf,Fin.addCases (fun _ => []) c⟩ := by
  let is := (List.finRange e).map (Fin.castAdd 3)
  have bd (i : Fin (e+3)) : ((Fin.addCases (motive:=fun _=>List Bool) q c) i).length≤U := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using bq j
    · simpa only [Fin.addCases_right] using bc j
  obtain ⟨n,rf,time,tr⟩ := sweep_eval is (Fin.addCases q c) r U bd
  have eq : swept is (Fin.addCases q c)=Fin.addCases (fun _ : Fin e => []) c := by
    funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have mem : j.castAdd 3∈is := List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩
      simp [swept,mem]
    · have nmem : Fin.natAdd e j∉is := by
        intro h; obtain ⟨v,_,eq⟩ := List.mem_map.mp h; have := congrArg Fin.val eq
        change v.val=e+j.val at this; have := v.isLt; omega
      simp [swept,nmem]
  rw [eq] at tr; exact ⟨n,rf,by simpa [is] using time,tr⟩
end DetDLP.EntryScratchReset
end

noncomputable section
namespace DetDLP.SubroutineInputBank
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls StackRoutines
open BitArithmeticUnit LeafScanFrame
inductive Source (n : ℕ) where
  | literal (w : List Bool)
  | slot (i : Fin n)
def Source.read {n} (a : Bank n) : Source n→List Bool
  | .literal w => w
  | .slot i => a i
def Source.size {n} : Source n→ℕ
  | .literal w => w.length
  | .slot _ => 0
variable {n e : ℕ}
abbrev pport (j : Fin n) := j.castAdd (1+e)
abbrev middle := Fin.natAdd n ((0:Fin 1).castAdd e)
abbrev ext (k : Fin e) := Fin.natAdd n (Fin.natAdd 1 k)
def frame (priv : Bank n) (outside : Bank e) := wide priv (wide (fun _ : Fin 1 => []) outside)
@[simp] theorem atP (p : Bank n) (a : Bank e) (j : Fin n) : frame p a (pport j)=p j := by simp [frame,pport,wide]
@[simp] theorem atMid (p : Bank n) (a : Bank e) : frame p a (middle (n:=n) (e:=e))=[] := by simp [frame,middle,wide]
@[simp] theorem atExt (p : Bank n) (a : Bank e) (j : Fin e) : frame p a (ext j)=a j := by simp [frame,ext,wide]
theorem pm (j : Fin n) : pport (e:=e) j ≠ middle := by
  intro h; have eq := congrArg Fin.val h; change j.val=n+0 at eq; have := j.isLt; omega
theorem pe (j : Fin n) (k : Fin e) : pport (e:=e) j≠ext k := by
  intro h; have eq := congrArg Fin.val h; change j.val=n+(1+k.val) at eq; have := j.isLt; omega
theorem mx (k : Fin e) : middle (n:=n)≠ext k := by
  intro h; have eq := congrArg Fin.val h; change n+0=n+(1+k.val) at eq; omega
theorem updateP (p : Bank n) (a : Bank e) (j : Fin n) (w : List Bool) :
    Function.update (frame p a) (pport j) w=frame (Function.update p j w) a := by
  funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · change Function.update (frame p a) (pport j) w (pport i)=_
    by_cases h : i=j
    · subst i; simp
    · have ne : pport (e:=e) i ≠ pport j := fun q => h (Fin.castAdd_injective _ _ q)
      simp [Function.update_of_ne ne,h]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · fin_cases i; change Function.update (frame p a) (pport j) w middle=_
      simp [Function.update_of_ne (pm j).symm]
    · change Function.update (frame p a) (pport j) w (ext i)=_
      simp [Function.update_of_ne (pe j i).symm]
def writeOne (j : Fin n) : Source e→Cmd 8 (n+(1+e))
  | .literal w => ArithmeticExpressionSupport.pushWord (pport j) w
  | .slot i => .call (copyProgram (ext i) (pport j) middle 0 1)
theorem write_eval (j : Fin n) (x : Source e) (r : Regs) (p : Bank n) (a : Bank e) :
    ∃ t rf,t ≤ 7*(x.read a).length+5 ∧ Eval (writeOne j x) t ⟨r,frame p a⟩
      ⟨rf,frame (Function.update p j (x.read a++p j)) a⟩ := by
  rw [←updateP]
  cases x with
  | literal w =>
    obtain ⟨rf,t⟩ := ArithmeticExpressionSupport.pushWord_eval (pport j) w (⟨r,frame p a⟩ : State 8 (n+(1+e)))
    exact ⟨2*w.length,rf,by dsimp [Source.read]; omega,by simpa [writeOne,Source.read] using t⟩
  | slot i =>
    have t := ArrayUpdatePrograms.copy_eval (ext i) (pport j) middle (0:Fin 8) 1
      (pe j i).symm (mx i).symm (pm j).symm (by decide) r (frame p a) (atMid p a)
    exact ⟨7*(a i).length+5,_,le_rfl,by simpa [writeOne,copyStacks,Source.read] using t⟩
def fill (src : Fin n→Source e) : List (Fin n)→Cmd 8 (n+(1+e))
  | [] => .base .skip
  | i::is => (writeOne i (src i)).seq (fill src is)
def filled (p : Bank n) (a : Bank e) (src : Fin n→Source e) (is : List (Fin n)) (j : Fin n) :=
  if j∈is then (src j).read a else p j
theorem fill_eval (src : Fin n→Source e) (is : List (Fin n)) (nd : is.Nodup) (r : Regs) (p : Bank n) (a : Bank e)
    (empty : ∀ j∈is,p j=[]) (W : ℕ) (cap : ∀ j,((src j).read a).length ≤ W) :
    ∃ t rf,t ≤ is.length*(7*W+5) ∧ Eval (fill src is) t ⟨r,frame p a⟩ ⟨rf,frame (filled p a src is) a⟩ := by
  induction is generalizing r p with
  | nil =>
    have eq : filled p a src []=p := by funext j; simp [filled]
    rw [eq]; exact ⟨0,r,by simp,.base (.skip _)⟩
  | cons i is ih =>
    have out := write_eval i (src i) r p a
    rw [empty i (by simp),List.append_nil] at out
    obtain ⟨t,r',time,step⟩ := out
    let p' := Function.update p i ((src i).read a)
    have free (j) (hj : j∈is) : p' j=[] := by
      have ne : j≠i := fun h => nd.notMem (h ▸ hj)
      simp [p',ne,empty j (List.mem_cons_of_mem _ hj)]
    obtain ⟨u,rf,hu,tr⟩ := ih nd.tail r' p' free
    have eq : filled p' a src is=filled p a src (i::is) := by
      funext j; by_cases h : j=i <;> by_cases jmem : j∈is <;> simp_all [filled,p']
    rw [eq] at tr
    refine ⟨_,rf,?_,.seq step tr⟩
    change t+u ≤ (is.length+1)*(7*W+5); rw [Nat.add_mul,one_mul]; have := cap i; omega
end DetDLP.SubroutineInputBank
end

noncomputable section
namespace DetDLP.SubroutineHarness
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BoundedProgramLoop StructuredCalls StackRoutines
open BitArithmeticUnit LeafScanFrame SubroutineInputBank
variable {n e l : ℕ}
abbrev empty (n : ℕ) : Bank n := fun _ => []
theorem frameBound {p : Bank n} {a : Bank e} {W : ℕ} (bp : ∀ j,(p j).length ≤ W) (ba : ∀ i,(a i).length ≤ W) :
    ∀ i,(frame p a i).length ≤ W := by
  intro i; refine Fin.addCases (fun j => ?_) (fun i => ?_) i
  · simpa only [atP] using bp j
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · fin_cases j; change (frame p a middle).length ≤ W; simp
    · change (frame p a (ext j)).length ≤ W; simpa using ba j
theorem updateExt (p : Bank n) (a : Bank e) (dst : Fin e) (w : List Bool) :
    Function.update (frame p a) (ext dst) w=frame p (Function.update a dst w) := by
  funext i; refine Fin.addCases (fun j => ?_) (fun i => ?_) i
  · change Function.update (frame p a) (ext dst) w (pport j)=_
    simp [Function.update_of_ne (pe j dst)]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · fin_cases j; change Function.update (frame p a) (ext dst) w middle=_
      simp [Function.update_of_ne (mx dst)]
    · change Function.update (frame p a) (ext dst) w (ext j)=_
      by_cases h : j=dst
      · subst j; simp
      · have ne : ext (n:=n) j≠ext dst := fun z => h (Fin.natAdd_injective _ _ (Fin.natAdd_injective _ _ z))
        simp [Function.update_of_ne ne,h]

def reset (n e : ℕ) := EntryScratchReset.sweep ((List.finRange n).map (Fin.castAdd (1+e)))
theorem reset_eval (p : Bank n) (a : Bank e) (r : Regs) (W : ℕ) (bd : ∀ i,(frame p a i).length ≤ W) :
    ∃ t rf,t ≤ n*(2*W+3) ∧ Eval (reset n e) t ⟨r,frame p a⟩ ⟨rf,frame (empty n) a⟩ := by
  let is := (List.finRange n).map (Fin.castAdd (1+e))
  obtain ⟨t,rf,ht,tr⟩ := EntryScratchReset.sweep_eval is (frame p a) r W bd
  have eq : EntryScratchReset.swept is (frame p a)=frame (empty n) a := by
    funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have mem : j.castAdd (1+e)∈is := List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩
      simp [EntryScratchReset.swept,mem,frame,wide,empty]
    · have ne : Fin.natAdd n j∉is := by
        intro h; obtain ⟨u,_,eq⟩ := List.mem_map.mp h; have z := congrArg Fin.val eq
        change u.val=n+j.val at z; have := u.isLt; omega
      simp [EntryScratchReset.swept,ne,frame,wide]
  rw [eq] at tr; exact ⟨t,rf,by simpa [is] using ht,tr⟩

def setup (src : Fin n→Source e) := compiled (fill src (List.finRange n)) middle middle
def collect (out : Fin n) (dst : Fin e) := compiled ((Cmd.call (copyProgram (pport out) (ext dst) middle 0 1)).seq
  (reset n e)) (pport out) (ext dst)
def machine (src : Fin n→Source e) (P : Program 8 n l) (out : Fin n) (dst : Fin e) :=
  link (setup src) (link (enlarged P (1+e)) (collect out dst))
theorem checked {s z : ℕ} (P : Program 8 s z) (a b : Bank s) (r rf : Regs) {W T t : ℕ}
    (bd : ∀ i,(a i).length ≤ W) (ht : t ≤ T)
    (tr : BitProgram.Trace P t ⟨some P.entry,r,a⟩ ⟨none,rf,b⟩) :
    SafeTrace (step P) (cap (W+T)) t ⟨some P.entry,r,a⟩ ⟨none,rf,b⟩ := by
  apply SafeTrace.of_trace tr
  intro j c hj pref i
  exact (BitTracePolynomial.trace_grows pref i).trans (Nat.add_le_add (bd i) (hj.trans ht))

theorem prepare (src : Fin n→Source e) (a : Bank e) (r : Regs) (W : ℕ)
    (ha : ∀ i,(a i).length ≤ W) (hs : ∀ j,((src j).read a).length ≤ W) :
    let T := n*(7*W+5)+1
    ∃ t rf,t ≤ T ∧ SafeTrace (step (setup src)) (cap (W+T)) t
      ⟨some (setup src).entry,r,frame (empty n) a⟩ ⟨none,rf,frame (fun j => (src j).read a) a⟩ := by
  intro T
  obtain ⟨t,rf,ht,tr⟩ := fill_eval src (List.finRange n) (List.nodup_finRange n) r (empty n) a (by simp [empty]) W hs
  have eq : filled (empty n) a src (List.finRange n)=(fun j => (src j).read a) := by funext j; simp [filled]
  rw [eq] at tr
  have time : t+1 ≤ T := by simpa only [T,Nat.add_le_add_iff_right,List.length_finRange] using Nat.add_le_add_right ht 1
  exact ⟨_,rf,time,checked _ _ _ _ _ (frameBound (by simp [empty]) ha) time (compiled_halt_trace tr middle middle)⟩

theorem harvest (out : Fin n) (dst : Fin e) (p : Bank n) (a : Bank e) (r : Regs) (W : ℕ)
    (bp : ∀ j,(p j).length ≤ W) (ba : ∀ j,(a j).length ≤ W) (clean : a dst=[]) :
    let T := 7*W+6+n*(2*W+3)
    ∃ t rf,t ≤ T ∧ SafeTrace (step (collect out dst)) (cap (W+T)) t
      ⟨some (collect out dst).entry,r,frame p a⟩ ⟨none,rf,frame (empty n) (Function.update a dst (p out))⟩ := by
  intro T
  let s := frame p a
  let a' := Function.update a dst (p out)
  have copy := ArrayUpdatePrograms.copy_eval (pport out) (ext dst) middle (0:Fin 8) 1
    (pe out dst) (pm out) (mx dst) (by decide) r s (atMid p a)
  have eq : copyStacks (pport out) (ext dst) s=frame p a' := by simp [s,copyStacks,clean,a',updateExt]
  rw [eq] at copy
  have bd (i) : (a' i).length ≤ W := by by_cases h : i=dst <;> simp [a',h,ba,bp]
  obtain ⟨t,rf,ht,tr⟩ := reset_eval p a' _ W (frameBound bp bd)
  have time : 7*(s (pport out)).length+5+t+1 ≤ T := by simp only [s,atP,T]; have := bp out; omega
  exact ⟨_,rf,time,checked _ _ _ _ _ (frameBound bp ba) time (compiled_halt_trace (Eval.seq copy tr) _ _)⟩
abbrev prepareTime (n W : ℕ) := n*(7*W+5)+1
abbrev collectTime (n W : ℕ) := 7*W+6+n*(2*W+3)
abbrev extra (n W U : ℕ) := prepareTime n W + collectTime n (W+U)
theorem run (src : Fin n→Source e) (P : Program 8 n l) (out : Fin n) (dst : Fin e)
    (a : Bank e) (W T U : ℕ) (word : List Bool) (r : Regs)
    (ba : ∀ i,(a i).length ≤ W) (bs : ∀ i,((src i).read a).length ≤ W) (zero : a dst=[])
    (call : ∀ r₀ : Regs,∃ t rf q,t ≤ T ∧
      SafeTrace (step P) (cap U) t ⟨some P.entry,r₀,fun i => (src i).read a⟩ ⟨none,rf,q⟩ ∧ q out=word) :
    let Q := machine src P out dst
    ∃ t rf,t ≤ T+extra n W U ∧ SafeTrace (step Q) (cap (W+U+extra n W U)) t
      ⟨some Q.entry,r,frame (empty n) a⟩ ⟨none,rf,frame (empty n) (Function.update a dst word)⟩ := by
  intro Q
  obtain ⟨t,r₁,ht,t₁⟩ := prepare src a r W ba bs
  obtain ⟨u,r₂,q,hu,t₂,val⟩ := call r₁
  have bq (i) : (q i).length ≤ U := t₂.within u _ le_rfl t₂.forget i
  let outside := wide (empty 1) a
  have bc (i : Fin (1+e)) : (outside i).length ≤ W+U := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [outside,wide,empty]
    · simpa only [outside,wide,Fin.addCases_right] using (ba j).trans (Nat.le_add_right W U)
  obtain ⟨r',body,eq⟩ := keep P _ _ outside r₁ r₂ (W:=W+U) bc (EntryEvaluatorCall.mono t₂ (Nat.le_add_left ..))
  subst r'
  obtain ⟨v,rf,hv,t₃⟩ := harvest out dst q a r₂ (W+U) (fun i => (bq i).trans (Nat.le_add_left ..))
    (fun i => (ba i).trans (Nat.le_add_right ..)) zero
  rw [val] at t₃
  let cap' := W+U+extra n W U
  have c₁ : W+prepareTime n W ≤ cap' := by dsimp only [cap',extra]; omega
  have c₂ : W+U ≤ cap' := Nat.le_add_right ..
  have c₃ : W+U+collectTime n (W+U) ≤ cap' := by dsimp only [cap',extra]; omega
  have tr := BoundedProgramLink.join _ _ (EntryEvaluatorCall.mono t₁ c₁)
    (BoundedProgramLink.join _ _ (EntryEvaluatorCall.mono body c₂) (EntryEvaluatorCall.mono t₃ c₃))
  refine ⟨t+(u+v),rf,?_,tr⟩
  change t ≤ prepareTime n W at ht
  change v ≤ collectTime n (W+U) at hv
  dsimp only [extra]; omega
end DetDLP.SubroutineHarness
end

noncomputable section
namespace DetDLP.HarnessLift
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BoundedProgramLoop
open BitArithmeticUnit LeafScanFrame SubroutineInputBank
open SubroutineHarness (empty)
variable {n e S l : ℕ}
def clearBank (S : ℕ) (a : Bank e) := wide a (empty S)
def ports (h : n < S) : Fin (n+(1+e))→Fin (e+S) :=
  Fin.addCases (fun j => Fin.natAdd e (j.castLE (Nat.le_of_lt h)))
    (Fin.addCases (fun _ => Fin.natAdd e ⟨n,h⟩) (Fin.castAdd S))
theorem injective (h : n < S) : Function.Injective (ports (e:=e) h) := by
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · intro eq; have z := congrArg Fin.val eq; simp only [ports,Fin.addCases_left,Fin.addCases_right] at z
    change e+i.val=e+j.val at z
    have : i=j := Fin.ext (by omega); subst j; rfl
  · refine Fin.addCases (fun _ => ?_) (fun j => ?_) j
    · intro eq; have z := congrArg Fin.val eq; simp only [ports,Fin.addCases_left,Fin.addCases_right] at z; change e+i.val=e+n at z; have := i.isLt; omega
    · intro eq; have z := congrArg Fin.val eq; simp only [ports,Fin.addCases_left,Fin.addCases_right] at z; change e+i.val=j.val at z; have := j.isLt; omega
  · refine Fin.addCases (fun _ => ?_) (fun i => ?_) i
    · intro eq; have z := congrArg Fin.val eq; simp only [ports,Fin.addCases_left,Fin.addCases_right] at z; change e+n=e+j.val at z; have := j.isLt; omega
    · intro eq; have z := congrArg Fin.val eq; simp only [ports,Fin.addCases_left,Fin.addCases_right] at z; change i.val=e+j.val at z; have := i.isLt; omega
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro _; have : i=j := Subsingleton.elim ..; subst j; rfl
    · intro eq; have z := congrArg Fin.val eq; simp only [ports,Fin.addCases_left,Fin.addCases_right] at z; change e+n=j.val at z; have := j.isLt; omega
    · intro eq; have z := congrArg Fin.val eq; simp only [ports,Fin.addCases_left,Fin.addCases_right] at z; change i.val=e+n at z; have := i.isLt; omega
    · intro eq; have z := congrArg Fin.val eq; simp only [ports,Fin.addCases_left,Fin.addCases_right] at z; change i.val=j.val at z; have : i=j := Fin.ext z; subst j; rfl
theorem lookup (h : n < S) (a : Bank e) : ∀ j,clearBank S a (ports h j)=frame (empty n) a j := by
  intro j; refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · simp [clearBank,wide,ports,frame,empty]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [ports,Fin.addCases_left,Fin.addCases_right,clearBank,wide,frame,empty]
    · simp [clearBank,wide,ports,frame,empty]
def machine (h : n < S) (src : Fin n→Source e) (P : Program 8 n l) (out : Fin n) (dst : Fin e) :=
  liftProgram (SubroutineHarness.machine src P out dst) id (ports h)
theorem run (h : n < S) (src : Fin n→Source e) (P : Program 8 n l) (out : Fin n) (dst : Fin e)
    (a : Bank e) (W T U : ℕ) (word : List Bool) (r : Regs)
    (ba : ∀ i,(a i).length ≤ W) (bs : ∀ i,((src i).read a).length ≤ W) (zero : a dst=[])
    (call : ∀ r₀ : Regs,∃ t rf q,t ≤ T ∧
      SafeTrace (step P) (cap U) t ⟨some P.entry,r₀,fun i => (src i).read a⟩ ⟨none,rf,q⟩ ∧ q out=word) :
    let Q := machine h src P out dst
    ∃ t rf,t ≤ T+SubroutineHarness.extra n W U ∧ SafeTrace (step Q) (cap (W+U+SubroutineHarness.extra n W U)) t
      ⟨some Q.entry,r,clearBank S a⟩ ⟨none,rf,clearBank S (Function.update a dst word)⟩ := by
  intro Q
  obtain ⟨t,rf,ht,tr⟩ := SubroutineHarness.run src P out dst a W T U word r ba bs zero call
  have unchanged (i : Fin (e+S)) (free : ¬∃ j,ports h j=i) (b : Bank e) :
      clearBank S b i=[] := by
    revert free; refine Fin.addCases (fun j free => ?_) (fun j free => ?_) i
    · exact (free ⟨ext j,by simp [ports,ext]⟩).elim
    · simp [clearBank,wide,empty]
  obtain ⟨r',done⟩ := CallOnPorts.run _ id (ports h) Function.injective_id (injective h)
    (clearBank S a) (clearBank S (Function.update a dst word)) _ _ r rf (lookup h a) (lookup h _)
    (fun i free => by rw [unchanged i free _,unchanged i free _]) (fun i free => by rw [unchanged i free a]; simp) tr
  exact ⟨_,r',ht,done⟩
end DetDLP.HarnessLift
end

noncomputable section

namespace DetDLP.BitFrameWrite
open OAI.Algorithms.SubexponentialSAT BitProgram

/-- Append a frame to the front of the output stack. The payload is read in reverse
order, so each marker and bit can be prepended to the existing suffix. -/
def writer : Program 3 2 8 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.set 2 false 1,.push 1 2 2,.set 2 true 3,.pop 0 0 1 4,.branch 1 5 7,.push 1 0 6,.push 1 2 3,.halt]

private def cfg (pc : Option (Fin 8)) (r : Fin 3 → Bool) (xs tail : List Bool) : Cfg 3 2 8 :=
  ⟨pc,r,![xs,tail]⟩
private theorem upd0 (xs ys z : List Bool) : Function.update ![xs,ys] (0:Fin 2) z = ![z,ys] := by
  funext i; fin_cases i <;> simp [Function.update_apply]
private theorem upd1 (xs ys z : List Bool) : Function.update ![xs,ys] (1:Fin 2) z = ![xs,z] := by
  funext i; fin_cases i <;> simp [Function.update_apply]

private def pushBits (xs tail : List Bool) := xs.foldl (fun acc b => true::b::acc) tail

private theorem loop (xs tail : List Bool) (r : Fin 3 → Bool) (hr : r 2=true) :
    ∃ rf, Trace writer (4*xs.length+3) (cfg (some 3) r xs tail) (cfg none rf [] (pushBits xs tail)) := by
  induction xs generalizing tail r with
  | nil =>
    let r' := readRegs r 0 1 none
    refine ⟨r',.cons (b:=cfg (some 4) r' [] tail) ?_ (.cons (b:=cfg (some 7) r' [] tail) ?_ (.cons ?_ (.refl _)))⟩
    · change step writer _ = some (cfg (some 4) r' [] tail)
      simp [step,writer,cfg,execInstr,upd0,r']
    · change step writer _ = some (cfg (some 7) r' [] tail)
      simp [step,writer,cfg,execInstr,r',readRegs]
    · rfl
  | cons b xs ih =>
    let r' := readRegs r 0 1 (some b)
    have h2 : r' 2 = true := by simpa [r',readRegs] using hr
    have h0 : r' 0=b := by simp [r',readRegs]
    have h1 : r' 1=true := by simp [r',readRegs]
    obtain ⟨rf,he⟩ := ih (true::b::tail) r' h2
    refine ⟨rf,?_⟩
    rw [List.length_cons,show 4*(xs.length+1)+3=(4*xs.length+3)+1+1+1+1 by omega]
    refine .cons (b:=cfg (some 4) r' xs tail) ?_ (.cons (b:=cfg (some 5) r' xs tail) ?_ (.cons (b:=cfg (some 6) r' xs (b::tail)) ?_ (.cons ?_ he)))
    · change step writer _ = some (cfg (some 4) r' xs tail)
      simp [step,writer,cfg,execInstr,upd0,r']
    · change step writer _ = some (cfg (some 5) r' xs tail)
      simp [step,writer,cfg,execInstr,h1]
    · change step writer _ = some (cfg (some 6) r' xs (b::tail))
      simp [step,writer,cfg,execInstr,h0,upd1]
    · simp [step,writer,cfg,execInstr,h2,upd1]

private theorem push_rev (xs tail : List Bool) :
    pushBits xs.reverse (false::tail) = Encoding.frame xs ++ tail := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [pushBits,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [show List.foldl (fun acc b => true::b::acc) (false::tail) xs.reverse = Encoding.frame xs ++ tail from ih]
    rfl

theorem writer_correct (xs tail : List Bool) (r : Fin 3 → Bool) :
    ∃ rf, Trace writer (4*xs.length+6) (cfg (some writer.entry) r xs.reverse tail)
      (cfg none rf [] (Encoding.frame xs ++ tail)) := by
  let r₁ := Function.update r 2 false
  let r₂ := Function.update r₁ 2 true
  obtain ⟨rf,hr⟩ := loop xs.reverse (false::tail) r₂ (by simp [r₂])
  rw [List.length_reverse,push_rev] at hr
  refine ⟨rf,.cons (b:=cfg (some 1) r₁ xs.reverse tail) ?_ (.cons (b:=cfg (some 2) r₁ xs.reverse (false::tail)) ?_ (.cons ?_ hr))⟩
  · change step writer _ = some (cfg (some 1) r₁ xs.reverse tail); rfl
  · change step writer _ = some (cfg (some 2) r₁ xs.reverse (false::tail))
    simp [step,writer,cfg,execInstr,r₁,upd1]
  · rfl
end DetDLP.BitFrameWrite
end

noncomputable section

namespace DetDLP.RecoveryFrame
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls StackRoutines
open BitArithmeticUnit
open BitWordBridge (C Stk)
abbrev reg (j : Fin 3) : Fin 8 := j.castAdd 5
def pair {n} (i j : Fin n) : Fin 2 → Fin n := ![i,j]
theorem pair_inj {n} {i j : Fin n} (h : i≠j) : Function.Injective (pair i j) := by
  intro a b e; fin_cases a <;> fin_cases b <;> simp_all [pair]
def call {n} (i j : Fin n) : C n := .call (ProgramLinking.liftProgram BitFrameWrite.writer reg (pair i j))
theorem call_eval {n} (a b : Fin n) (h : a≠b) (xs : List Bool) (r : Regs) (s : Stk n) (hs : s a=xs.reverse) :
    ∃ rf,Eval (call a b) (4*xs.length+6) ⟨r,s⟩ ⟨rf,Function.update (Function.update s a []) b (Encoding.frame xs++s b)⟩ := by
  let fr : StructuredProgram.State 8 n := ⟨r,s⟩
  let loc : Fin 3 → Bool := r ∘ reg
  obtain ⟨rf,et⟩ := BitFrameWrite.writer_correct xs (s b) loc
  let src : StructuredProgram.State 3 2 := ⟨loc,![xs.reverse,s b]⟩
  let dst : StructuredProgram.State 3 2 := ⟨rf,![[],Encoding.frame xs++s b]⟩
  have e := eval_call_lifted BitFrameWrite.writer reg (pair a b) fr (Fin.castAdd_injective ..) (pair_inj h)
    (a:=src) (b:=dst) et
  have pre : embedState reg (pair a b) fr src=fr := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective ..) (pair_inj h)
    · intro i; rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> first | exact hs | rfl
    · intro i hi; rfl
  let fs := Function.update (Function.update s a []) b (Encoding.frame xs++s b)
  let R := Function.extend reg rf r
  have post : embedState reg (pair a b) fr dst=⟨R,fs⟩ := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective ..) (pair_inj h)
    · intro i; exact Function.Injective.extend_apply (Fin.castAdd_injective 3 5) .. 
    · intro i hi; exact Function.extend_apply' _ _ _ hi
    · intro i; fin_cases i <;> simp [fs,pair,dst,h]
    · intro i hi
      have ha : i≠a := fun e => hi ⟨0,e.symm⟩
      have hb : i≠b := fun e => hi ⟨1,e.symm⟩
      simp [fs,Function.update_of_ne ha,Function.update_of_ne hb,fr]
  rw [pre,post] at e; exact ⟨R,e⟩

def field {n} (src tmp dst : Fin n) : C n :=
  (BitWordBridge.transfer src tmp).seq ((call tmp dst).seq (BitWordBridge.mark dst))

theorem field_eval {n} (src tmp dst : Fin n) (st : src≠tmp) (sd : src≠dst) (td : tmp≠dst)
    (r : Regs) (s : Stk n) (ht : s tmp=[]) :
    ∃ rf,Eval (field src tmp dst) (7*(s src).length+11) ⟨r,s⟩
      ⟨rf,Function.update (Function.update s src []) dst (true::(Encoding.frame (s src)++s dst))⟩ := by
  have A := ArrayUpdatePrograms.transfer_eval src tmp 0 1 st (by decide : (0:Fin 8)≠1) r s
  let v := transferStacks src tmp s
  have ht' : v tmp=(s src).reverse := by simp [v,transferStacks,ht,st.symm]
  have hd : v dst=s dst := by simp [v,transferStacks,sd.symm,td.symm]
  obtain ⟨rb,B⟩ := call_eval tmp dst td (s src) (readRegs r 0 1 none) v ht'
  rw [hd] at B
  let w := Function.update (Function.update v tmp []) dst (Encoding.frame (s src)++s dst)
  have C₁ := BitWordBridge.mark_eval dst rb w
  have hw : w dst=Encoding.frame (s src)++s dst := Function.update_self ..
  rw [hw] at C₁
  have restore : Function.update v tmp []=Function.update s src [] := by
    funext i
    by_cases e : i=src
    · subst i; simp [v,transferStacks,st]
    by_cases g : i=tmp
    · subst i; simp [ht,Function.update_of_ne st.symm]
    · simp [v,transferStacks,Function.update_apply,g,e]
  have last : Function.update w dst (true::(Encoding.frame (s src)++s dst)) =
      Function.update (Function.update s src []) dst (true::(Encoding.frame (s src)++s dst)) := by
    dsimp only [w]; rw [Function.update_idem,restore]
  rw [last] at C₁
  refine ⟨Function.update rb 2 true,?_⟩
  rw [show 7*(s src).length+11=(3*(s src).length+3)+((4*(s src).length+6)+2) by omega]
  exact .seq A (.seq B C₁)
end DetDLP.RecoveryFrame
end

noncomputable section
namespace DetDLP.RecoveryEmit
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls SqrtLogSpace
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open BitWordBridge (C Stk)
open BitWordFrames (word)

abbrev stab {n} (s : Stk n) (i : Fin n) (xs : List Bool) := Function.update s i xs
def zeroBit {n} (i : Fin n) : C n := (.base (.atom (.set 2 false)) : C n).seq (.base (.atom (.push i 2)))
theorem zero_eval {n} (i : Fin n) (r : Regs) (s : Stk n) :
    Eval (zeroBit i) 2 ⟨r,s⟩ ⟨Function.update r 2 false,stab s i (false::s i)⟩ := by
  apply Eval.seq (n:=1) (m:=1) (.base (.atom _ _))
  simpa only [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,StructuredProgram.State.withPC,StructuredProgram.State.ofCfg,execInstr,Function.update_self] using
    (Eval.base (StructuredProgram.Eval.atom (.push i 2) ⟨Function.update r 2 false,s⟩))

def normalize {n} (i : Fin n) : C n := (.base (.atom (.peek i 0 1)) : C n).seq (.ite 1 (.base .skip) (zeroBit i))
theorem normalize_eval {n} (i : Fin n) (k : ℕ) (r : Regs) (s : Stk n) (h : s i=k.bits) :
    ∃ t rf,t ≤ 4 ∧ Eval (normalize i) t ⟨r,s⟩ ⟨rf,stab s i (countWord k)⟩ := by
  let r' := readRegs r 0 1 (s i).head?
  have e : Eval (.base (.atom (.peek i 0 1))) 1 ⟨r,s⟩ ⟨r',s⟩ := .base (.atom _ _)
  by_cases hk : k=0
  · subst k; have hs : s i=[] := h
    have hz : r' 1=false := by simp [r',readRegs,hs]
    have Z := zero_eval i r' s
    rw [hs] at Z
    exact ⟨4,_,le_rfl,.seq e (.ite_false hz Z)⟩
  · have he : (s i)≠[] := by
      intro emp; rw [h] at emp
      apply hk; apply Nat.size_eq_zero.mp; rw [← Nat.size_eq_bits_len,emp]; rfl
    have hp : r' 1=true := by
      cases hsi : s i with
      | nil => exact (he hsi).elim
      | cons b bs => simp [r',readRegs,hsi]
    rw [countWord,if_neg hk,← h,show stab s i (s i)=s from Function.update_eq_self i s]
    exact ⟨2,r',by decide,.seq e (.ite_true hp (.base (.skip _)))⟩

def payload (signed : Bool) (k : ℕ) := if signed then false::countWord k else countWord k
def canon {n} (signed : Bool) (i : Fin n) : C n :=
  (normalize i).seq (if signed then zeroBit i else .base .skip)

def writeCount {n} (signed : Bool) (i j : Fin n) : Code n :=
  (canon signed (port i)).seq (RecoveryFrame.field (port i) (low 0) (port j))
def writeWord {n} (i j : Fin n) : Code n :=
  (BitWordBridge.decode (port i) (low 0)).seq (RecoveryFrame.field (port i) (low 0) (port j))


def finish {n} (v : Vars n) (i j : Fin n) (xs tail : List Bool) :=
  Function.update (Function.update v i 0) j (word (true::(Encoding.frame xs++tail)))


end DetDLP.RecoveryEmit
end

noncomputable section
namespace DetDLP.WordFlow
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BoundedProgramLoop StructuredCalls SqrtLogSpace
open BitArithmeticUnit LeafScanFrame
variable {n l l' : ℕ}
def Runs (P : Program 8 n l) (a b : Bank n) (T U : ℕ) : Prop :=
  ∀ r : Regs,∃ t rf,t ≤ T ∧ SafeTrace (step P) (cap U) t ⟨some P.entry,r,a⟩ ⟨none,rf,b⟩
theorem chain {P : Program 8 n l} {Q : Program 8 n l'} {a b c : Bank n} {T U V W : ℕ}
    (first : Runs P a b T U) (second : Runs Q b c V W) : Runs (link P Q) a c (T+V) (max U W) := by
  intro r; obtain ⟨t,r',ht,tr⟩ := first r; obtain ⟨u,rf,hu,tq⟩ := second r'
  exact ⟨t+u,rf,Nat.add_le_add ht hu,BoundedProgramLink.join _ _ (EntryEvaluatorCall.mono tr (le_max_left ..)) (EntryEvaluatorCall.mono tq (le_max_right ..))⟩
theorem weaken {P : Program 8 n l} {a b : Bank n} {T U V W : ℕ} (x : Runs P a b T U) (t : T ≤ V) (u : U ≤ W) :
    Runs P a b V W := by
  intro r; obtain ⟨k,rf,h,tr⟩ := x r; exact ⟨k,rf,h.trans t,EntryEvaluatorCall.mono tr u⟩
inductive Change where | mark | unmark | count
def command : Change→Cmd 8 2
  | .mark => BitWordBridge.encode 0 1
  | .unmark => BitWordBridge.decode 0 1
  | .count => RecoveryEmit.normalize 0
def machine (c : Change) := compiled (command c) 0 0
def payload : Change→ List Bool→ℕ→List Bool
  | .unmark,w,_ => w++[true]
  | .mark,w,_ => w
  | .count,_,k => k.bits
def answer : Change→List Bool→ℕ→List Bool
  | .unmark,w,_ => w
  | .mark,w,_ => w++[true]
  | .count,_,k => countWord k
def pair (s : List Bool) : Bank 2 := ![s,[]]
theorem replace (a b : List Bool) : Function.update (pair a) (0:Fin 2) b=pair b := by funext i; fin_cases i <;> simp [pair]
theorem execute (c : Change) (w : List Bool) (k : ℕ) :
    let x := payload c w k
    let T := 6*x.length+15
    Runs (machine c) (pair x) (pair (answer c w k)) T (x.length+T) := by
  intro x T r
  have finish {t : ℕ} {rf : Regs} (ht : t+1 ≤ T)
      (ev : Eval (command c) t ⟨r,pair x⟩ ⟨rf,Function.update (pair x) (0:Fin 2) (answer c w k)⟩) :
      ∃ u rf,u ≤ T ∧ SafeTrace (step (machine c)) (cap (x.length+T)) u ⟨some (machine c).entry,r,pair x⟩ ⟨none,rf,pair (answer c w k)⟩ := by
    rw [replace] at ev
    exact ⟨_,rf,ht,SubroutineHarness.checked _ _ _ _ _ (fun i => by fin_cases i <;> simp [pair]) ht (compiled_halt_trace ev 0 0)⟩
  cases c with
  | mark =>
    obtain ⟨rf,tr⟩ := BitWordBridge.encode_eval (0:Fin 2) 1 (by decide) r (pair x) rfl
    apply finish (t:=6*x.length+8) (by dsimp only [T]; omega)
    simpa only [command,answer,BitWordFrames.bits,pair,Matrix.cons_val_zero,x,payload] using tr
  | unmark =>
    have h : pair x 0=(BitWordFrames.word w).bits := by simp [pair,x,payload,BitWordFrames.bits]
    obtain ⟨rf,tr⟩ := BitWordBridge.decode_eval (0:Fin 2) 1 (by decide) w r (pair x) h rfl
    exact finish (t:=6*w.length+10) (by simp [T,x,payload]; omega) tr
  | count =>
    obtain ⟨t,rf,ht,tr⟩ := RecoveryEmit.normalize_eval (0:Fin 2) k r (pair x) rfl
    exact finish (t:=t) (by dsimp only [T]; omega) tr
end DetDLP.WordFlow
end

noncomputable section

namespace DetDLP.SerializedFieldCall
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode BitRegisterCall
open BitWordFrames (word value word_value)

def low {n} (i : Fin 10) : Fin (10+n) := i.castAdd n
def high {n} (i : Fin n) : Fin (10+n) := Fin.natAdd 10 i
def merge {n} (l : Vars 10) (v : Vars n) : Vars (10+n) :=
  fun i => Fin.addCases (m:=10) (n:=n) (motive:=fun _ => ℕ) l v i
def clean : Vars 10 := BitWordFrames.state 0 0 1
@[simp] theorem get_low {n} (l : Vars 10) (v : Vars n) (i : Fin 10) : merge l v (low i)=l i := Fin.addCases_left ..
@[simp] theorem get_high {n} (l : Vars 10) (v : Vars n) (i : Fin n) : merge l v (high i)=v i := Fin.addCases_right ..
theorem ne {n} (k : Fin 10) (i : Fin n) : low k ≠ high i := by
  intro h; have e := congrArg Fin.val h; change k.val=10+i.val at e; omega

@[simp] theorem set_low {n} (l : Vars 10) (v : Vars n) (i : Fin 10) (x : ℕ) :
    Function.update (merge l v) (low i) x=merge (Function.update l i x) v := by
  funext j
  refine Fin.addCases (m:=10) (n:=n) (motive:=fun j => Function.update (merge l v) (low i) x j = merge (Function.update l i x) v j) (fun k => ?_) (fun k => ?_) j
  · change Function.update (merge l v) (low i) x (low k) = merge _ _ (low k)
    by_cases e : k=i
    · subst k; simp
    · simp [Function.update_of_ne e,Function.update_of_ne (show low (n:=n) k ≠ low i from fun h => e (Fin.castAdd_injective _ _ h))]
  · change Function.update (merge l v) (low i) x (high k)=merge _ _ (high k)
    rw [Function.update_of_ne (ne i k).symm,get_high,get_high]

@[simp] theorem set_high {n} (l : Vars 10) (v : Vars n) (i : Fin n) (x : ℕ) :
    Function.update (merge l v) (high i) x=merge l (Function.update v i x) := by
  funext j
  refine Fin.addCases (m:=10) (n:=n) (motive:=fun j => Function.update (merge l v) (high i) x j = merge l (Function.update v i x) j) (fun k => ?_) (fun k => ?_) j
  · change Function.update (merge l v) (high i) x (low k) = merge _ _ (low k)
    rw [Function.update_of_ne (ne k i),get_low,get_low]
  · change Function.update (merge l v) (high i) x (high k)=merge _ _ (high k)
    by_cases e : k=i
    · subst k; simp
    · simp [Function.update_of_ne e,Function.update_of_ne (show high k ≠ high i from fun h => e (Fin.natAdd_injective _ _ h))]

abbrev I (n : ℕ) := BitRegisterCode.Instr (10+n)
def cp {n} (a b : Fin (10+n)) : I n := ⟨.add,a,low 7,b⟩
def pre {n} (src : Fin n) : List (I n) := [cp (high src) (low 0),⟨.rem,low 9,low 0,low 3⟩]
def post {n} (src raw framed : Fin n) : List (I n) :=
  [cp (low 0) (high src),cp (low 1) (high raw),⟨.add,low 1,low 2,high framed⟩,
   cp (low 7) (low 0),cp (low 7) (low 1),cp (low 8) (low 2),cp (low 7) (low 3)]
def result {n} (v : Vars n) (src raw framed : Fin n) (xs tail : List Bool) :=
  Function.update (Function.update (Function.update v src (word tail)) raw (value xs)) framed (word xs)
def prog := compiled BitWordFrames.read (port (0:Fin 10)) (port (0:Fin 10))
def cmd {n} (src raw framed : Fin n) : Code (10+n) :=
  (compile (pre src)).seq ((subroutine prog (@left 10 n)).seq (compile (post src raw framed)))

theorem pre_ok {n} (v : Vars n) (src : Fin n) :
    let input := merge clean v
    Valid (pre src) input ∧ run (pre src) input=merge (BitWordFrames.state (v src) 0 1) v := by
  intro input
  constructor
  · simp [pre,cp,Valid,Op.Valid,BitRegisterCode.Instr.step,input,clean,BitWordFrames.state]
  · simp only [pre,cp,run,BitRegisterCode.Instr.step,input,get_high,get_low,set_low,Op.eval]
    congr 1; funext j; fin_cases j <;> simp [clean,BitWordFrames.state,Function.update_apply]

theorem post_ok {n} (v : Vars n) (src raw framed : Fin n) (xs tail : List Bool) :
    let inL := BitWordFrames.state (word tail) (value xs) (2^xs.length)
    let inp := merge inL v
    Valid (post src raw framed) inp ∧ run (post src raw framed) inp=merge clean (result v src raw framed xs tail) := by
  intro l inp
  constructor
  · simp [post,cp,Valid,Op.Valid]
  · simp only [post,cp,run,BitRegisterCode.Instr.step,inp,Op.eval,get_high,get_low,set_high,set_low]
    have L : l 7=0 := rfl
    have O : l 8=1 := rfl
    simp only [L,O,add_zero]
    congr 1
    · funext j; fin_cases j <;> simp [clean,l,BitWordFrames.state,Function.update_apply]
    · simp only [result,word_value xs]; rfl

theorem merge_bound {n} (l : Vars 10) (v : Vars n) (N : ℕ) (hl : ∀ j,l j ≤ N) (hv : ∀ j,v j ≤ N) :
    ∀ j,merge l v j ≤ N := by
  intro j; refine Fin.addCases (m:=10) (n:=n) (motive:=fun j => merge l v j ≤ N) (fun i => ?_) (fun i => ?_) j
  · exact (get_low l v i) ▸ hl i
  · exact (get_high l v i) ▸ hv i

def cost := 1000^8+1000^3+1000^9+10

theorem eval {n} (v : Vars n) (src raw framed : Fin n) (xs tail : List Bool)
    (input : v src = word (true::(Encoding.frame xs++tail))) (N : ℕ)
    (h2 : 2 ≤ N) (hv : ∀ i,v i ≤ N) (hp : 2^xs.length ≤ N) (ht : word tail ≤ N) (r : Regs) :
    ∃ t rf,t ≤ cost*(xs.length+4)*(N.size+2)^2 ∧
      Eval (cmd src raw framed) t ⟨r,frame (merge clean v)⟩ ⟨rf,frame (merge clean (result v src raw framed xs tail))⟩ := by
  obtain ⟨h₁,h₁'⟩ := pre_ok v src
  have hc (j : Fin 10) : clean j ≤ N := by fin_cases j <;> simp [clean,BitWordFrames.state] <;> omega
  obtain ⟨t,rt,ht',et⟩ := run_eval _ _ r N.size (fun i => Nat.size_le_size (merge_bound _ _ _ hc hv i)) h₁
  rw [h₁',input] at et
  obtain ⟨u,ru,hu,eu⟩ := BitWordFrames.read_eval xs tail N (input ▸ hv src) hp rt
  have eu' := call_left (n:=10) (u:=n) prog _ _ v rt ru (u+1) (compiled_halt_trace eu _ _)
  let l := BitWordFrames.state (word tail) (value xs) (2^xs.length)
  have hl (j : Fin 10) : l j ≤ N := by
    have := (BitWordFrames.value_lt xs).le.trans hp
    have := (Nat.mod_le (word tail) 2).trans ht
    fin_cases j <;> simp [l,BitWordFrames.state] <;> omega
  obtain ⟨h₂,h₂'⟩ := post_ok v src raw framed xs tail
  obtain ⟨w,rf,hw,ew⟩ := run_eval _ _ ru N.size (fun i => Nat.size_le_size (merge_bound _ _ _ hl hv i)) h₂
  rw [h₂'] at ew
  refine ⟨_,rf,?_,.seq et (.seq eu' ew)⟩
  let S := (N.size+2)^2
  change t ≤ 1000^3*S at ht'
  change w ≤ 1000^8*S at hw
  change u ≤ 1000^3*S+xs.length*(1000^9*S+2)+1000^3*S+4 at hu
  have hS : 1 ≤ S := Nat.one_le_pow _ _ (by omega)
  change _ ≤ cost*(xs.length+4)*S
  unfold cost
  nlinarith only [ht',hw,hu,hS,Nat.mul_le_mul_left xs.length hS]

end DetDLP.SerializedFieldCall
end

noncomputable section

namespace DetDLP.CosetTapeBounds

open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem frame_length (xs : List Bool) : (Encoding.frame xs).length = 2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x l ih => change (Encoding.frame l).length+1+1 = _; rw [ih]; simp; omega







end DetDLP.CosetTapeBounds
end

noncomputable section

namespace DetDLP.BinaryUpdateFields
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls SqrtLogSpace
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open BitWordFrames (word value)
open SerializedFieldCall (merge clean)

structure Pop (n : ℕ) where
  src : Fin n
  raw : Fin n
  field : Fin n

def sequence {n} : List (Pop n) → Code (10+n)
  | [] => .base .skip
  | p::ps => (SerializedFieldCall.cmd p.src p.raw p.field).seq (sequence ps)

inductive Parses {n : ℕ} (L : ℕ) : List (Pop n) → Vars n → Vars n → Prop
  | nil (v : Vars n) : Parses L [] v v
  | cons {p : Pop n} {ps : List (Pop n)} {v w : Vars n} (x tail : List Bool)
      (he : v p.src=word (true::(Encoding.frame x++tail))) (hx : x.length ≤ L) (ht : tail.length ≤ L)
      (next : Parses L ps (SerializedFieldCall.result v p.src p.raw p.field x tail) w) :
      Parses L (p::ps) v w

theorem word_bound (x : List Bool) : word x < 2^(x.length+1) := by
  rw [BitWordFrames.word_value,pow_succ]; have := BitWordFrames.value_lt x; omega


def pops : List (Pop 11) :=
  [⟨0,1,10⟩,⟨0,2,10⟩,⟨0,9,3⟩,⟨0,9,4⟩,⟨0,5,10⟩,⟨3,9,6⟩,⟨3,9,7⟩]

def fields {n} (m : ℕ) (x a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (c : ℕ) :=
  let X := encodeNatListBin (List.ofFn x)
  let A := encodeNatListBin (List.ofFn a)
  let F := Encoding.encodeList encodeIntBin ((List.finRange n).flatMap fun i =>
    (List.finRange n).map fun j => B i j)
  ![word [false],m,n,word [false],word A,c,word X,word F,0,value F,word (countWord c)]

theorem tail_length (x tail : List Bool) :
    tail.length ≤ (true::(Encoding.frame x++tail)).length := by simp; omega
theorem head_length (x tail : List Bool) :
    x.length ≤ (true::(Encoding.frame x++tail)).length := by
  simp [CosetTapeBounds.frame_length]; omega


end DetDLP.BinaryUpdateFields
end

noncomputable section

namespace DetDLP.BorderedHermite



abbrev Subgroup (n : ℕ) := AddSubgroup (Fin n → ℤ)

private def grid {n : ℕ} (m : ℤ) (j : Fin n) : Fin n → ℤ := Pi.single j m

private def reserves {n : ℕ} (m : ℤ) (k : ℕ) (H : Subgroup n) : Prop :=
  ∀ i : Fin n, k ≤ i.val → grid m i ∈ H

private def held {n : ℕ} (H : Subgroup n) (xs : Array (Column n)) :=
  ∀ c ∈ xs, c.get ∈ H







private def oldZero {n : ℕ} (k : ℕ) (v : Column n) : Prop :=
  ∀ i : Fin n, i.val < k → v.get i = 0



/-- Each processed row has one positive pivot and the required reduced entries. -/
private def shape {n : ℕ} (k : ℕ) (cols : Array (Column n)) : Prop :=
  cols.size = k ∧ ∀ i : Fin n, i.val < k →
    ∃ d : ℤ, 0 < d ∧ ∀ j : Fin cols.size,
      (if i.val < j.val then cols[j].get i = 0
       else if i.val = j.val then cols[j].get i = d
       else 0 ≤ cols[j].get i ∧ cols[j].get i < d)





private def represents {n : ℕ} (m : ℤ) (k : ℕ) (st : Array (Column n) × Array (Column n))
    (H : Subgroup n) := held H st.1 ∧ held H st.2 ∧ reserves m k H




end DetDLP.BorderedHermite
end

noncomputable section

namespace DetDLP.UnsignedHermitePivot
open BorderedHermite
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterCode

def signedColumn {n} (v : Fin n → ℕ) : Column n := Vector.ofFn (fun i => (v i : ℤ))

def tail (m a b t' p' v w : ℕ) : ℕ × ℕ :=
  ((a*v+b*w)%m,(((m-1)*t')*v+p'*w)%m)




def operation {n} (m : ℕ) (j : Fin n) (v w : Fin n → ℕ) (i : Fin n) : ℕ × ℕ :=
  let p := v j; let t := w j; let g := p.gcd t
  if t=0 then (v i,w i) else if i<j then (0,0) else if i=j then (g,0) else
    tail m ((p.gcdA t:ℤ):ZMod m).val ((p.gcdB t:ℤ):ZMod m).val (t/g) (p/g) (v i) (w i)


/-- 0 modulus, 1 its predecessor, 2 and 3 Bézout residues, 4 and 5 divided pivot
entries, 6 and 7 tail entries. The two output coordinates are on ports 8 and 9. -/
def tailCode : List (BitRegisterCode.Instr 11) :=
  [⟨.mul,2,6,8⟩,⟨.mul,3,7,10⟩,⟨.add,8,10,8⟩,⟨.rem,0,8,8⟩,
   ⟨.mul,1,4,9⟩,⟨.mul,9,6,9⟩,⟨.mul,5,7,10⟩,⟨.add,9,10,9⟩,⟨.rem,0,9,9⟩]
end DetDLP.UnsignedHermitePivot
end

noncomputable section

namespace DetDLP.BitColumnScan

open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode

structure Coeff where
  m : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ

def Coeff.radix (q : Coeff) := q.m+1

def Coeff.row (q : Coeff) (u : ℕ × ℕ) : ℕ × ℕ :=
  ((q.a*u.1+q.b*u.2)%q.m,(q.c*u.1+q.d*u.2)%q.m)

def pack (b : ℕ) (rows : List (ℕ × ℕ)) : ℕ × ℕ :=
  (Nat.ofDigits b (rows.map Prod.fst),Nat.ofDigits b (rows.map Prod.snd))

def data (q : Coeff) (x y s t w : ℕ) : Vars 17 :=
  ![q.m,q.radix,q.a,q.b,q.c,q.d,x,y,s,t,w,x+y,0,0,0,0,0]

def stepCode : List (BitRegisterCode.Instr 17) :=
  [⟨.rem,1,6,12⟩,⟨.rem,1,7,13⟩,
   ⟨.mul,2,12,14⟩,⟨.mul,3,13,15⟩,⟨.add,14,15,14⟩,⟨.rem,0,14,14⟩,
   ⟨.mul,10,14,14⟩,⟨.add,8,14,8⟩,
   ⟨.mul,4,12,14⟩,⟨.mul,5,13,15⟩,⟨.add,14,15,14⟩,⟨.rem,0,14,14⟩,
   ⟨.mul,10,14,14⟩,⟨.add,9,14,9⟩,⟨.mul,10,1,10⟩,
   ⟨.quot,1,6,6⟩,⟨.quot,1,7,7⟩,⟨.add,6,7,11⟩,
   ⟨.add,16,16,12⟩,⟨.add,16,16,13⟩,⟨.add,16,16,14⟩,⟨.add,16,16,15⟩]

private def body := (compile stepCode).seq (peek (11:Fin 17))
def command := (peek (11:Fin 17)).seq (.while 1 body)






def program := compiled command (port (6:Fin 17)) (port (8:Fin 17))
end DetDLP.BitColumnScan
end

noncomputable section

namespace DetDLP.ModularBezout
open BoundedExtendedEuclid

/-- Coefficients are kept in the original modulus throughout the Euclidean loop. -/
structure Registers (m : ℕ) where
  r : ℕ
  oldR : ℕ
  u : ZMod m
  v : ZMod m
  oldU : ZMod m
  oldV : ZMod m

def encode {m : ℕ} (s : BoundedExtendedEuclid.State) : Registers m :=
  ⟨s.r,s.oldR,s.u,s.v,s.oldU,s.oldV⟩

def step {m : ℕ} (s : Registers m) : Registers m :=
  if s.r = 0 then s else
    let q := (s.oldR/s.r : ℕ)
    ⟨s.oldR%s.r,s.r,s.oldU-(q:ZMod m)*s.u,s.oldV-(q:ZMod m)*s.v,s.u,s.v⟩

def run {m : ℕ} : ℕ → Registers m → Registers m
  | 0,s => s
  | k+1,s => run k (step s)




/-- An unsigned subtraction primitive with inputs in [0,m) computes the ring subtraction. -/
def subResidue (m x y : ℕ) := (x + m - y) % m


end DetDLP.ModularBezout
end

noncomputable section

namespace DetDLP.BitExtendedEuclid
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode

abbrev V := Vars 13
abbrev R (m : ℕ) := ModularBezout.Registers m

def data (m : ℕ) (s : R m) : V :=
  ![m,m-1,s.r,s.oldR,s.u.val,s.oldU.val,s.v.val,s.oldV.val,0,0,0,0,0]

/-- Ports 8–11 store the quotient, remainder and the two new coefficient residues.
Port 12 remains zero. The instruction list and port indices are fixed. -/
def stepCode : List (BitRegisterCode.Instr 13) :=
  [⟨.quot,2,3,8⟩,⟨.rem,2,3,9⟩,⟨.mul,1,8,8⟩,
   ⟨.mul,8,4,10⟩,⟨.add,5,10,10⟩,⟨.rem,0,10,10⟩,
   ⟨.mul,8,6,11⟩,⟨.add,7,11,11⟩,⟨.rem,0,11,11⟩,
   ⟨.add,12,2,3⟩,⟨.add,12,9,2⟩,⟨.add,12,4,5⟩,⟨.add,12,10,4⟩,
   ⟨.add,12,6,7⟩,⟨.add,12,11,6⟩,
   ⟨.add,12,12,8⟩,⟨.add,12,12,9⟩,⟨.add,12,12,10⟩,⟨.add,12,12,11⟩]



private def body := (compile stepCode).seq (peek (2:Fin 13))
private def command := (peek (2:Fin 13)).seq (.while 1 body)




def program := compiled command (port (2:Fin 13)) (port (3:Fin 13))

end DetDLP.BitExtendedEuclid
end

noncomputable section

namespace DetDLP.BitPackedPivot
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open BitRegisterCall

abbrev V := Vars 30
abbrev I := BitRegisterCode.Instr 30
def banks (e : Vars 13) (a : Vars 17) : V := fun i => Fin.addCases (m:=13) (n:=17) (motive:=fun _ => ℕ) e a i
def blank : Vars 13 := fun _ => 0
def io (m w x y : ℕ) : Vars 17 := ![m,m+1,x,y,w,1,0,0,0,0,0,0,0,0,0,0,0]
def staged (m w x y p t topX topY : ℕ) : Vars 17 :=
  ![m,m+1,x,y,w,1,0,p,t,topX,topY,0,0,0,0,0,0]

private def cp (fromPort toPort : Fin 30) : I := ⟨.add,fromPort,29,toPort⟩
private def erase (i : Fin 30) : I := cp 29 i

/-- Split both columns at the pivot and load the canonical Euclidean basis. -/
def prepare : List I :=
  [cp 13 0,⟨.mul,13,13,1⟩,⟨.quot,14,1,1⟩,
   ⟨.quot,17,15,22⟩,⟨.quot,17,16,23⟩,⟨.rem,14,22,20⟩,⟨.rem,14,23,21⟩,
   ⟨.quot,14,22,22⟩,⟨.quot,14,23,23⟩,cp 20 2,cp 21 3,cp 18 4,cp 18 7]

/-- Save the original row address, then convert the Euclidean outputs into
the two modular tail transformations and initialize the output prefixes. -/
def configure : List I :=
  [cp 17 8,cp 18 9,⟨.quot,3,21,25⟩,⟨.quot,3,20,26⟩,⟨.mul,1,25,27⟩,⟨.mul,17,3,28⟩,
   cp 22 19,cp 23 20,cp 28 21,erase 22,⟨.mul,17,14,23⟩,
   cp 5 15,cp 7 16,cp 27 17,cp 26 18,⟨.add,19,20,24⟩,erase 25,erase 26,erase 27,erase 28]

/-- Copy the two output columns back to the argument ports and release every
scratch register, so that the same subroutine can be called repeatedly. -/
def finish : List I :=
  [cp 21 15,cp 22 16,cp 8 17,cp 9 18,erase 19,erase 20,erase 21,erase 22,erase 23,
   erase 24,erase 25,erase 26,erase 27,erase 28,
   erase 0,erase 1,erase 2,erase 3,erase 4,erase 5,erase 6,erase 7,erase 8,erase 9,erase 10,erase 11,erase 12]

def command : Code 30 :=
  (compile prepare).seq ((subroutine BitExtendedEuclid.program (@left 13 17)).seq
    ((compile configure).seq ((subroutine BitColumnScan.program (@right 13 17)).seq (compile finish))))

def program := compiled command (port (15:Fin 30)) (port (15:Fin 30))


def prepared (m p t : ℕ) : Vars 13 := ![m,m-1,p,t,1,0,0,1,0,0,0,0,0]
def saved (e : Vars 13) (w : ℕ) : Vars 13 := Function.update (Function.update e 8 w) 9 1

def coefficients (m p t g a b : ℕ) : BitColumnScan.Coeff := ⟨m,a,b,(m-1)*(t/g),p/g⟩




abbrev Bounded {n : ℕ} (v : Vars n) (N : ℕ) := ∀ j, v j ≤ N



noncomputable def matrix (m p t : ℕ) : BitColumnScan.Coeff :=
  coefficients m p t (p.gcd t) (((p.gcdA t:ℤ):ZMod m).val) (((p.gcdB t:ℤ):ZMod m).val)


theorem digit_bound (b p X L : ℕ) (hp : p < b) (hX : X < L) : p+b*X < b*L := by
  have hh := Nat.mul_le_mul_left b (show X+1 ≤ L by omega)
  rw [Nat.mul_succ] at hh; omega


def overhead := 1000^(prepare.length+1)+1000^(configure.length+1)+1000^(finish.length+1)+
  1000^(BitColumnScan.stepCode.length+1)+1000^(BitExtendedEuclid.stepCode.length+1)+10


end DetDLP.BitPackedPivot
end

noncomputable section
namespace DetDLP.BitFixedColumn
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode BitRegisterCall
open BitPackedPivot (V I banks io blank Bounded)

private def cp (a dst : Fin 30) : I := ⟨.add,a,29,dst⟩
private def erase (i : Fin 30) : I := cp 29 i

/-- Preserve the pivot column and the row address in the left bank. The right
bank performs the same simultaneous row pass used for the Euclidean pivot. -/
def before : List I :=
  [cp 15 0,cp 17 1,cp 18 2,
   ⟨.quot,17,15,3⟩,⟨.quot,17,16,4⟩,⟨.rem,14,3,5⟩,⟨.rem,14,4,6⟩,
   ⟨.rem,5,6,7⟩,⟨.quot,5,6,8⟩,⟨.rem,17,16,9⟩,
   ⟨.mul,17,7,21⟩,⟨.add,9,21,21⟩,⟨.mul,17,14,23⟩,
   ⟨.quot,14,4,19⟩,⟨.quot,14,3,20⟩,⟨.add,19,20,24⟩,
   ⟨.mul,13,13,3⟩,⟨.quot,14,3,3⟩,⟨.mul,3,8,16⟩,cp 18 15,erase 17,erase 18]

def after : List I :=
  [cp 0 15,cp 21 16,cp 1 17,cp 2 18,erase 19,erase 20,erase 21,erase 22,erase 23,
   erase 24,erase 25,erase 26,erase 27,erase 28,erase 0,erase 1,erase 2,erase 3,erase 4,
   erase 5,erase 6,erase 7,erase 8,erase 9,erase 10,erase 11,erase 12]

def command : Code 30 :=
  (compile before).seq ((subroutine BitColumnScan.program (@right 13 17)).seq (compile after))

def matrix (m p t : ℕ) : BitColumnScan.Coeff := ⟨m,1,(m-1)*(t/p),0,0⟩

def hold (m w x y p t : ℕ) : Vars 13 :=
  ![x,w,1,m-1,y/w,p,t,t%p,t/p,y%w,0,0,0]



def overhead := 1000^(before.length+1)+1000^(BitColumnScan.stepCode.length+1)+1000^(after.length+1)+10

end DetDLP.BitFixedColumn
end

noncomputable section

namespace DetDLP.PackedHermiteRefinement
open BorderedHermite UnsignedHermitePivot

abbrev Pair := ℕ × ℕ
def rowsAt (pre : List Pair) (z : Pair) (tail : List Pair) := pre ++ z::tail
noncomputable def signed {n : ℕ} (u : Fin n → ℕ) : Column n := signedColumn u




/-- Pair two lists of natural coordinates and view them as signed columns. -/
def column (s : List Pair) (f : Pair → ℕ) := signedColumn (fun i : Fin s.length => f (s.get i))



end DetDLP.PackedHermiteRefinement
end

noncomputable section

namespace DetDLP.PackedColumnWords
open BorderedHermite
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open BitPackedPivot (io banks blank)

def low {n : ℕ} (j : Fin n) (i : Fin j.val) : Fin n := ⟨i.val,lt_trans i.isLt j.isLt⟩
def high {n : ℕ} (j : Fin n) (i : Fin (n-j.val-1)) : Fin n := ⟨j.val+1+i.val,by have := i.isLt; omega⟩


def digit {n} (c : Column n) (i : Fin n) := (c.get i).toNat
def word {n} (b : ℕ) (c : Column n) := Nat.ofDigits b (List.ofFn (digit c))
def digitsBounded {n} (m : ℕ) (c : Column n) := ∀ i, 0 ≤ c.get i ∧ c.get i ≤ (m:ℤ)
def zeroBefore {n} (j : Fin n) (c : Column n) := ∀ i < j,c.get i=0
def reducedAfter {n} (m : ℕ) (j : Fin n) (c : Column n) := ∀ i,j < i → c.get i < (m:ℤ)




def tailRows {n} (j : Fin n) (v w : Column n) :=
  List.ofFn fun i => (digit v (high j i),digit w (high j i))








end DetDLP.PackedColumnWords
end

noncomputable section

namespace DetDLP.BitMatrixPass
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode BitRegisterCall
open BitPackedPivot (io blank banks Bounded)

abbrev I := BitRegisterCode.Instr 38
def table (D : ℕ) (cols : List ℕ) : ℕ := Nat.ofDigits D (cols++[1])

private def params (D stream accum pow : ℕ) : Vars 8 :=
  ![D,stream,accum,pow,stream/D,0,0,0]

def state (m w x y D stream accum pow : ℕ) : Vars 38 :=
  fun i => Fin.addCases (m:=30) (n:=8) (motive:=fun _ => ℕ) (banks blank (io m w x y)) (params D stream accum pow) i

private def loadCode : List I := [⟨.rem,30,31,16⟩]
private def saveCode : List I :=
  [⟨.mul,33,16,35⟩,⟨.add,32,35,32⟩,⟨.mul,33,30,33⟩,⟨.add,34,37,31⟩,
   ⟨.quot,30,31,34⟩,⟨.add,37,37,35⟩,⟨.add,37,37,16⟩]

def body {l} (P : Program 8 38 l) : Code 38 :=
  (compile loadCode).seq ((subroutine P (@left 30 8)).seq ((compile saveCode).seq (peek (34:Fin 38))))

def command {l} (P : Program 8 38 l) : Code 38 :=
  (peek (34:Fin 38)).seq (.while 1 (body P))






/-- Each call to P may update both the running pivot and the current column. -/
inductive Pass {l} (P : Program 8 38 l) (m w D budget : ℕ) : ℕ → List ℕ → ℕ → List ℕ → Prop where
  | nil (x : ℕ) (hx : x < D) : Pass P m w D budget x [] x []
  | cons {x y x' y' xf xs ys}
      (hx : x < D) (hy : y < D) (hx' : x' < D) (hy' : y' < D)
      (step : ∀ r : Regs,∃ k rf, k ≤ budget ∧ Trace P k
        ⟨some P.entry,r,frame (banks blank (io m w x y))⟩
        ⟨none,rf,frame (banks blank (io m w x' y'))⟩)
      (rest : Pass P m w D budget x' xs xf ys) :
      Pass P m w D budget x (y::xs) xf (y'::ys)

def passOverhead := 1000^(loadCode.length+1)+1000^(saveCode.length+1)+3



end DetDLP.BitMatrixPass
end

noncomputable section

namespace DetDLP.HermiteWordPass
open BorderedHermite PackedColumnWords BitMatrixPass
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode

def Active {n} (m k : ℕ) (c : Column n) : Prop :=
  digitsBounded m c ∧ (∀ i : Fin n,i.val < k → c.get i=0) ∧
    (∀ i : Fin n,k ≤ i.val → c.get i < (m:ℤ))

def sweep {n} (m : ℤ) (j : Fin n) (v : Column n) : List (Column n) → Column n × List (Column n)
  | [] => (v,[])
  | c::cs =>
    let z := pivotPair m j v c
    let tail := sweep m j z.1 cs
    (tail.1,z.2::tail.2)



def pivotBudget (m n N : ℕ) := 4*BitPackedPivot.overhead*(bitLen m+n+3)*((2*N).size+2)^2+1


def fixedProgram := compiled BitFixedColumn.command (port (15:Fin 30)) (port (15:Fin 30))
def fixedBudget (n N : ℕ) := BitFixedColumn.overhead*(n+3)*((2*N).size+2)^2+1


end DetDLP.HermiteWordPass
end

noncomputable section

namespace DetDLP.HermiteStageMachine
open BorderedHermite PackedColumnWords HermiteWordPass
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode BitRegisterCall
open BitMatrixPass (table Pass)
abbrev I := BitRegisterCode.Instr 47
abbrev L := Vars 38
abbrev R := Vars 9
abbrev V := Vars 47
def merge (v : L) (a : R) : V := fun i => Fin.addCases (m:=38) (n:=9) (motive:=fun _ => ℕ) v a i
def shell (m D w F A : ℕ) : R := ![m,m+1,D,w,F,A,D/((m+1)*w),1,0]
def initial (m D w F A : ℕ) := merge (fun _ => 0) (shell m D w F A)
private def cp (a dst : Fin 47) : I := ⟨.add,a,46,dst⟩
private def erase (a : Fin 47) := cp 46 a

def prepare : List I :=
  [cp 38 13,cp 39 14,⟨.mul,38,41,15⟩,cp 41 17,cp 45 18,cp 40 30,cp 43 31,cp 45 33,⟨.quot,40,43,34⟩]
def switchPass : List I :=
  [⟨.add,32,33,43⟩,cp 42 31,erase 32,cp 45 33,⟨.quot,40,42,34⟩]
def finish : List I :=
  [⟨.add,15,40,35⟩,⟨.mul,35,33,35⟩,⟨.add,32,35,42⟩,⟨.mul,41,39,41⟩,
   ⟨.mul,39,41,35⟩,⟨.quot,35,40,44⟩,erase 13,erase 14,erase 15,erase 17,
   erase 18,erase 30,erase 31,erase 32,erase 33,erase 34,erase 35]

def passProg {l} (P : Program 8 38 l) :=
  compiled (BitMatrixPass.command P) (port (31:Fin 38)) (port (32:Fin 38))

def command : Code 47 :=
  (compile prepare).seq ((subroutine (passProg BitPackedPivot.program) (@left 38 9)).seq
    ((compile switchPass).seq ((subroutine (passProg fixedProgram) (@left 38 9)).seq (compile finish))))




def bounded {k} (v : Vars k) (N : ℕ) := ∀ i,v i ≤ N






def overhead := 1000^(prepare.length+1)+1000^(switchPass.length+1)+1000^(finish.length+1)+6


end DetDLP.HermiteStageMachine
end

noncomputable section

namespace DetDLP.HermiteRowTrace
open BorderedHermite PackedColumnWords HermiteWordPass HermiteStageMachine
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open BitMatrixPass (table)

def matrixWord {n} (m : ℕ) (a : Array (Column n)) := table ((m+1)^n) (a.toList.map (word (m+1)))
def ceiling (m n c : ℕ) := (m+1)^((n+2)*(n+c+3))
def invariant {n} (m c k : ℕ) (s : Array (Column n) × Array (Column n)) :=
  s.1.size=k ∧ s.2.size=c ∧ (∀ v∈s.1,digitsBounded m v) ∧ (∀ v∈s.2,Active m k v)




def seed {n} (m : ℕ) (j : Fin n) : Column n := Vector.ofFn fun i => if i=j then (m:ℤ) else 0


def rowCost (m n c : ℕ) :=
  let N := ceiling m n c
  (n+c)*(pivotBudget m n N+fixedBudget n N+BitMatrixPass.passOverhead*(N.size+2)^2)+overhead*(N.size+2)^2


end DetDLP.HermiteRowTrace
end

noncomputable section

namespace DetDLP.BitBorderColumn
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open BitMatrixPass (table)
abbrev I := BitRegisterCode.Instr 16

/-- m,b,Q=b^n, the column address, remaining coefficient and matrix streams,
accumulated column, place, scalar product, loop guard and arithmetic scratch. -/
def state (m Q addr A X col w dot : ℕ) : Vars 16 :=
  ![m,m+1,Q,addr,A,X,col,w,dot,A/(m+1),0,0,0,0,1,0]
def stepCode : List I :=
  [⟨.rem,1,4,10⟩,⟨.rem,2,5,11⟩,⟨.quot,3,11,11⟩,⟨.rem,1,11,11⟩,
   ⟨.mul,7,11,12⟩,⟨.add,6,12,6⟩,⟨.mul,1,7,7⟩,⟨.mul,10,11,12⟩,
   ⟨.add,8,12,8⟩,⟨.rem,0,8,8⟩,⟨.add,9,15,4⟩,⟨.quot,1,4,9⟩,
   ⟨.quot,2,5,5⟩,⟨.add,15,15,10⟩,⟨.add,15,15,11⟩,⟨.add,15,15,12⟩]
def body : Code 16 := (compile stepCode).seq (peek (9:Fin 16))
def finish : List I := [⟨.mul,1,6,6⟩,⟨.add,8,6,6⟩,⟨.add,15,15,8⟩]
def command : Code 16 := (peek (9:Fin 16)).seq ((Cmd.while 1 body).seq (compile finish))

def coord (b addr x : ℕ) := x/addr%b
def packA (b : ℕ) (xs : List (ℕ × ℕ)) := table b (xs.map Prod.fst)
def packX (Q : ℕ) (xs : List (ℕ × ℕ)) := Nat.ofDigits Q (xs.map Prod.snd)
def column (b addr : ℕ) (xs : List (ℕ × ℕ)) := Nat.ofDigits b (xs.map (fun s => coord b addr s.2))
def dot (b addr : ℕ) (xs : List (ℕ × ℕ)) := (xs.map (fun s => s.1 * coord b addr s.2)).sum


def cost := 1000^(stepCode.length+1)


end DetDLP.BitBorderColumn
end

noncomputable section

namespace DetDLP.BorderedWords
open BorderedHermite PackedColumnWords
open OAI.Algorithms.SubexponentialSAT SqrtLogSpace

def remDigit (m : ℕ) (z : ℤ) := (z%(m:ℤ)).toNat





def row {n : ℕ} (m : ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :=
  Nat.ofDigits (m+1) (List.ofFn fun j => remDigit m (B i j))
def rows {n : ℕ} (m : ℕ) (a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) :=
  List.ofFn fun i => (a i,row m B i)




def dotZ {n : ℕ} (a : Fin n → ℕ) (v : Fin n → ℤ) :=
  (List.finRange n).foldl (fun s i => s+(a i:ℤ)*v i) 0
def bordered {n : ℕ} (a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) : Array (Column (n+1)) :=
  Array.ofFn fun j => Vector.ofFn (Fin.cases (dotZ a (fun i => B i j)) (fun i => B i j))




end DetDLP.BorderedWords
end

noncomputable section

namespace DetDLP.FramedDigitScan
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls SqrtLogSpace
open BitArithmeticUnit BitRegisterBank BitRegisterCode BitRegisterCall
open BitWordFrames (word value)
open SerializedFieldCall (merge clean)

abbrev I := BitRegisterCode.Instr 13
def data (m stream acc place : ℕ) : Vars 13 :=
  ![m,m+1,m-2,stream,acc,place,0,0,0,stream%2,0,1,2]
def lifted (m stream acc place raw payload : ℕ) : Vars 13 :=
  ![m,m+1,m-2,stream,acc,place,raw,payload,0,1,0,1,2]
def digit (signed : Bool) (m raw : ℕ) :=
  if signed then ((1+(m-2)*(raw%2))*(raw/2))%m else raw
def convert (signed : Bool) : List I := if signed then
  [⟨.rem,12,6,8⟩,⟨.mul,2,8,8⟩,⟨.add,11,8,8⟩,⟨.quot,12,6,6⟩,⟨.mul,8,6,6⟩,⟨.rem,0,6,6⟩] else []
def advance (signed : Bool) : List I := convert signed ++
  [⟨.mul,5,6,8⟩,⟨.add,4,8,4⟩,⟨.mul,1,5,5⟩,⟨.rem,12,3,9⟩,⟨.add,10,10,6⟩,⟨.add,10,10,7⟩,⟨.add,10,10,8⟩]


theorem pop_eq (m acc place : ℕ) (x tail : List Bool) :
    SerializedFieldCall.result (data m (word (true::(Encoding.frame x++tail))) acc place) 3 6 7 x tail =
      lifted m (word tail) acc place (value x) (word x) := by
  funext j; fin_cases j <;> simp [SerializedFieldCall.result,data,lifted,BitWordFrames.word]

theorem advance_ok (s : Bool) (m stream acc w raw p : ℕ) (hm : 2 ≤ m) :
    Valid (advance s) (lifted m stream acc w raw p) ∧
    run (advance s) (lifted m stream acc w raw p)=data m stream (acc+w*digit s m raw) ((m+1)*w) := by
  cases s <;> constructor
  · simp [advance,convert,Valid,Op.Valid,BitRegisterCode.Instr.step,lifted]
  · funext j; fin_cases j <;> rfl
  · simp [advance,convert,Valid,Op.Valid,BitRegisterCode.Instr.step,lifted]; omega
  · funext j; fin_cases j <;> rfl

def adProgram (s : Bool) := compiled (compile (advance s)) (port (0:Fin 13)) (port (0:Fin 13))
def probe : Code 23 := peek (SerializedFieldCall.high (9:Fin 13))
def body (s : Bool) : Code 23 := (SerializedFieldCall.cmd 3 6 7).seq
  ((subroutine (adProgram s) (@right 10 13)).seq probe)
def command (s : Bool) : Code 23 := probe.seq (.while 1 (body s))
def C := SerializedFieldCall.cost+1000^14+10

theorem step_eval (s : Bool) (m acc w N L : ℕ) (hm : 2 ≤ m) (x tail : List Bool) (r : Regs)
    (hL : x.length ≤ L) (h0 : m+1 ≤ N) (h1 : acc ≤ N) (h2 : w ≤ N)
    (h3 : word (true::(Encoding.frame x++tail)) ≤ N)
    (h4 : word x ≤ N) (h5 : word tail ≤ N) :
    ∃ t rf,t ≤ C*(L+4)*(N.size+2)^2 ∧
      Eval (body s) t ⟨r,frame (merge clean (data m (word (true::(Encoding.frame x++tail))) acc w))⟩
        ⟨rf,frame (merge clean (data m (word tail) (acc+w*digit s m (value x)) ((m+1)*w)))⟩ ∧
      rf 1=decide (word tail%2≠0) := by
  let src := word (true::(Encoding.frame x++tail))
  have hp : 2^x.length ≤ N := by rw [BitWordFrames.word_value] at h4; omega
  have hv := (BitWordFrames.value_lt x).le.trans hp
  have hh (i : Fin 13) : data m src acc w i ≤ N := by
    have hsrc : src ≤ N := h3
    have := Nat.mod_lt src (by decide : 0<2)
    fin_cases i <;> simp [data] <;> omega
  obtain ⟨t,rt,ht,et⟩ := SerializedFieldCall.eval (data m src acc w) 3 6 7 x tail rfl N
    (by omega) hh hp h5 r
  change Eval _ _ _ ⟨rt,frame (merge clean (SerializedFieldCall.result (data m (word (true::(Encoding.frame x++tail))) acc w) 3 6 7 x tail))⟩ at et
  rw [pop_eq] at et
  have hp' (i : Fin 13) : lifted m (word tail) acc w (value x) (word x) i ≤ N := by
    fin_cases i <;> simp [lifted] <;> omega
  obtain ⟨v,rv,hv,ev⟩ := run_eval (advance s) _ rt N.size (fun i => Nat.size_le_size (hp' i)) (advance_ok s _ _ _ _ _ _ hm).1
  rw [(advance_ok s _ _ _ _ _ _ hm).2] at ev
  have call := call_right (adProgram s) _ _ clean rt rv (v+1) (compiled_halt_trace ev _ _)
  obtain ⟨rq,eq,hq⟩ := peek_eval (SerializedFieldCall.high (9:Fin 13))
    (merge clean (data m (word tail) (acc+w*digit s m (value x)) ((m+1)*w))) rv
  have hcost : 1000^((advance s).length+1) ≤ 1000^14 := by cases s <;> decide
  have hv' := hv.trans (Nat.mul_le_mul_right ((N.size+2)^2) hcost)
  have ht' := ht.trans (Nat.mul_le_mul_right ((N.size+2)^2) (Nat.mul_le_mul_left SerializedFieldCall.cost
    (show x.length+4 ≤ L+4 by omega)))
  have hpS : 1 ≤ (N.size+2)^2 := Nat.one_le_pow _ _ (by omega)
  refine ⟨_,rq,?_,.seq et (.seq call eq),?_⟩
  · unfold C; nlinarith only [hv',ht',hpS,Nat.zero_le (L*(N.size+2)^2)]
  · exact hq

def packed (s : Bool) (m : ℕ) (xs : List (List Bool)) :=
  Nat.ofDigits (m+1) (xs.map fun x => digit s m (value x))

theorem scan (s : Bool) (m N L : ℕ) (hm : 2 ≤ m) (xs : List (List Bool))
    (hD : ∀ x∈xs,digit s m (value x) < m+1) (hmN : m+1 ≤ N) (hN : 2^(L+1) ≤ N)
    (hL : (Encoding.encodeList id xs).length ≤ L) (acc w : ℕ) (hacc : acc<w)
    (hw : w*(m+1)^xs.length ≤ N) (r : Regs)
    (hr : r 1=decide (word (Encoding.encodeList id xs)%2≠0)) :
    ∃ t rf,t ≤ xs.length*(C*(L+4)*(N.size+2)^2+1)+1 ∧
      Eval (.while 1 (body s)) t ⟨r,frame (merge clean (data m (word (Encoding.encodeList id xs)) acc w))⟩
       ⟨rf,frame (merge clean (data m (word [false]) (acc+w*packed s m xs) (w*(m+1)^xs.length)))⟩ := by
  induction xs generalizing acc w r with
  | nil =>
    have h : r 1=false := by simpa [Encoding.encodeList,BitWordFrames.word] using hr
    exact ⟨1,r,by simp,by simpa [Encoding.encodeList,packed] using
      (Eval.while_false (a:=⟨r,frame (merge clean (data m (word [false]) acc w))⟩) (body:=body s) h)⟩
  | cons x xs ih =>
    let tail := Encoding.encodeList id xs
    have hl : tail.length ≤ L := (BinaryUpdateFields.tail_length x tail).trans hL
    have hx : x.length ≤ L := (BinaryUpdateFields.head_length x tail).trans hL
    have wb (v : List Bool) (hh : v.length ≤ L) : word v ≤ N :=
      ((BinaryUpdateFields.word_bound v).le.trans (Nat.pow_le_pow_right (by decide) (by omega : v.length+1 ≤ L+1))).trans hN
    have wn := (Nat.le_mul_of_pos_right w (pow_pos (Nat.succ_pos m) (x::xs).length)).trans hw
    have hpos : r 1=true := by
      change r 1=decide ((1+2*word (Encoding.frame x++tail))%2≠0) at hr
      simpa using hr
    let d := digit s m (value x)
    obtain ⟨t,rt,ht,et,hr'⟩ := step_eval s m acc w N L hm x tail r hx hmN (hacc.le.trans wn) wn (wb _ hL) (wb _ hx) (wb _ hl)
    have hacc' : acc+w*d < (m+1)*w := by
      simpa [Nat.mul_comm] using BitPackedPivot.digit_bound w acc d (m+1) hacc (hD x (by simp))
    have hw' : ((m+1)*w)*(m+1)^xs.length ≤ N := by simpa only [List.length_cons,pow_succ',Nat.mul_left_comm,Nat.mul_assoc] using hw
    obtain ⟨v,rv,hv,ev⟩ := ih (fun y hy => hD y (by simp [hy])) hl _ _ hacc' hw' rt hr'
    have ep : acc+w*packed s m (x::xs)=(acc+w*d)+((m+1)*w)*packed s m xs := by
      change acc+w*(d+(m+1)*packed s m xs)=_; ring
    refine ⟨t+v+1,rv,?_,?_⟩
    · rw [List.length_cons,Nat.succ_mul]; omega
    · rw [ep,List.length_cons,pow_succ',show w*((m+1)*(m+1)^xs.length)=(m+1)*w*(m+1)^xs.length by ring]
      exact .while_true hpos et ev

end DetDLP.FramedDigitScan
end

noncomputable section
namespace DetDLP.PackedPortBits
open OAI.Algorithms.SubexponentialSAT
abbrev Edges := List (ℕ×ℕ)
def flat (ps : Edges) := ps.flatMap fun p => [p.1,p.2]
def serial (r : ℕ) (ps : Edges) := Nat.ofDigits r (flat ps)+r^(2*ps.length)
theorem serial_cons (r a b : ℕ) (ps : Edges) :
    serial r ((a,b)::ps)=a+r*(b+r*serial r ps) := by
  simp only [serial,flat,List.flatMap_cons,List.cons_append,List.nil_append,Nat.ofDigits_cons,List.length_cons,
    Nat.mul_add,Nat.mul_one,pow_add,pow_two]; ring
theorem serial_pos {r} (hr : 1≤r) (ps : Edges) : 0<serial r ps := by
  unfold serial; positivity

def selected (v bits : ℕ) : Edges → List Bool
  | [] => []
  | (a,b)::xs =>
    let tail := selected v (bits/2) xs
    if a=v ∨ b=v then bits.testBit 0::tail else tail

def specs (G : BipartiteMultigraph) : Edges :=
  (List.finRange G.nE).map fun e => ((G.endpoints e).1.val,(G.endpoints e).2.val)
theorem assignment (G : BipartiteMultigraph) (v : Fin G.nV) (bits : ℕ) :
    selected v.val bits (specs G) =
      List.ofFn (fun j => bits.testBit ((G.ports v).get j).val) := by
  have aux (i : ℕ) (es : List (Fin G.nE)) (ordered : ∀ j : Fin es.length,(es.get j).val=i+j.val) :
      selected v.val (bits/2^i) (es.map fun e => ((G.endpoints e).1.val,(G.endpoints e).2.val))=
      (es.filter fun e => decide ((G.endpoints e).1=v ∨ (G.endpoints e).2=v)).map (fun e => bits.testBit e.val) := by
    induction es generalizing i with
    | nil => rfl
    | cons e es ih =>
      have here : e.val=i := by simpa using ordered 0
      have next := ih (i+1) (by
        intro j; have z := ordered j.succ; simp only [List.get_eq_getElem,Fin.val_succ,List.getElem_cons_succ] at z ⊢; omega)
      have dv : bits/2^i/2=bits/2^(i+1) := by rw [Nat.div_div_eq_div_mul,pow_succ]
      simp only [List.map_cons,selected,List.filter_cons,dv,next]
      have bit : (bits/2^i).testBit 0=bits.testBit e.val := by
        rw [Nat.testBit_div_two_pow,here,Nat.zero_add]
      by_cases q : (G.endpoints e).1=v ∨ (G.endpoints e).2=v
      · have q' : (G.endpoints e).1.val=v.val ∨ (G.endpoints e).2.val=v.val := by simpa only [Fin.val_inj] using q
        simp [q,q',bit]
      · have q' : ¬((G.endpoints e).1.val=v.val ∨ (G.endpoints e).2.val=v.val) := by simpa only [Fin.val_inj] using q
        simp [q,q']
  have h := aux 0 (List.finRange G.nE) (by intro j; simp)
  rw [show (List.ofFn fun j => bits.testBit ((G.ports v).get j).val)=(G.ports v).map (fun e => bits.testBit e.val) from
    List.ofFn_getElem_eq_map (G.ports v) (fun e => bits.testBit e.val)]
  simpa only [specs,pow_zero,Nat.div_one,BipartiteMultigraph.ports] using h

def equal (a b : ℕ) := ((a+1)/(b+1))*((b+1)/(a+1))
theorem equal_spec (a b : ℕ) : equal a b=if a=b then 1 else 0 := by
  rcases lt_trichotomy a b with lt|rfl|gt
  · simp [equal,lt.ne,Nat.div_eq_of_lt (Nat.succ_lt_succ lt)]
  · simp [equal]
  · simp [equal,gt.ne',Nat.div_eq_of_lt (Nat.succ_lt_succ gt)]
def hit (v a b : ℕ) := 1/(1+1/(1+equal a v+equal b v))
theorem hit_spec (v a b : ℕ) : hit v a b=if a=v ∨ b=v then 1 else 0 := by
  by_cases ha : a=v <;> by_cases hb : b=v <;> simp [hit,equal_spec,ha,hb] <;> decide
end DetDLP.PackedPortBits
end

noncomputable section
namespace DetDLP.PortScanArithmetic
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode PackedPortBits
def data (v r s k a w : ℕ) : Vars 16 := ![v+1,r,s,k,a,w,1,2,s/r,0,0,0,0,0,0,0]
end DetDLP.PortScanArithmetic
end

noncomputable section
namespace DetDLP.GraphAssignmentProgram
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open PackedPortBits BitRegisterCode BitArithmeticUnit PortScanArithmetic
def width (G : BipartiteMultigraph) := (G.nV+4)*(2*G.nE+3)
theorem packed_bounds (G : BipartiteMultigraph) :
    let r := G.nV+3
    let ps := specs G
    let N := 2^width G
    r≤N ∧ serial r ps≤N ∧ 2^G.nE≤N ∧ (∀ p∈ps,p.1<r ∧ p.2<r) := by
  intro r ps N
  have enough : 2≤r := by dsimp [r]; omega
  have nr : r≤width G := by unfold width; dsimp [r]; nlinarith only [Nat.zero_le (G.nV*G.nE),Nat.zero_le G.nV,Nat.zero_le G.nE]
  have ne : G.nE≤width G := by unfold width; nlinarith only [Nat.zero_le (G.nV*G.nE),Nat.zero_le G.nV,Nat.zero_le G.nE]
  have valid : ∀ p∈ps,p.1<r ∧ p.2<r := by
    intro p hp; obtain ⟨e,_,rfl⟩ := List.mem_map.mp hp
    exact ⟨lt_trans (G.endpoints e).1.isLt (by dsimp [r]; omega),lt_trans (G.endpoints e).2.isLt (by dsimp [r]; omega)⟩
  have len : ps.length=G.nE := by simp [ps,specs]
  have lf : (flat ps).length=2*G.nE := by simp [flat,List.length_flatMap,len,List.map_const',Nat.mul_comm]
  have dig := Nat.ofDigits_lt_base_pow_length (show 1<r by omega) (l:=flat ps) (by
    intro x hx; obtain ⟨e,he,mem⟩ := List.mem_flatMap.mp hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · exact (valid e he).1
    · exact (valid e he).2)
  rw [lf] at dig
  have powr : r ≤ 2^r := Nat.lt_two_pow_self.le
  have upper := Nat.pow_le_pow_left powr (2*G.nE)
  rw [←pow_mul] at upper
  have step : r*(2*G.nE)+1≤width G := by dsimp [r,width]; nlinarith only [Nat.zero_le G.nV,Nat.zero_le G.nE]
  refine ⟨powr.trans (Nat.pow_le_pow_right (by decide) nr),?_,Nat.pow_le_pow_right (by decide) ne,valid⟩
  unfold serial; rw [len]
  apply le_trans _ (Nat.pow_le_pow_right (by decide) step)
  rw [pow_succ]; omega

structure AddressProgram where
  labels : ℕ
  coefficient : ℕ
  machine : Program 8 24 labels
  correct : ∀ (G : BipartiteMultigraph) (v : Fin G.nV) (k : ℕ) (hk : k<2^G.nE) (reg : Regs),
    let r := G.nV+3
    let ps := specs G
    let start := frame (data v.val r (serial r ps) k 0 1)
    ∃ t rf out,t≤coefficient*(G.nE+1)*(width G+4)^2 ∧
      Trace machine t ⟨some machine.entry,reg,start⟩ ⟨none,rf,out⟩ ∧
      out machine.outputStack=(List.ofFn fun j => k.testBit ((G.ports v).get j).val)++[true]
theorem inhabitedAddress : Nonempty AddressProgram := by
  obtain ⟨l₁,l₂,l₃,K,read,pack,project,all⟩ := contraction_input_and_port_address_machines
  refine ⟨⟨l₃,K,project,?_⟩⟩
  intro G v k hk reg r ps start
  obtain ⟨t,rf,out,ht,tr,word⟩ := (all G [] 0 0 0).2.2 v k hk reg
  have eq : serial r ps=Nat.ofDigits r ((List.finRange G.nE).flatMap fun e => [(G.endpoints e).1.val,(G.endpoints e).2.val])+r^(2*G.nE) := by simp [serial,ps,flat,specs,List.flatMap_map,Function.comp_def]
  refine ⟨t,rf,out,ht,?_,word⟩
  dsimp only [start,data]; rw [eq]; exact tr
noncomputable def address := Classical.choice inhabitedAddress
noncomputable abbrev program := address.machine
noncomputable abbrev charge := address.coefficient
abbrev run (G : BipartiteMultigraph) (v : Fin G.nV) (k : ℕ) (hk : k<2^G.nE) (reg : Regs) :=
  address.correct G v k hk reg
end DetDLP.GraphAssignmentProgram
end

noncomputable section
namespace DetDLP.ContractionInputFields
open OAI.Algorithms.SubexponentialSAT BitProgram SqrtLogSpace
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open BinaryUpdateFields (Pop Parses)
open BitWordFrames (word value)
abbrev ends (G : BipartiteMultigraph) :=
  encodeNatListBin ((List.finRange G.nE).flatMap fun e => [(G.endpoints e).1.val,(G.endpoints e).2.val])
def pops : List (Pop 13) :=
  [⟨0,11,1⟩,⟨0,11,2⟩,⟨0,3,12⟩,⟨0,4,12⟩,⟨0,5,12⟩,⟨2,6,12⟩,⟨2,7,12⟩,⟨2,11,8⟩,⟨2,11,9⟩]
def fields (desc : List Bool) (G : BipartiteMultigraph) (β P ell : ℕ) : Vars 13 :=
  ![word [false],word desc,word [false],β,P,ell,G.nV,G.nE,word (List.ofFn G.side),
    word (ends G),0,value (ends G),word (countWord G.nE)]
def start (xs : List Bool) : Vars 13 := ![word xs,0,0,0,0,0,0,0,0,0,0,0,0]

def program := StructuredCalls.compiled (BinaryUpdateFields.sequence pops) (port (10:Fin 23)) (port (19:Fin 23))
end DetDLP.ContractionInputFields
end

noncomputable section
namespace DetDLP.EndpointPacking
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls SqrtLogSpace
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open BitWordFrames (word value)
open PackedPortBits FramedDigitScan
def finalCode : List (BitRegisterCode.Instr 23) :=
  [⟨.add,SerializedFieldCall.high (4:Fin 13),SerializedFieldCall.high (5:Fin 13),SerializedFieldCall.high (4:Fin 13)⟩]
def machine := compiled ((command false).seq (compile finalCode)) (port (13:Fin 23)) (port (14:Fin 23))
abbrev vals (G : BipartiteMultigraph) := (flat (specs G)).map countWord

def N (G : BipartiteMultigraph) := 2^(GraphAssignmentProgram.width G+(ContractionInputFields.ends G).length+1)
end DetDLP.EndpointPacking
end

noncomputable section
namespace DetDLP.LeafCoefficientReader
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls SqrtLogSpace BoundedProgramLoop
open BitArithmeticUnit BitRegisterBank BitRegisterCode FramedDigitScan
open BitWordFrames (word value)
def machine := compiled (command false) (port (13:Fin 23)) (port (14:Fin 23))
theorem encode_map (l : List ℕ) : Encoding.encodeList id (l.map countWord)=encodeNatListBin l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons,encodeNatListBin,Encoding.encodeList,id_eq] at ih ⊢; rw [ih]
def frameOf (W : ℕ) (bytes : List Bool) :=
    frame (SerializedFieldCall.merge SerializedFieldCall.clean (data (2^W-1) (word bytes) 0 1))
set_option maxHeartbeats 1000000 in
theorem run (W : ℕ) (hW : 2 ≤ W) (xs : List ℕ) (digits : ∀ x∈xs,x < 2^W) (reg : Regs) :
    let w := encodeNatListBin xs
    let L := w.length
    let k := W*(xs.length+1)+L+2
    let N := 2^k
    let T := xs.length*(FramedDigitScan.C*(L+4)*(N.size+2)^2+1)+3
    ∃ t rf out,t ≤ T ∧ SafeTrace (step machine) (cap (N.size+T)) t
      ⟨some machine.entry,reg,frameOf W w⟩ ⟨none,rf,out⟩ ∧ out machine.outputStack=(Nat.ofDigits (2^W) xs).bits := by
  intro w L k N T
  let m := 2^W-1
  let fields := xs.map countWord
  have high : 4 ≤ 2^W := (Nat.pow_le_pow_right (by decide : 0<2) hW : 2^2 ≤ 2^W)
  have base : m+1=2^W := by dsimp [m]; omega
  have enc : Encoding.encodeList id fields=w := encode_map xs
  have len : fields.length=xs.length := by simp [fields]
  have hw : W ≤ k := by dsimp only [k]; rw [Nat.mul_add,Nat.mul_one]; omega
  have a : m+1 ≤ N := by rw [base]; exact Nat.pow_le_pow_right (by decide) hw
  have b : 2^(L+1) ≤ N := Nat.pow_le_pow_right (by decide) (by dsimp [k]; omega)
  have place : (m+1)^fields.length ≤ N := by
    rw [base,len,←pow_mul]; exact Nat.pow_le_pow_right (by decide) (by dsimp [k]; rw [Nat.mul_add]; omega)
  have digit' (x) (hx : x∈fields) : digit false m (value x) < m+1 := by
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hx
    simpa [digit,BitWordFrames.value_count,base] using digits u hu
  have eq : packed false m fields=Nat.ofDigits (2^W) xs := by
    simp [packed,fields,base,List.map_map,Function.comp_def,digit,BitWordFrames.value_count]
  let env := SerializedFieldCall.merge SerializedFieldCall.clean (data m (word w) 0 1)
  obtain ⟨r,p,flag⟩ := peek_eval (SerializedFieldCall.high (9:Fin 13)) env reg
  have flag' : r 1=decide (word (Encoding.encodeList id fields)%2≠0) := by rw [enc]; exact flag
  obtain ⟨u,rf,hu,scan⟩ := FramedDigitScan.scan false m N L (by dsimp [m]; omega) fields digit' a b (by rw [enc]) 0 1 (by decide) (by simpa using place) r flag'
  rw [enc] at scan
  have checked := compiled_halt_trace (Eval.seq p scan) (port (13:Fin 23)) (port (14:Fin 23))
  rw [len] at hu
  have duration : 1+u+1 ≤ T := by dsimp only [T]; omega
  have z : word w ≤ N := (BinaryUpdateFields.word_bound w).le.trans b
  have init (j : Fin 23) : (env j).size ≤ N.size := by
    apply Nat.size_le_size
    apply SerializedFieldCall.merge_bound
    · intro i; fin_cases i <;> simp [SerializedFieldCall.clean,BitWordFrames.state] <;> omega
    · intro i; have h := Nat.mod_lt (word w) (by decide : 0<2)
      fin_cases i <;> simp [data] <;> omega
  refine ⟨_,rf,_,duration,SafeTrace.of_trace checked ?_,?_⟩
  · intro j c hj pref i
    have start : (frame env i).length ≤ N.size := by
      refine Fin.addCases (fun k => ?_) (fun k => ?_) i
      · simp [frame,store]
      · simpa [frame,store,Nat.size_eq_bits_len] using init k
    exact (BitTracePolynomial.trace_grows pref i).trans (Nat.add_le_add start (hj.trans duration))
  · change (0+1*packed false m fields).bits=_
    simp [eq]
end DetDLP.LeafCoefficientReader
end

noncomputable section
namespace DetDLP.PackedEntryStages
open OAI.Algorithms.SubexponentialSAT BitProgram BoundedProgramLoop StructuredCalls SqrtLogSpace
open BitArithmeticUnit LeafScanFrame SubroutineInputBank WordFlow
variable {n S l : ℕ}
abbrev input := Bank 16
abbrev lit (x : ℕ) : Source 16 := .literal x.bits
abbrev slot (x : Fin 16) : Source 16 := .slot x
abbrev Lift (P : Program 8 n l) (hn : n < S) (args : Fin n→Source 16) (out : Fin n) (dst : Fin 16) :=
  HarnessLift.machine hn args P out dst
abbrev boot (a : input) := HarnessLift.clearBank S a
def Short (a : input) (W : ℕ) := ∀ i,(a i).length ≤ W
def sourceBound (args : Fin n→Source 16) := ∀ j,(args j).size ≤ 2
theorem fit (args : Fin n→Source 16) (shape : sourceBound args) (a : input) {W : ℕ} (bd : Short a W) (hw : 2 ≤ W) :
    ∀ i,((args i).read a).length ≤ W := by
  intro i; have h := shape i; cases eq : args i with
  | literal w => rw [eq] at h; exact (show w.length ≤ 2 from h).trans hw
  | slot j => exact bd j
abbrev fits (p : Program 8 n l) (x : Bank n) (out : Fin n) (z : List Bool) (T U : ℕ) := ∀ r : Regs,
  ∃ t rf q,t ≤ T ∧ SafeTrace (step p) (cap U) t ⟨some p.entry,r,x⟩ ⟨none,rf,q⟩ ∧ q out=z
theorem liftRun (P : Program 8 n l) (hn : n < S) (args : Fin n→Source 16) (out : Fin n) (dst : Fin 16)
    (a : input) (W T U : ℕ) (z : List Bool) (bd : Short a W) (hw : 2 ≤ W) (small : sourceBound args)
    (clean : a dst=[]) (call : fits P (fun i => (args i).read a) out z T U) :
    Runs (Lift P hn args out dst) (boot a) (boot (Function.update a dst z))
      (T+SubroutineHarness.extra n W U) (W+U+SubroutineHarness.extra n W U) :=
  fun r => HarnessLift.run hn args P out dst a W T U z r bd (fit args small _ bd hw) clean call
def argPair (i : Fin 16) : Fin 2→Source 16 := ![slot i,lit 0]
def byte (c : Change) (hn : 2 < S) (i dst : Fin 16) := Lift (WordFlow.machine c) hn (argPair i) 0 dst
theorem byteRun (c : Change) (hn : 2 < S) (i dst : Fin 16) (a : input) (w : List Bool) (k W : ℕ)
    (bd : Short a W) (hw : 2 ≤ W) (clean : a dst=[]) (inp : a i=payload c w k) :
    let x := payload c w k
    let T := 6*x.length+15
    let U := x.length+T
    Runs (byte c hn i dst) (boot a) (boot (Function.update a dst (answer c w k)))
      (T+SubroutineHarness.extra 2 W U) (W+U+SubroutineHarness.extra 2 W U) := by
  intro x T U
  apply liftRun _ _ _ _ _ a W T U _ bd hw (by intro j; fin_cases j <;> exact (by decide : 0 ≤ 2)) clean
  have eq : (fun j => ((argPair i) j).read a)=pair x := by
    funext j; fin_cases j <;> simp [argPair,pair,Source.read,inp,x]
  rw [eq]
  intro r; obtain ⟨t,rf,ht,tr⟩ := execute c w k r
  exact ⟨t,rf,_,ht,tr,rfl⟩
def incCode : List (BitRegisterCode.Instr 3) := [⟨.add,0,1,2⟩]
def incMachine := compiled (BitRegisterCode.compile incCode) (BitRegisterBank.port (0:Fin 3)) (BitRegisterBank.port (2:Fin 3))
def wordArgs {s : ℕ} (d : Fin s→Source 16) : Fin (8+s)→Source 16 := Fin.addCases (fun _ => lit 0) d
def incArgs := wordArgs ![slot 1,lit 1,lit 0]
def inc (hn : 11 < S) := Lift incMachine hn incArgs incMachine.outputStack 9
def incTime (W : ℕ) := 1000^2*(W+2)^2+1
theorem incRun (hn : 11 < S) (a : input) (W j : ℕ) (bd : Short a W) (hw : 2 ≤ W) (zero : a 9=[]) (inp : a 1=j.bits) :
    let T := incTime W
    let U := W+T
    Runs (inc hn) (boot a) (boot (Function.update a (9:Fin 16) (j+1).bits))
      (T+SubroutineHarness.extra 11 W U) (W+U+SubroutineHarness.extra 11 W U) := by
  intro T U
  apply liftRun _ _ _ _ _ a W T U _ bd hw (by intro i; fin_cases i <;> decide) zero
  let v : BitRegisterBank.Vars 3 := ![j,1,0]
  have eq : (fun i => (incArgs i).read a)=BitRegisterCode.frame v := by
    funext i; fin_cases i <;> first | exact inp | rfl
  rw [eq]
  intro r; have h := bd 1; rw [inp,Nat.size_eq_bits_len] at h
  have S' (i : Fin 3) : (v i).size ≤ W := by
    fin_cases i
    · exact h
    · change (1:ℕ).size ≤ W; rw [Nat.size_one]; omega
    · exact Nat.zero_le _
  obtain ⟨t,rf,ht,tr⟩ := BitRegisterCode.run_eval incCode v r W S' (by simp [BitRegisterCode.Valid,incCode,Op.Valid])
  have time : t+1 ≤ T := by change t ≤ 1000^2*(W+2)^2 at ht; dsimp only [T,incTime]; omega
  have base : ∀ i,((BitRegisterCode.frame v) i).length ≤ W := by
    rw [←eq]; apply fit _ (by intro i; fin_cases i <;> decide) _ bd hw
  exact ⟨_,rf,_,time,SubroutineHarness.checked incMachine _ _ _ _ base time (compiled_halt_trace tr _ _),rfl⟩
end DetDLP.PackedEntryStages
end

noncomputable section
namespace DetDLP.PackedEntryIO
open OAI.Algorithms.SubexponentialSAT BitProgram BoundedProgramLoop SqrtLogSpace
open BitArithmeticUnit LeafScanFrame SubroutineInputBank WordFlow PackedEntryStages
variable {S : ℕ}
def projArgs := wordArgs ![slot 9,slot 3,slot 4,slot 2,lit 0,lit 1,lit 1,lit 2,slot 5,lit 0,lit 0,lit 0,lit 0,lit 0,lit 0,lit 0]
def project (hn : 24 < S) := Lift GraphAssignmentProgram.program hn projArgs GraphAssignmentProgram.program.outputStack 11
def graphCode (G : BipartiteMultigraph) := PackedPortBits.serial (G.nV+3) (PackedPortBits.specs G)
def projectTime (G : BipartiteMultigraph) :=
  GraphAssignmentProgram.charge*(G.nE+1)*(GraphAssignmentProgram.width G+4)^2
theorem projectRun (hn : 24 < S) (a : input) (W : ℕ) (G : BipartiteMultigraph) (v : Fin G.nV) (k : ℕ)
    (hk : k<2^G.nE) (bd : Short a W) (hw : 2 ≤ W) (zero : a 11=[]) (j : a 9=(v.val+1).bits)
    (r : a 3=(G.nV+3).bits) (s : a 4=(graphCode G).bits) (kk : a 2=k.bits) (tail : a 5=(graphCode G/(G.nV+3)).bits) :
    let z := List.ofFn fun i => k.testBit ((G.ports v).get i).val
    let T := projectTime G
    Runs (project hn) (boot a) (boot (Function.update a (11:Fin 16) (z++[true])))
      (T+SubroutineHarness.extra 24 W (W+T)) (W+(W+T)+SubroutineHarness.extra 24 W (W+T)) := by
  intro z T
  have tiny : sourceBound projArgs := by intro i; fin_cases i <;> decide
  apply liftRun _ _ _ _ _ a W T (W+T) _ bd hw tiny zero
  let d := PortScanArithmetic.data v.val (G.nV+3) (graphCode G) k 0 1
  have eq : (fun i => (projArgs i).read a)=BitRegisterCode.frame d := by
    funext i; refine Fin.addCases (fun j => ?_) (fun t => ?_) i
    · simp only [projArgs,wordArgs,BitRegisterCode.frame,BitRegisterBank.store,Fin.addCases_left,lit,Source.read] <;> rfl
    · simp only [projArgs,wordArgs,BitRegisterCode.frame,BitRegisterBank.store,Fin.addCases_right]
      fin_cases t <;> first | exact j | exact r | exact s | exact kk | exact tail | rfl | (change (2:ℕ).bits=(2:ℕ).bits; rfl)
  intro reg; obtain ⟨t,rf,o,ht,tr,out⟩ := GraphAssignmentProgram.run G v k hk reg
  rw [eq]; have base (i) : (BitRegisterCode.frame d i).length ≤ W := by rw [←eq]; exact fit _ tiny a bd hw i
  exact ⟨t,rf,o,ht,SubroutineHarness.checked _ _ _ _ _ base ht tr,out⟩
def readArgs := wordArgs ![lit 0,lit 0,lit 1,lit 0,lit 0,lit 0,lit 0,lit 0,lit 1,lit 2,
  slot 6,slot 7,slot 8,slot 14,lit 0,lit 1,lit 0,lit 0,lit 0,lit 1,lit 0,lit 1,lit 2]
def read (hn : 31 < S) := Lift LeafCoefficientReader.machine hn readArgs LeafCoefficientReader.machine.outputStack 15
def stream (xs : List ℕ) := BitWordFrames.word (encodeNatListBin xs)
theorem odd {xs : List ℕ} (h : xs≠[]) : stream xs%2=1 := by
  cases xs with
  | nil => contradiction
  | cons u us =>
    change (1+2*BitWordFrames.word _)%2=1
    omega
def readWidth (width : ℕ) (xs : List ℕ) := width*(xs.length+1)+(encodeNatListBin xs).length+2
def readTime (width : ℕ) (xs : List ℕ) := xs.length*(FramedDigitScan.C*((encodeNatListBin xs).length+4)*((2^readWidth width xs).size+2)^2+1)+3
theorem readRun (hn : 31 < S) (a : input) (W width : ℕ) (xs : List ℕ)
    (bd : Short a W) (hw : 2 ≤ W) (zero : a 15=[]) (hd : 2 ≤ width) (nz : xs≠[]) (digits : ∀ x∈xs,x<2^width)
    (m : a 6=(2^width-1).bits) (base : a 7=(2^width).bits) (lo : a 8=(2^width-1-2).bits)
    (w : a 14=(encodeNatListBin xs)++[true]) :
    let T := readTime width xs
    let U := (2^readWidth width xs).size+T
    Runs (read hn) (boot a) (boot (Function.update a (15:Fin 16) (Nat.ofDigits (2^width) xs).bits))
      (T+SubroutineHarness.extra 31 W U) (W+U+SubroutineHarness.extra 31 W U) := by
  intro T U
  apply liftRun _ _ _ _ _ a W T U _ bd hw (by intro i; fin_cases i <;> decide) zero
  have fix : 2^width-1+1=2^width := by have := Nat.two_pow_pos width; omega
  have b' : a 7=(2^width-1+1).bits := by rwa [fix]
  have w' : a 14=(stream xs).bits := by simpa only [stream,BitWordFrames.bits] using w
  have o : (1:ℕ).bits=(stream xs%2).bits := by rw [odd nz]
  have eq : (fun i => (readArgs i).read a)=LeafCoefficientReader.frameOf width (encodeNatListBin xs) := by
    funext i; refine Fin.addCases (fun j => ?_) (fun t => ?_) i
    · simp only [readArgs,wordArgs,LeafCoefficientReader.frameOf,BitRegisterCode.frame,BitRegisterBank.store,Fin.addCases_left,lit,Source.read] <;> rfl
    · simp only [readArgs,wordArgs,LeafCoefficientReader.frameOf,BitRegisterCode.frame,BitRegisterBank.store,Fin.addCases_right]
      fin_cases t <;> first | exact m | exact b' | exact lo | exact w' | exact o | rfl | (change (2:ℕ).bits=(2:ℕ).bits; rfl)
  rw [eq]; exact LeafCoefficientReader.run width hd xs digits
end DetDLP.PackedEntryIO
end

noncomputable section
namespace DetDLP.PackedEntryCall
open OAI.Algorithms.SubexponentialSAT BitProgram BoundedProgramLoop SqrtLogSpace
open BitArithmeticUnit LeafScanFrame SubroutineInputBank WordFlow PackedEntryStages PackedEntryIO
variable {s l S : ℕ} (Q : Program 8 (s+3) l) (it : Fin s)
def args (it : Fin s) : Fin (s+3)→Source 16 := Fin.addCases (fun j => if j=it then slot 0 else lit 0) ![slot 10,slot 12,lit 0]
def evaluator (hn : s+3 < S) := Lift Q hn (args it) (Fin.natAdd s (0:Fin 3)) 13
def inputQ (it : Fin s) (desc vert bits : List Bool) : Fin (s+3)→List Bool :=
  Fin.addCases (fun j => if j=it then desc else []) ![vert,bits,[]]
def outputQ (s : ℕ) (word : List Bool) : Fin (s+3)→List Bool := Fin.addCases (fun _ => []) ![word,[],[]]
def Eval (desc : List Bool) (v : ℕ) (bits w : List Bool) (T U : ℕ) := ∀ r : Fin 8→Bool,
  let V := EntryEvaluatorCall.budget s (EntryCallPreparation.size desc (countWord v) bits) U
  let start : Cfg 8 (s+3) l := ⟨some Q.entry,r,inputQ it desc (countWord v) bits⟩
  ∃ n rf,n ≤ T+V ∧ BitProgram.Trace Q n start ⟨none,rf,outputQ s w⟩ ∧
    ∀ j c,j ≤ n → BitProgram.Trace Q j start c → ∀ i,(c.stacks i).length ≤ V
theorem run (hn : s+3 < S) (a : input) (W T U : ℕ) (desc bits w : List Bool) (v : ℕ)
    (bd : Short a W) (hw : 2 ≤ W) (zero : a 13=[]) (dd : a 0=desc) (vv : a 10=countWord v) (bb : a 12=bits)
    (ev : Eval Q it desc v bits w T U) :
    let V := EntryEvaluatorCall.budget s (EntryCallPreparation.size desc (countWord v) bits) U
    Runs (evaluator Q it hn) (boot a) (boot (Function.update a (13:Fin 16) w))
      (T+V+SubroutineHarness.extra (s+3) W V) (W+V+SubroutineHarness.extra (s+3) W V) := by
  intro V
  have shape : sourceBound (args it) := by
    intro i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · by_cases h : j=it <;> simp [args,h,Source.size,slot,lit]
    · fin_cases j <;> simp [args,Source.size,slot,lit]
  apply liftRun _ _ _ _ _ a W (T+V) V _ bd hw shape zero
  have eq : (fun i => (args it i).read a)=inputQ it desc (countWord v) bits := by
    funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · by_cases h : j=it <;> simp [args,h,inputQ,slot,lit,Source.read,dd]
    · fin_cases j <;> simp [args,inputQ,slot,lit,Source.read,vv,bb]
  rw [eq]; intro r
  obtain ⟨n,rf,ht,tr,room⟩ := ev r
  exact ⟨n,rf,_,ht,SafeTrace.of_trace tr room,by simp [outputQ]⟩
end DetDLP.PackedEntryCall
end

noncomputable section
namespace DetDLP.PackedEntryPipeline
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BoundedProgramLoop SqrtLogSpace
open BitArithmeticUnit LeafScanFrame SubroutineInputBank WordFlow PackedEntryStages PackedEntryIO
variable {s l : ℕ} (Q : Program 8 (s+3) l) (it : Fin s)
def scratch (s : ℕ) := s+32
def cells (G : BipartiteMultigraph) (desc : List Bool) (v : Fin G.nV) (k width : ℕ) (xs : List ℕ) : input :=
  let bits := List.ofFn fun i => k.testBit ((G.ports v).get i).val
  let w := encodeNatListBin xs
  ![desc,v.val.bits,k.bits,(G.nV+3).bits,(graphCode G).bits,(graphCode G/(G.nV+3)).bits,
    (2^width-1).bits,(2^width).bits,(2^width-1-2).bits,(v.val+1).bits,countWord v.val,bits++[true],
    bits,w,w++[true],(Nat.ofDigits (2^width) xs).bits]
def visible (a : input) (p : ℕ) (i : Fin 16) := if i.val<p then a i else []
theorem advance (a : input) (dst : Fin 16) : Function.update (visible a dst.val) dst (a dst)=visible a (dst.val+1) := by
  funext i
  by_cases h : i=dst
  · subst i; simp [visible]
  · have ne : i.val≠dst.val := fun eq => h (Fin.ext eq)
    simp only [Function.update_of_ne h,visible]; by_cases lt : i.val<dst.val <;> simp [lt,show (i.val<dst.val+1) ↔ i.val<dst.val by omega]
theorem vbound {a : input} {W : ℕ} (bd : Short a W) (p : ℕ) : Short (visible a p) W := by
  intro i; unfold visible; split
  · exact bd i
  · exact Nat.zero_le _
theorem ready (s : ℕ) : 31<scratch s := by dsimp only [scratch]; omega
def stage1 := inc (S:=scratch s) (by have := ready s; omega)
def stage2 := byte .count (S:=scratch s) (by have := ready s; omega) 1 10
def stage3 := project (S:=scratch s) (by have := ready s; omega)
def stage4 := byte .unmark (S:=scratch s) (by have := ready s; omega) 11 12
def stage5 := PackedEntryCall.evaluator Q it (S:=scratch s) (by dsimp [scratch]; omega)
def stage6 := byte .mark (S:=scratch s) (by have := ready s; omega) 13 14
def stage7 := read (S:=scratch s) (ready s)
def machine := link (stage1 (s:=s)) (link (stage2 (s:=s)) (link (stage3 (s:=s)) (link (stage4 (s:=s))
  (link (stage5 Q it) (link (stage6 (s:=s)) (stage7 (s:=s)))))))
def bound (s W X : ℕ) := 4*(s+33)*(12*(W+X+1))
theorem bound_local {n s W t u X : ℕ} (hn : n ≤ s+31) (ht : t ≤ X) (hu : u ≤ X) :
    t+SubroutineHarness.extra n W u ≤ bound s W X ∧ W+u+SubroutineHarness.extra n W u ≤ bound s W X := by
  have a := Nat.mul_le_mul hn (Nat.le_refl (7*W+5))
  have b := Nat.mul_le_mul hn (show 2*(W+u)+3 ≤ 2*(W+X)+3 by omega)
  dsimp only [SubroutineHarness.extra,SubroutineHarness.prepareTime,SubroutineHarness.collectTime,bound]
  constructor <;> nlinarith only [a,b,hu,ht,Nat.zero_le (s*W),Nat.zero_le (s*X),Nat.zero_le W,Nat.zero_le X,Nat.zero_le s]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1800000 in
theorem run (G : BipartiteMultigraph) (desc : List Bool) (v : Fin G.nV) (k width : ℕ) (xs : List ℕ)
    (hk : k<2^G.nE) (hd : 2 ≤ width) (ne : xs≠[]) (digits : ∀ x∈xs,x<2^width) (W T U : ℕ) (hw : 2 ≤ W)
    (bd : Short (cells G desc v k width xs) W)
    (ev : PackedEntryCall.Eval Q it desc v.val (List.ofFn fun i => k.testBit ((G.ports v).get i).val) (encodeNatListBin xs) T U) :
    let a := cells G desc v k width xs
    let bits := List.ofFn fun i => k.testBit ((G.ports v).get i).val
    let V := EntryEvaluatorCall.budget s (EntryCallPreparation.size desc (countWord v.val) bits) U
    let X := W+incTime W+projectTime G+7*W+15+V+(2^readWidth width xs).size+readTime width xs
    let M := bound s W X
    Runs (machine Q it) (boot (visible a 9)) (boot (visible a 16)) (T+7*M) M := by
  intro a bits V X M
  let b (j : ℕ) := HarnessLift.clearBank (scratch s) (visible a j)
  have cost {n t u : ℕ} (hn : n ≤ s+31) (ht : t ≤ X) (hu : u ≤ X) := bound_local (W:=W) hn ht hu
  have finish (dst : Fin 16) {labels t u : ℕ} {p : Program 8 (16+scratch s) labels}
      (tr : Runs p (b dst.val) (boot (Function.update (visible a dst.val) dst (a dst))) t u) :
      Runs p (b dst.val) (b (dst.val+1)) t u := by rw [advance a dst] at tr; exact tr
  have step1 : Runs (stage1 (s:=s)) (b 9) (b 10) M M := by
    have tr := incRun (S:=scratch s) (by have := ready s; omega) (visible a 9) W v.val (vbound bd _) hw rfl rfl
    have done := finish 9 tr
    have c := cost (n:=11) (by omega) (t:=incTime W) (by dsimp only [X]; omega) (u:=W+incTime W) (by dsimp only [X]; omega)
    exact weaken done c.1 c.2
  have cell (p : Fin 16) := bd p
  have bytes (c : Change) (src dst : Fin 16) (w : List Bool) (j : ℕ) (before : src.val<dst.val)
      (inp : a src=payload c w j) (out : answer c w j=a dst) :
      Runs (byte c (S:=scratch s) (by have := ready s; omega) src dst) (b dst.val) (b (dst.val+1)) M M := by
    have x := byteRun c (S:=scratch s) (by have := ready s; omega) src dst (visible a dst.val) w j W (vbound bd _) hw
      (by simp [visible]) (by simp [visible,before,inp])
    dsimp only at x
    rw [out] at x
    have done := finish dst x
    have len : (a src).length ≤ W := cell src
    rw [inp] at len
    let u := 6*(payload c w j).length+15
    have lim := cost (n:=2) (by omega) (t:=u) (by dsimp only [X,u]; omega) (u:=(payload c w j).length+u) (by dsimp only [X,u]; omega)
    exact weaken done lim.1 lim.2
  have step2 := bytes .count 1 10 [] v.val (by decide) rfl rfl
  have step3 : Runs (stage3 (s:=s)) (b 11) (b 12) M M := by
    have tr := projectRun (S:=scratch s) (by have := ready s; omega) (visible a 11) W G v k hk (vbound bd _) hw rfl rfl rfl rfl rfl rfl
    have done := finish 11 tr
    have c := cost (n:=24) (by omega) (t:=projectTime G) (by dsimp only [X]; omega) (u:=W+projectTime G) (by dsimp only [X]; omega)
    exact weaken done c.1 c.2
  have step4 := bytes .unmark 11 12 bits 0 (by decide) rfl rfl
  have step5 : Runs (stage5 Q it) (b 13) (b 14) (T+M) M := by
    have tr := PackedEntryCall.run Q it (S:=scratch s) (by dsimp [scratch]; omega) (visible a 13) W T U desc bits (encodeNatListBin xs) v.val
      (vbound bd _) hw rfl rfl rfl rfl ev
    have done := finish 13 tr
    have cap : V ≤ X := by dsimp only [X]; omega
    have c := cost (n:=s+3) (by omega) cap cap
    exact weaken done (by change T+V+SubroutineHarness.extra (s+3) W V ≤ T+M; dsimp only [M]; omega) c.2
  have step6 := bytes .mark 13 14 (encodeNatListBin xs) 0 (by decide) rfl rfl
  have step7 : Runs (stage7 (s:=s)) (b 15) (b 16) M M := by
    have tr := readRun (ready s) (visible a 15) W width xs (vbound bd _) hw rfl hd ne digits rfl rfl rfl rfl
    have done := finish 15 tr
    have c := cost (n:=31) (by omega) (t:=readTime width xs) (by dsimp only [X]; omega)
      (u:=(2^readWidth width xs).size+readTime width xs) (by dsimp only [X]; omega)
    exact weaken done c.1 c.2
  have all := chain step1 (chain step2 (chain step3 (chain step4 (chain step5 (chain step6 step7)))))
  exact weaken all (by omega) (by simp)
end DetDLP.PackedEntryPipeline
end

noncomputable section
namespace DetDLP.LeafAssignmentLoops
open Finset OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BoundedProgramLoop
open BitArithmeticUnit BitRegisterBank BitRegisterCode LeafScanControl LeafScanFrame
variable (K J : ℕ) (F : ℕ→ℕ→ℕ)
def part (k j : ℕ) := ∏ i∈range j,F k i
def total (k : ℕ) := ∑ i∈range k,part F i J
def bank (k j f : ℕ) := core K J k j (part F k j) (total J F k) f (if j=0 then k+1 else j+1) (if j=0 then K/(k+1) else J/(j+1))
theorem pushP (k j : ℕ) : part F k (j+1)=part F k j*F k j := prod_range_succ ..
theorem pushS (k : ℕ) : total J F (k+1)=total J F k+part F k J := sum_range_succ ..
variable {e l : ℕ} (Q : Program 8 (19+e) l)
def inBody := link Q (enlarged inner e)
def inLoop := loop (inBody Q) 1
def productCall := link (enlarged (test 1) e) (inLoop Q)
def outBody := link (productCall Q) (enlarged outer e)
def outLoop := loop (outBody Q) 1
def table := link (enlarged (test 0) e) (outLoop Q)
variable (ctx : Bank e)
def mem (k j f : ℕ) := wide (frame (bank K J F k j f)) ctx
def Small (W : ℕ) := ∀ k,k ≤ K → ∀ j,j ≤ J →
  (∀ i,(bank K J F k j 0 i).size ≤ W) ∧ (k<K → j<J → ∀ i,(bank K J F k j (F k j) i).size ≤ W)
def Action (T U : ℕ) := ∀ k,k<K → ∀ j,j<J → ∀ r : Regs,
    ∃ t rf,t ≤ T ∧ SafeTrace (step Q) (cap U) t
      ⟨some Q.entry,r,mem K J F ctx k j 0⟩ ⟨none,rf,mem K J F ctx k j (F k j)⟩
theorem storeBound (v : Vars 11) (W : ℕ) (w : ∀ j,(v j).size ≤ W) (c : ∀ j,(ctx j).length ≤ W) :
    ∀ i,(wide (frame v) ctx i).length ≤ W := by
  intro i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [wide,Fin.addCases_left]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [frame,store]
    · simpa [frame,store,Nat.size_eq_bits_len] using w j
  · simpa [wide] using c i
abbrev space (W U : ℕ) := W+U+time innerOps W+time outerOps W+2
abbrev oneCost (T W : ℕ) := T+time innerOps W
abbrev productCost (J T W : ℕ) := 4+J*(oneCost T W+1)
abbrev sumCost (J T W : ℕ) := productCost J T W+time outerOps W

theorem vertex_step (T U W : ℕ) (sm : Small K J F W) (run : Action K J F Q ctx T U)
    (ctxb : ∀ i,(ctx i).length ≤ W) (k j : ℕ) (hk : k<K) (hj : j<J) (r : Regs) :
    ∃ t rf,t ≤ oneCost T W ∧ rf 1=decide (j+1<J) ∧ SafeTrace (step (inBody Q)) (cap (space W U)) t
      ⟨some (inBody Q).entry,r,mem K J F ctx k j 0⟩ ⟨none,rf,mem K J F ctx k (j+1) 0⟩ := by
  obtain ⟨n,r₁,ht,callback⟩ := run k hk j hj r
  let a := if j=0 then k+1 else j+1
  let b := if j=0 then K/(k+1) else J/(j+1)
  obtain ⟨m,r₂,hm,flag,tr⟩ := product_step K J k j (part F k j) (total J F k) (F k j) a b W r₁ ((sm k hk.le j hj.le).2 hk hj)
  have dest : core K J k (j+1) (part F k j*F k j) (total J F k) 0 (j+2) (J/(j+2))=bank K J F k (j+1) 0 := by
    simp [bank,pushP]
  rw [dest] at tr
  obtain ⟨r',lift,eq⟩ := keep inner _ _ ctx _ _ (W:=W+time innerOps W) (fun i => (ctxb i).trans (by omega)) tr
  subst r'
  exact ⟨n+m,r₂,by dsimp only [oneCost]; omega,flag,BoundedProgramLink.join _ _
    (EntryEvaluatorCall.mono callback (by dsimp only [space]; omega))
    (EntryEvaluatorCall.mono lift (by dsimp only [space]; omega))⟩

theorem product_run (T U W : ℕ) (sm : Small K J F W) (run : Action K J F Q ctx T U)
    (ctxb : ∀ i,(ctx i).length ≤ W) (k : ℕ) (hk : k<K) (r : Regs) :
    ∃ t rf,t ≤ productCost J T W ∧ SafeTrace (step (productCall Q)) (cap (space W U)) t
      ⟨some (productCall Q).entry,r,mem K J F ctx k 0 0⟩ ⟨none,rf,mem K J F ctx k J 0⟩ := by
  obtain ⟨r₁,flag,tr⟩ := probe 1 (bank K J F k 0 0) r W (sm k hk.le 0 (Nat.zero_le _)).1
  obtain ⟨r',first,eq⟩ := keep (test 1) _ _ ctx _ _ (W:=W+2) (fun j => (ctxb j).trans (by omega)) tr
  subst r'
  have flag' : r₁ 1=decide (0<J) := flag.trans (by change decide (J≠0)=decide (0<J); simp [Nat.pos_iff_ne_zero])
  have blocks j (hj : j<J) (r0 : Regs) (_ : r0 1=true) := vertex_step K J F Q ctx T U W sm run ctxb k j hk hj r0
  obtain ⟨n,rf,time',tail⟩ := forNat (inBody Q) (fun j => mem K J F ctx k j 0) J (oneCost T W) (space W U) r₁ flag'
    (fun j hj i => (storeBound ctx _ W (sm k hk.le j hj).1 ctxb i).trans (by dsimp only [space]; omega)) blocks
  exact ⟨2+n,rf,by dsimp only [productCost]; omega,BoundedProgramLink.join _ _ (EntryEvaluatorCall.mono first (by dsimp only [space]; omega)) tail⟩
end DetDLP.LeafAssignmentLoops
end

noncomputable section
namespace DetDLP.LeafSumMachine
open Finset OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BoundedProgramLoop
open BitArithmeticUnit BitRegisterBank BitRegisterCode LeafScanControl LeafScanFrame LeafAssignmentLoops
variable (K J : ℕ) (F : ℕ→ℕ→ℕ) {e l : ℕ} (Q : Program 8 (19+e) l) (ctx : Bank e)
theorem assignment_step (T U W : ℕ) (sm : Small K J F W) (run : Action K J F Q ctx T U)
    (ctxb : ∀ i,(ctx i).length ≤ W) (k : ℕ) (hk : k<K) (r : Regs) :
    ∃ t rf,t ≤ sumCost J T W ∧ rf 1=decide (k+1<K) ∧ SafeTrace (step (outBody Q)) (cap (space W U)) t
      ⟨some (outBody Q).entry,r,mem K J F ctx k 0 0⟩ ⟨none,rf,mem K J F ctx (k+1) 0 0⟩ := by
  obtain ⟨n,r₁,hn,prod⟩ := product_run K J F Q ctx T U W sm run ctxb k hk r
  let a := if J=0 then k+1 else J+1
  let b := if J=0 then K/(k+1) else J/(J+1)
  obtain ⟨m,rf,hm,flag,tr⟩ := sum_step K J k J (part F k J) (total J F k) a b W r₁ (sm k hk.le J le_rfl).1
  have dest : core K J (k+1) 0 1 (total J F k+part F k J) 0 (k+2) (K/(k+2))=bank K J F (k+1) 0 0 := by
    simp [bank,pushS,part]
  rw [dest] at tr
  obtain ⟨r',end',eq⟩ := keep outer _ _ ctx _ _ (W:=W+time outerOps W) (fun i => (ctxb i).trans (by omega)) tr
  subst r'
  exact ⟨n+m,rf,by dsimp only [sumCost]; omega,flag,BoundedProgramLink.join _ _ prod
    (EntryEvaluatorCall.mono end' (by dsimp only [space]; omega))⟩

theorem run (T U W : ℕ) (sm : Small K J F W) (call : Action K J F Q ctx T U)
    (ctxb : ∀ i,(ctx i).length ≤ W) (r : Regs) :
    ∃ t rf,t ≤ 4+K*(sumCost J T W+1) ∧
      SafeTrace (step (table Q)) (cap (space W U)) t
        ⟨some (table Q).entry,r,mem K J F ctx 0 0 0⟩ ⟨none,rf,mem K J F ctx K 0 0⟩ := by
  obtain ⟨r₁,flag,tr⟩ := probe 0 (bank K J F 0 0 0) r W (sm 0 (Nat.zero_le _) 0 (Nat.zero_le _)).1
  obtain ⟨r',first,eq⟩ := keep (test 0) _ _ ctx _ _ (W:=W+2) (fun j => (ctxb j).trans (by omega)) tr
  subst r'
  have flag' : r₁ 1=decide (0<K) := flag.trans (by change decide (K≠0)=decide (0<K); simp [Nat.pos_iff_ne_zero])
  have blocks j (hj : j<K) (r0 : Regs) (_ : r0 1=true) := assignment_step K J F Q ctx T U W sm call ctxb j hj r0
  obtain ⟨n,rf,time',tail⟩ := forNat (outBody Q) (fun j => mem K J F ctx j 0 0) K (sumCost J T W) (space W U) r₁ flag'
    (fun j hj i => (storeBound ctx _ W (sm j hj 0 (Nat.zero_le _)).1 ctxb i).trans (by dsimp only [space]; omega)) blocks
  exact ⟨2+n,rf,by omega,BoundedProgramLink.join _ _ (EntryEvaluatorCall.mono first (by dsimp only [space]; omega)) tail⟩
end DetDLP.LeafSumMachine
end

noncomputable section

namespace DetDLP.PackedLeafContraction
open Finset Polynomial
variable {ell : ℕ} (G : BipartiteMultigraph)
abbrev table (ell : ℕ) := (v : Fin G.nV)→(Fin (G.deg v)→Bool)→Fin ell→ℕ
noncomputable def entry (a : Fin ell→ℕ) : ℕ[X] := ∑ i,monomial i.val (a i)
noncomputable def Z (A : table G ell) : ℕ[X] :=
  ∑ x : Fin G.nE→Bool,∏ v,entry (A v (fun j => x ((G.ports v).get j)))
def pack (b : ℕ) (a : Fin ell→ℕ) : ℕ := Nat.ofDigits b (List.ofFn a)
theorem pack_sum (b : ℕ) (a : Fin ell→ℕ) : pack b a=∑ i,a i*b^i.val := by
  induction ell with
  | zero => simp [pack]
  | succ n ih =>
    unfold pack
    rw [List.ofFn_succ, Nat.ofDigits, Fin.sum_univ_succ]
    simp only [Fin.val_zero,pow_zero,mul_one, Fin.val_succ, pow_succ]
    have h := ih (fun i => a i.succ)
    unfold pack at h; rw [h]
    rw [mul_comm b,Finset.sum_mul]
    congr 1; apply sum_congr rfl; intro i _; ring

theorem eval_entry (b : ℕ) (a : Fin ell→ℕ) : (entry a).eval b=pack b a := by
  rw [entry,eval_finsetSum,pack_sum]; simp [eval_monomial]
def acc (b : ℕ) (A : table G ell) : ℕ :=
  ∑ x : Fin G.nE→Bool,∏ v,pack b (A v (fun j => x ((G.ports v).get j)))
def width (P ell : ℕ) := G.nE+G.nV*(P+Nat.clog 2 ell)+1+P

theorem eval_acc (A : table G ell) (b : ℕ) : (Z G A).eval b=acc G b A := by
  simp [Z,acc,eval_finsetSum,eval_prod,eval_entry]

theorem mass (P : ℕ) (A : table G ell) (ha : ∀ v t i,A v t i<2^P) :
    acc G 1 A<2^(width G P ell) := by
  let W := P+Nat.clog 2 ell
  have loc (v : Fin G.nV) (t : Fin (G.deg v)→Bool) : (entry (A v t)).eval 1 ≤2^W := by
    rw [entry,eval_finsetSum]; simp only [eval_monomial,one_pow,mul_one]
    calc
      _ ≤ ∑ _ : Fin ell,2^P := sum_le_sum fun i _ => (ha v t i).le
      _ = ell*(2^P) := by simp
      _ ≤ (2^(Nat.clog 2 ell))*(2^P) := Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _)
      _ = _ := by rw [mul_comm,← pow_add]
  have term (x : Fin G.nE→Bool) : (∏ v,(entry (A v (fun j => x ((G.ports v).get j)))).eval 1) ≤ (2^W)^G.nV := by
    calc
      _ ≤ ∏ _ : Fin G.nV,2^W := prod_le_prod' (fun v _ => loc v _)
      _ = _ := by simp
  unfold acc
  simp_rw [← eval_entry]
  calc
    _ ≤ ∑ _ : Fin G.nE→Bool,(2^W)^G.nV := sum_le_sum fun x _ => term x
    _ = 2^G.nE*(2^W)^G.nV := by simp
    _ = 2^(G.nE+G.nV*W) := by rw [pow_add 2 G.nE, Nat.mul_comm G.nV W,pow_mul]
    _ < 2^(width G P ell) := Nat.pow_lt_pow_right (by decide) (by unfold width; dsimp [W]; omega)

theorem coeff_le_mass (f : ℕ[X]) (j : ℕ) : f.coeff j≤f.eval 1 := by
  by_cases h : j∈f.support
  · have e := congrArg (Polynomial.eval 1) f.as_sum_support_C_mul_X_pow
    simp only [eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,one_pow,mul_one] at e
    rw [e]; exact single_le_sum (fun _ _ => Nat.zero_le _) h
  · rw [notMem_support_iff.mp h]; omega

theorem eval_digits (f : ℕ[X]) (b : ℕ) (d : ℕ) (hd : f.natDegree<d) :
    f.eval b=Nat.ofDigits b ((List.range d).map f.coeff) := by
  rw [eval_eq_sum_range' hd]
  induction d with
  | zero => simp
  | succ d _ =>
    have H : ∀ n, (∑ j∈range n,f.coeff j*b^j) = Nat.ofDigits b ((List.range n).map f.coeff) := by
      intro n; induction n with
      | zero => simp
      | succ n ih =>
        rw [sum_range_succ,List.range_succ,List.map_append,Nat.ofDigits_append,ih]
        simp [Nat.ofDigits,mul_comm]
    exact H _

theorem digit (f : ℕ[X]) (b : ℕ) (hb : 1<b) (small : ∀ i,f.coeff i<b) (j : ℕ) :
    f.eval b/b^j%b=f.coeff j := by
  let d := max (f.natDegree+1) (j+1)
  have hd : f.natDegree<d := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hj : j<d := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  let l := (List.range d).map f.coeff
  have hsmall : ∀ v∈l,v<b := by intro v hv; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv; exact small i
  rw [eval_digits f b d hd,Nat.ofDigits_div_pow_eq_ofDigits_drop j (by omega) l hsmall]
  have he : l.drop j=f.coeff j :: l.drop (j+1) := by
    rw [List.drop_eq_getElem_cons (by simpa [l] using hj)]
    simp [l]
  rw [he,Nat.ofDigits,Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (small j)

theorem exact_coefficients (P : ℕ) (A : table G ell) (ha : ∀ v t i,A v t i<2^P) (j : ℕ) :
    let b := 2^(width G P ell)
    acc G b A / b^j % b = (Z G A).coeff j := by
  intro b; rw [← eval_acc]
  have mh := mass G P A ha
  rw [← eval_acc] at mh
  apply digit _ _ (one_lt_pow₀ (by decide) (show width G P ell≠0 by unfold width; omega))
  exact fun i => (coeff_le_mass _ i).trans_lt mh

end DetDLP.PackedLeafContraction
end

noncomputable section

namespace DetDLP.PackedLeafScan
open Finset Polynomial PackedLeafContraction
def bits (n k : ℕ) (j : Fin n) := k.testBit j.val
theorem bijective (n : ℕ) : Function.Bijective (fun k : Fin (2^n) => bits n k.val) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,by simp⟩
  intro x y h; apply Fin.ext; apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j<n
  · exact congrFun h ⟨j,hj⟩
  · have hp := Nat.pow_le_pow_right (n:=2) (by decide) (Nat.le_of_not_gt hj)
    rw [Nat.testBit_eq_false_of_lt (x.isLt.trans_le hp),Nat.testBit_eq_false_of_lt (y.isLt.trans_le hp)]
variable {ell : ℕ} (G : BipartiteMultigraph)
def term (A : table G ell) (b k : ℕ) :=
  ∏ v,pack b (A v (fun i => bits G.nE k ((G.ports v).get i)))

def scan (A : table G ell) (b : ℕ) : ℕ→ℕ→ℕ→ℕ
  | 0,_,acc => acc
  | n+1,k,acc => scan A b n (k+1) (acc+term G A b k)

theorem scan_eq (A : table G ell) (b n k c : ℕ) :
    scan G A b n k c=c+∑ i∈range n,term G A b (k+i) := by
  induction n generalizing k c with
  | zero => simp [scan]
  | succ n ih =>
    rw [scan,ih,sum_range_succ']
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem full (A : table G ell) (b : ℕ) : scan G A b (2^G.nE) 0 0=acc G b A := by
  simp only [scan_eq,zero_add]
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv (Equiv.ofBijective _ (bijective G.nE)) _ _ (fun _ => rfl)

theorem int_poly (A : table G ell) : (Z G A).map (Nat.castRingHom ℤ)=
    BTNContract G (fun v t => ∑ i : Fin ell,monomial i.val (A v t i:ℤ)) := by
  simp [Z,BTNContract,entry,Polynomial.map_prod,Polynomial.map_sum]

theorem word (P : ℕ) (A : table G ell) (ha : ∀ v t i,A v t i<2^P) :
    let W := width G P ell
    let b := 2^W
    let total := scan G A b (2^G.nE) 0 0
    let F := BTNContract G (fun v t => ∑ i : Fin ell,monomial i.val (A v t i:ℤ))
    encodeNatListBin (List.ofFn fun i : Fin ell => total/b^i.val%b%(2^P)) =
      encodeNatListBin (List.ofFn fun i : Fin ell => (F.coeff i.val:ZMod (2^P)).val) := by
  intro W b total F
  apply congrArg encodeNatListBin; apply congrArg List.ofFn
  funext i
  change scan G A b (2^G.nE) 0 0/b^i.val%b%(2^P)=_
  rw [full,exact_coefficients G P A ha i.val]
  dsimp only [F]
  rw [← int_poly G A,coeff_map]
  simp [ZMod.val_natCast]

theorem product_bound (P : ℕ) (A : table G ell) (ha : ∀ v t i,A v t i<2^P)
    (k : ℕ) (vs : Finset (Fin G.nV)) :
    let W := width G P ell
    let b := 2^W
    (∏ v∈vs,pack b (A v (fun i => bits G.nE k ((G.ports v).get i)))) ≤ b^(ell*G.nV) := by
  intro W b
  have hB : 1<b := one_lt_pow₀ (by decide) (by unfold W width; omega)
  have cap : 2^P≤b := Nat.pow_le_pow_right (by decide) (by unfold W width; omega)
  calc
    _ ≤ ∏ _v∈vs,b^ell := by
      apply prod_le_prod'; intro v _
      unfold pack
      apply le_of_lt
      simpa only [List.length_ofFn] using Nat.ofDigits_lt_base_pow_length hB (l:=List.ofFn
        (A v (fun i => bits G.nE k ((G.ports v).get i)))) (by
        intro z hz; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hz; exact (ha _ _ j).trans_le cap)
    _ = b^(ell*vs.card) := by simp [pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (by simpa using vs.card_le_univ))

theorem prefix_size (P : ℕ) (A : table G ell) (ha : ∀ v t i,A v t i<2^P) (n : ℕ) (hn : n≤2^G.nE) :
    (scan G A (2^(width G P ell)) n 0 0).size≤G.nE+width G P ell*(ell*G.nV)+1 := by
  let W := width G P ell
  let b := 2^W
  have bound (k : ℕ) : term G A b k≤b^(ell*G.nV) := product_bound G P A ha k univ
  have H : scan G A b n 0 0≤2^(G.nE+W*(ell*G.nV)) := by
    simp only [scan_eq,zero_add]
    calc
      _ ≤ ∑ _∈range n,b^(ell*G.nV) := sum_le_sum fun k _ => bound k
      _ = n*(b^(ell*G.nV)) := by simp
      _ ≤ 2^G.nE*(b^(ell*G.nV)) := Nat.mul_le_mul_right _ hn
      _ = _ := by rw [pow_add 2 G.nE,pow_mul 2 W]
  apply Nat.size_le.mpr
  exact H.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))
end DetDLP.PackedLeafScan
end

noncomputable section

namespace DetDLP.PackedNetworkLeafMachine
open Finset PackedLeafContraction LeafAssignmentLoops LeafScanControl LeafScanFrame
open OAI.Algorithms.SubexponentialSAT BitProgram BoundedProgramLoop BitArithmeticUnit
variable {ell : ℕ} (G : BipartiteMultigraph) (P : ℕ) (A : table G ell)
abbrev radix := 2^(width G P ell)
def vertex (k : ℕ) (v : Fin G.nV) := pack (radix G P (ell:=ell)) (A v (fun i => k.testBit ((G.ports v).get i).val))
def factor (k j : ℕ) := if h : j<G.nV then vertex G P A k ⟨j,h⟩ else 0
theorem part_eq (k : ℕ) : part (factor G P A) k G.nV=PackedLeafScan.term G A (radix G P (ell:=ell)) k := by
  unfold part
  rw [← Fin.prod_univ_eq_prod_range]
  exact prod_congr rfl fun v _ => by simp [factor,vertex,PackedLeafScan.bits]
theorem total_eq (k : ℕ) : total G.nV (factor G P A) k=PackedLeafScan.scan G A (radix G P (ell:=ell)) k 0 0 := by
  simp [total,PackedLeafScan.scan_eq,part_eq]
abbrev limit := G.nE+width G P ell*(ell*G.nV)+G.nV+4
variable (ha : ∀ v t i,A v t i<2^P)
include ha
theorem part_bound (k j : ℕ) (hj : j ≤ G.nV) : part (factor G P A) k j ≤ (radix G P (ell:=ell))^(ell*G.nV) := by
  let vs := (univ : Finset (Fin j)).map (Fin.castLEEmb hj)
  have h := PackedLeafScan.product_bound G P A ha k vs
  simp only [vs,prod_map] at h
  rw [part,← Fin.prod_univ_eq_prod_range]
  apply le_trans (le_of_eq ?_) h
  exact prod_congr rfl fun v _ => by simp [factor,vertex,v.isLt.trans_le hj,PackedLeafScan.bits,radix] <;> rfl
theorem vertex_bound (k j : ℕ) (hj : j<G.nV) : factor G P A k j ≤ (radix G P (ell:=ell))^(ell*G.nV) := by
  simpa [factor,vertex,hj,PackedLeafScan.bits,radix] using PackedLeafScan.product_bound G P A ha k {⟨j,hj⟩}
theorem small : Small (2^G.nE) G.nV (factor G P A) (limit G P (ell:=ell)) := by
  intro k hk j hj
  let W := limit G P (ell:=ell)
  let M := width G P ell * (ell*G.nV)
  have size_of {x : ℕ} (h : x ≤ (radix G P (ell:=ell))^(ell*G.nV)) : x.size ≤ W := by
    change x ≤ (2^(width G P ell))^(ell*G.nV) at h
    rw [←pow_mul] at h
    have z := Nat.size_le_size h
    rw [Nat.size_pow] at z
    dsimp [W,limit]; omega
  have prod := size_of (part_bound G P A ha k j hj)
  have acc := PackedLeafScan.prefix_size G P A ha k hk
  rw [←total_eq] at acc
  have szJ : G.nV.size ≤ G.nV := Nat.size_le.mpr Nat.lt_two_pow_self
  have szJs : (G.nV+1).size ≤ G.nV+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have szK := Nat.size_pow (n:=G.nE)
  have szKs : (k+1).size ≤ G.nE+2 := by
    apply Nat.size_le.mpr
    have p := Nat.two_pow_pos G.nE
    rw [pow_succ, pow_succ]; omega
  have szk := (Nat.size_le_size hk).trans szK.le
  have szj := (Nat.size_le_size hj).trans szJ
  have szjs := (Nat.size_le_size (Nat.succ_le_succ hj)).trans szJs
  have fK := (Nat.size_le_size (Nat.div_le_self (2^G.nE) (k+1))).trans szK.le
  have fJ := (Nat.size_le_size (Nat.div_le_self G.nV (j+1))).trans szJ
  have leK : G.nE+2 ≤ W := by dsimp only [W,limit]; omega
  have leJ : G.nV+1 ≤ W := by dsimp only [W,limit]; omega
  have leA : (total G.nV (factor G P A) k).size ≤ W := by dsimp only [W,limit]; omega
  have tmp : (if j=0 then k+1 else j+1).size ≤ W := by
    split
    · exact szKs.trans leK
    · exact szjs.trans leJ
  have flag : (if j=0 then 2^G.nE/(k+1) else G.nV/(j+1)).size ≤ W := by
    split
    · exact fK.trans ((Nat.le_succ _).trans leK)
    · exact fJ.trans ((Nat.le_succ _).trans leJ)
  have all (f : ℕ) (hf : f.size ≤ W) (i : Fin 11) : (bank (2^G.nE) G.nV (factor G P A) k j f i).size ≤ W := by
    fin_cases i
    · exact szK.le.trans ((Nat.le_succ _).trans leK)
    · exact szJ.trans ((Nat.le_succ _).trans leJ)
    · exact szk.trans ((Nat.le_succ _).trans leK)
    · exact szj.trans ((Nat.le_succ _).trans leJ)
    · exact prod
    · exact leA
    · exact hf
    · exact Nat.zero_le _
    · change (1:ℕ).size ≤ W; rw [Nat.size_one]; omega
    · exact tmp
    · exact flag
  exact ⟨all 0 (by simp),fun _ h => all _ (size_of (vertex_bound G P A ha k j h))⟩
theorem run {e l : ℕ} (Q : Program 8 (19+e) l) (ctx : Bank e) (T U H : ℕ)
    (call : Action (2^G.nE) G.nV (factor G P A) Q ctx T U) (ctxb : ∀ i,(ctx i).length ≤ H) (r : Regs) :
    let cols := 2^G.nE
    let W := limit G P (ell:=ell)+H
    let F := factor G P A
    let totalWord := PackedLeafScan.scan G A (radix G P (ell:=ell)) cols 0 0
    let Z := BTNContract G (fun v t => ∑ i : Fin ell,Polynomial.monomial i.val (A v t i:ℤ))
    ∃ t rf out,t ≤ 4+cols*(sumCost G.nV T W+1) ∧
      SafeTrace (step (LeafAssignmentLoops.table Q)) (cap (space W U)) t
        ⟨some (LeafAssignmentLoops.table Q).entry,r,mem cols G.nV F ctx 0 0 0⟩ ⟨none,rf,out⟩ ∧
      out ((BitRegisterBank.port (5:Fin 11)).castAdd e)=totalWord.bits ∧
      encodeNatListBin (List.ofFn fun i : Fin ell => totalWord/(radix G P (ell:=ell))^i.val%(radix G P (ell:=ell))%(2^P)) =
        encodeNatListBin (List.ofFn fun i : Fin ell => (Z.coeff i.val:ZMod (2^P)).val) := by
  intro cols W F totalWord Z
  have h := small G P A ha
  have sm : Small cols G.nV F W := by
    intro k hk j hj; obtain ⟨x,y⟩ := h k hk j hj
    exact ⟨fun i => (x i).trans (Nat.le_add_right ..),fun hk hj i => (y hk hj i).trans (Nat.le_add_right ..)⟩
  obtain ⟨t,rf,time,tr⟩ := LeafSumMachine.run cols G.nV F Q ctx T U W sm call (fun i => (ctxb i).trans (Nat.le_add_left ..)) r
  refine ⟨t,rf,_,time,tr,?_,PackedLeafScan.word G P A ha⟩
  change (wide _ ctx ((BitRegisterBank.port (5:Fin 11)).castAdd e))=_
  simp only [wide,Fin.addCases_left]
  change (total G.nV (factor G P A) cols).bits=_
  rw [total_eq]
end DetDLP.PackedNetworkLeafMachine
end

noncomputable section
namespace DetDLP.PackedLeafWiring
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BoundedProgramLoop
open BitArithmeticUnit LeafScanFrame SubroutineInputBank PackedEntryPipeline PackedEntryStages
open LeafAssignmentLoops PackedLeafContraction
variable {n m z l : ℕ}
theorem assocBank (x : Bank n) (y : Bank m) (z' : Bank z) (j : Fin ((n+m)+z)) :
    wide x (wide y z') (Fin.cast (Nat.add_assoc n m z) j)=wide (wide x y) z' j := by
  refine Fin.addCases (fun t => ?_) (fun t => ?_) j
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) t
    · have eq : Fin.cast (Nat.add_assoc n m z) ((i.castAdd m).castAdd z)=i.castAdd (m+z) := Fin.ext rfl
      rw [eq]; simp [wide]
    · have eq : Fin.cast (Nat.add_assoc n m z) ((Fin.natAdd n i).castAdd z)=Fin.natAdd n (i.castAdd z) := Fin.ext rfl
      rw [eq]; simp [wide]
  · have eq : Fin.cast (Nat.add_assoc n m z) (Fin.natAdd (n+m) t)=Fin.natAdd n (Fin.natAdd m t) := Fin.ext (Nat.add_assoc ..)
    rw [eq]; simp [wide]
def regroup (P : Program 8 ((n+m)+z) l) := liftProgram P id (Fin.cast (Nat.add_assoc n m z))
theorem regroupRun (P : Program 8 ((n+m)+z) l) (a b : Bank n) (x : Bank m) (c : Bank z) (T U : ℕ)
    (old : WordFlow.Runs P (wide (wide a x) c) (wide (wide b x) c) T U) :
    WordFlow.Runs (regroup P) (wide a (wide x c)) (wide b (wide x c)) T U := by
  intro r; obtain ⟨t,rf,ht,tr⟩ := old r
  let φ := Fin.cast (Nat.add_assoc n m z)
  have onto : Function.Surjective φ := (finCongr (Nat.add_assoc n m z)).surjective
  obtain ⟨r',exec⟩ := CallOnPorts.run P id φ Function.injective_id (finCongr (Nat.add_assoc n m z)).injective
    (wide a (wide x c)) (wide b (wide x c)) _ _ r rf (assocBank a x c) (assocBank b x c)
    (fun i h => False.elim (h (onto i))) (fun i h => False.elim (h (onto i))) tr
  exact ⟨t,r',ht,exec⟩
abbrev pad (s : ℕ) := 16+scratch s+1
def params (G : BipartiteMultigraph) (desc : List Bool) (width : ℕ) : Bank 7 :=
  ![desc,(G.nV+3).bits,(PackedEntryIO.graphCode G).bits,(PackedEntryIO.graphCode G/(G.nV+3)).bits,
    (2^width-1).bits,(2^width).bits,(2^width-1-2).bits]
abbrev ctx (s : ℕ) (G : BipartiteMultigraph) (desc : List Bool) (width : ℕ) :=
  wide (params G desc width) (SubroutineHarness.empty (pad s))
def pipesrc (s : ℕ) : Fin (16+scratch s)→Source (19+7) :=
  Fin.addCases ![.slot 19,.slot 11,.slot 10,.slot 20,.slot 21,.slot 22,.slot 23,.slot 24,.slot 25,
    .literal [],.literal [],.literal [],.literal [],.literal [],.literal [],.literal []] (fun _ => .literal [])
variable {s lq ell : ℕ} (Q : Program 8 (s+3) lq) (it : Fin s)
def raw := HarnessLift.machine (show 16+scratch s < pad s by exact Nat.lt_succ_self _) (pipesrc s)
  (PackedEntryPipeline.machine Q it) ((15:Fin 16).castAdd (scratch s)) (14:Fin (19+7))
def machine := regroup (n:=19) (m:=7) (z:=pad s) (raw Q it)
variable (G : BipartiteMultigraph) (P : ℕ) (A : PackedLeafContraction.table G ell)
abbrev fac := PackedNetworkLeafMachine.factor G P A
abbrev store (k j f : ℕ) := BitRegisterCode.frame (bank (2^G.nE) G.nV (fac G P A) k j f)
abbrev old (desc : List Bool) (k j f : ℕ) := wide (store G P A k j f) (params G desc (width G P ell))
theorem input_eq (desc : List Bool) (v : Fin G.nV) (k : ℕ) (xs : List ℕ) :
    (fun i => (pipesrc s i).read (old G P A desc k v.val 0)) =
      HarnessLift.clearBank (scratch s) (visible (cells G desc v k (width G P ell) xs) 9) := by
  funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [pipesrc,Fin.addCases_left,HarnessLift.clearBank,wide,Fin.addCases_left]
    fin_cases i <;> rfl
  · simp [pipesrc,Source.read,HarnessLift.clearBank,wide,SubroutineHarness.empty]
theorem changePort {n m : ℕ} (a : Bank n) (c : Bank m) (dst : Fin n) (val : List Bool) :
    Function.update (wide a c) (dst.castAdd m) val=wide (Function.update a dst val) c := by
  funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · by_cases h : j=dst
    · subst j; simp [wide]
    · have ne : j.castAdd m ≠ dst.castAdd m := (Fin.castAdd_injective ..).ne h
      simp [wide,Function.update_of_ne ne,h]
  · have ne : Fin.natAdd n j≠dst.castAdd m := by
      intro eq; have z := congrArg Fin.val eq; change n+j.val=dst.val at z; have := dst.isLt; omega
    simp [wide,Function.update_of_ne ne]
theorem changeNumber {n : ℕ} (v : BitRegisterBank.Vars n) (i : Fin n) (x : ℕ) :
    Function.update (BitRegisterCode.frame v) (BitRegisterBank.port i) x.bits=BitRegisterCode.frame (Function.update v i x) := by
  funext j; refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · change Function.update (BitRegisterCode.frame v) (BitRegisterBank.port i) x.bits (BitRegisterBank.low l)=_
    simp [BitRegisterCode.frame,Function.update_of_ne (BitRegisterBank.low_ne_port l i)]
  · change Function.update (BitRegisterCode.frame v) (BitRegisterBank.port i) x.bits (BitRegisterBank.port l)=_
    by_cases h : l=i
    · subst l; simp [BitRegisterCode.frame]
    · have ne : BitRegisterBank.port l≠BitRegisterBank.port i := (Fin.natAdd_injective ..).ne h
      simp [BitRegisterCode.frame,Function.update_of_ne ne,h]
theorem factorVar (K J k j prod acc x tmp flag : ℕ) :
    Function.update (LeafScanControl.core K J k j prod acc 0 tmp flag) (6:Fin 11) x =
      LeafScanControl.core K J k j prod acc x tmp flag := by
  funext i; fin_cases i <;> simp [Function.update_apply,LeafScanControl.core]
theorem output_eq (desc : List Bool) (k j x : ℕ) :
    Function.update (old G P A desc k j 0) (14:Fin (19+7)) x.bits = old G P A desc k j x := by
  change Function.update (wide _ _) ((BitRegisterBank.port (6:Fin 11)).castAdd 7) x.bits=_
  rw [changePort,changeNumber]
  exact congrArg (fun v => wide (BitRegisterCode.frame v) (params G desc (width G P ell)))
    (factorVar _ _ _ _ _ _ _ _ _)
end DetDLP.PackedLeafWiring
end

noncomputable section
namespace DetDLP.PackedLeafSize
open OAI.Algorithms.SubexponentialSAT SqrtLogSpace PackedLeafContraction PackedEntryPipeline PackedEntryStages PackedEntryIO
variable {ell : ℕ} (G : BipartiteMultigraph) (P : ℕ)
def wordLimit (desc : List Bool) (G : BipartiteMultigraph) (P ell : ℕ) :=
  desc.length+G.nV+G.nE+GraphAssignmentProgram.width G+width G P ell*(ell+1)+ell*(2*(P+1)+2)+10
theorem listBound (xs : List ℕ) (P : ℕ) (h : ∀ x∈xs,x<2^P) :
    (encodeNatListBin xs).length ≤ 1+xs.length*(2*(P+1)+2) := by
  induction xs with
  | nil => simp [encodeNatListBin,Encoding.encodeList]
  | cons x xs ih =>
    have hh := ih (fun z hz => h z (by simp [hz]))
    have sz : x.size ≤ P := Nat.size_le.mpr (h _ (by simp))
    have c : (countWord x).length ≤ P+1 := by
      by_cases z : x=0
      · simp [countWord,z]
      · simp only [countWord,if_neg z,Nat.size_eq_bits_len]; omega
    have fr (l : List Bool) : (Encoding.frame l).length=2*l.length+1 := by
      induction l with
      | nil => rfl
      | cons x l ih => change (Encoding.frame l).length+1+1=_; rw [ih]; simp; omega
    change (Encoding.frame (countWord x)++encodeNatListBin xs).length+1 ≤ _
    simp only [List.length_append,fr,List.length_cons]
    rw [Nat.add_mul xs.length 1,one_mul]; omega
theorem bound (desc : List Bool) (v : Fin G.nV) (k : ℕ) (hk : k<2^G.nE) (a : Fin ell→ℕ) (ha : ∀ i,a i<2^P) :
    Short (cells G desc v k (width G P ell) (List.ofFn a)) (wordLimit desc G P ell) := by
  let W := width G P ell
  let B := wordLimit desc G P ell
  have w : W ≤ B := by dsimp only [B,wordLimit,W]; rw [Nat.mul_add,Nat.mul_one]; omega
  have wp : 0 < W := by dsimp [W,width]; omega
  have pW : P ≤ W := by dsimp [W,width]; omega
  have xs (x) (h : x∈List.ofFn a) : x<2^P := by obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h; exact ha i
  have src := listBound (List.ofFn a) P xs
  simp only [List.length_ofFn] at src
  have ports : (G.ports v).length ≤ G.nE := by
    unfold BipartiteMultigraph.ports; exact (List.length_filter_le ..).trans_eq List.length_finRange
  let bits := List.ofFn fun i => k.testBit ((G.ports v).get i).val
  have inc : (v.val+1).size ≤ G.nV := (Nat.size_le.mpr Nat.lt_two_pow_self).trans v.isLt
  have num : v.val.size ≤ G.nV := (Nat.size_le.mpr Nat.lt_two_pow_self).trans v.isLt.le
  have vert : (countWord v.val).length ≤ G.nV+1 := by
    by_cases h : v.val=0
    · simp [countWord,h]
    · simp only [countWord,if_neg h,Nat.size_eq_bits_len]; omega
  obtain ⟨r,code,_,_⟩ := GraphAssignmentProgram.packed_bounds G
  have rr := Nat.size_le_size r
  have cc := Nat.size_le_size code
  change (graphCode G).size ≤ (2^GraphAssignmentProgram.width G).size at cc
  rw [Nat.size_pow] at rr cc
  have dd := (Nat.size_le_size (Nat.div_le_self (graphCode G) (G.nV+3))).trans cc
  have pp := Nat.size_pow (n:=W)
  have mm := (Nat.size_le_size (Nat.sub_le (2^W) 1)).trans pp.le
  have ll := (Nat.size_le_size (Nat.sub_le (2^W-1) 2)).trans mm
  have cap := Nat.ofDigits_lt_base_pow_length (show 1<2^W from one_lt_pow₀ (by decide) wp.ne') (l:=List.ofFn a)
    (fun x hx => (xs _ hx).trans_le (Nat.pow_le_pow_right (by decide) pW))
  rw [List.length_ofFn,←pow_mul] at cap
  have ax := Nat.size_le.mpr cap
  have digit : bits.length ≤ G.nE := by simpa only [bits,List.length_ofFn,BipartiteMultigraph.deg] using ports
  have round : bits.length+1 ≤ B := by dsimp only [B,wordLimit]; omega
  have d0 : desc.length ≤ B := by dsimp only [B,wordLimit]; omega
  have nv : G.nV+1 ≤ B := by dsimp only [B,wordLimit]; omega
  have ne : G.nE ≤ B := by dsimp only [B,wordLimit]; omega
  have gr : GraphAssignmentProgram.width G+1 ≤ B := by dsimp only [B,wordLimit]; omega
  have ww : W+1 ≤ B := by dsimp only [B,wordLimit,W]; rw [Nat.mul_add,Nat.mul_one]; omega
  have finish : W*ell ≤ B := by dsimp only [B,wordLimit,W]; rw [Nat.mul_add,Nat.mul_one]; omega
  have encoded : (encodeNatListBin (List.ofFn a)).length+1 ≤ B := by dsimp only [B,wordLimit]; omega
  have get (j : Fin 16) : (cells G desc v k W (List.ofFn a) j).length ≤ B := by
    fin_cases j
    · exact d0
    · change v.val.bits.length ≤ B; rw [Nat.size_eq_bits_len]; omega
    · change k.bits.length ≤ B; rw [Nat.size_eq_bits_len]; exact (Nat.size_le.mpr hk).trans ne
    · change (G.nV+3).bits.length ≤ B; rw [Nat.size_eq_bits_len]; exact rr.trans gr
    · change (graphCode G).bits.length ≤ B; rw [Nat.size_eq_bits_len]; exact cc.trans gr
    · change (graphCode G/(G.nV+3)).bits.length ≤ B; rw [Nat.size_eq_bits_len]; exact dd.trans gr
    · change (2^W-1).bits.length ≤ B; rw [Nat.size_eq_bits_len]; exact mm.trans ww
    · change (2^W).bits.length ≤ B; rw [Nat.size_eq_bits_len]; exact pp.le.trans ww
    · change (2^W-1-2).bits.length ≤ B; rw [Nat.size_eq_bits_len]; exact ll.trans ww
    · change (v.val+1).bits.length ≤ B; rw [Nat.size_eq_bits_len]; omega
    · exact vert.trans nv
    · change (bits++[true]).length ≤ B; simpa using round
    · exact digit.trans ne
    · change (encodeNatListBin (List.ofFn a)).length ≤ B; omega
    · change (encodeNatListBin (List.ofFn a)++[true]).length ≤ B; simpa using encoded
    · change (Nat.ofDigits (2^W) (List.ofFn a)).bits.length ≤ B; rw [Nat.size_eq_bits_len]; exact ax.trans finish
  exact get
end DetDLP.PackedLeafSize
end

noncomputable section
namespace DetDLP.PackedLeafCallback
open OAI.Algorithms.SubexponentialSAT BitProgram BoundedProgramLoop SqrtLogSpace
open BitArithmeticUnit LeafScanFrame SubroutineInputBank WordFlow PackedEntryStages PackedEntryIO PackedLeafWiring
open PackedLeafContraction LeafAssignmentLoops
variable {s l ell : ℕ} (Q : Program 8 (s+3) l) (it : Fin s)
variable (G : BipartiteMultigraph) (P : ℕ) (A : PackedLeafContraction.table G ell) (desc : List Bool)
abbrev H := PackedLeafSize.wordLimit desc G P ell
abbrev scalarWidth := width G P ell
abbrev outerWidth := PackedNetworkLeafMachine.limit G P (ell:=ell)+H G P desc (ell:=ell)
def bound (e width ell W U proj : ℕ) :=
  let V := EntryEvaluatorCall.budget e (3*W) U
  let digits := width*(ell+1)+W+2
  let rt := ell*(FramedDigitScan.C*(W+4)*(digits+3)^2+1)+3
  PackedEntryPipeline.bound e W (W+incTime W+proj+7*W+15+V+(digits+1)+rt)
abbrev rate (s U : ℕ) := bound s (scalarWidth G P (ell:=ell)) ell (H G P desc (ell:=ell)) U (projectTime G)
abbrev cost (s T U : ℕ) := T+7*rate G P desc s U (ell:=ell)+SubroutineHarness.extra (16+PackedEntryPipeline.scratch s)
  (outerWidth G P desc (ell:=ell)) (rate G P desc s U (ell:=ell))
abbrev peak (s U : ℕ) := outerWidth G P desc (ell:=ell)+rate G P desc s U (ell:=ell)+
  SubroutineHarness.extra (16+PackedEntryPipeline.scratch s) (outerWidth G P desc (ell:=ell)) (rate G P desc s U (ell:=ell))
theorem localRate (v : Fin G.nV) (k : ℕ) (hk : k<2^G.nE)
    (ha : ∀ v t i,A v t i<2^P) (hp : 1 ≤ P) (hℓ : 0 < ell) (T U : ℕ)
    (eval : ∀ (v : Fin G.nV) (t : Fin (G.deg v)→Bool),PackedEntryCall.Eval Q it desc v.val (List.ofFn t) (encodeNatListBin (List.ofFn (A v t))) T U) :
    let w := scalarWidth G P (ell:=ell)
    let a := List.ofFn (A v (fun i => k.testBit ((G.ports v).get i).val))
    let data := PackedEntryPipeline.cells G desc v k w a
    let M := rate G P desc s U (ell:=ell)
    Runs (PackedEntryPipeline.machine Q it) (boot (PackedEntryPipeline.visible data 9))
      (boot (PackedEntryPipeline.visible data 16)) (T+7*M) M := by
  intro w a data M
  let W := H G P desc (ell:=ell)
  have ha' := fun i => ha v (fun i => k.testBit ((G.ports v).get i).val) i
  have cells : Short data W := PackedLeafSize.bound G P desc v k hk _ ha'
  have win : 2 ≤ W := by dsimp only [W,H,PackedLeafSize.wordLimit]; omega
  have width' : 2 ≤ w := by dsimp only [w,scalarWidth,width]; omega
  have nz : a≠[] := by intro h; have z := congrArg List.length h; simp [a] at z; omega
  have dig (x) (hx : x∈a) : x<2^w := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (ha' i).trans_le (Nat.pow_le_pow_right (by decide) (by dsimp only [w,scalarWidth,width]; omega))
  let bits := List.ofFn fun i => k.testBit ((G.ports v).get i).val
  have exec := PackedEntryPipeline.run Q it G desc v k w a hk width' nz dig W T U win cells (eval _ _)
  have len : (encodeNatListBin a).length ≤ W := cells 13
  have arr : a.length=ell := List.length_ofFn
  let digs := w*(ell+1)+W+2
  have dw : readWidth w a ≤ digs := by dsimp only [digs,readWidth]; rw [arr]; omega
  have rtime : readTime w a ≤ ell*(FramedDigitScan.C*(W+4)*(digs+3)^2+1)+3 := by
    dsimp only [readTime]; rw [Nat.size_pow,arr,show digs+3=(digs+1)+2 by omega]; gcongr
  have vv : EntryEvaluatorCall.budget s (EntryCallPreparation.size desc (countWord v.val) bits) U ≤ EntryEvaluatorCall.budget s (3*W) U := by
    dsimp only [EntryEvaluatorCall.budget]; gcongr
    have d : desc.length ≤ W := cells 0
    have v' : (countWord v.val).length ≤ W := cells 10
    have b : bits.length ≤ W := cells 12
    dsimp only [EntryCallPreparation.size]; omega
  have upper :
      PackedEntryPipeline.bound s W (W+incTime W+projectTime G+7*W+15+
        EntryEvaluatorCall.budget s (EntryCallPreparation.size desc (countWord v.val) bits) U+
        (2^readWidth w a).size+readTime w a) ≤ M := by
    dsimp only [M,rate,bound,PackedEntryPipeline.bound,W,w,scalarWidth,H,digs] at *
    rw [Nat.size_pow]; gcongr <;> omega
  exact weaken exec (Nat.add_le_add_left (Nat.mul_le_mul_left 7 upper) T) upper
theorem action (ha : ∀ v t i,A v t i<2^P) (hp : 1 ≤ P) (hℓ : 0 < ell) (T U : ℕ)
    (eval : ∀ (v : Fin G.nV) (t : Fin (G.deg v)→Bool),PackedEntryCall.Eval Q it desc v.val (List.ofFn t) (encodeNatListBin (List.ofFn (A v t))) T U) :
    Action (2^G.nE) G.nV (fac G P A) (PackedLeafWiring.machine Q it)
      (ctx s G desc (width G P ell)) (cost G P desc s T U (ell:=ell)) (peak G P desc s U (ell:=ell)) := by
  intro k hk j hj
  let v : Fin G.nV := ⟨j,hj⟩
  let bits (i : Fin (G.deg v)) := k.testBit ((G.ports v).get i).val
  let w := width G P ell
  let xs := List.ofFn (A v bits)
  let z := Nat.ofDigits (2^w) xs
  let d := PackedEntryPipeline.cells G desc v k w xs
  let base := old G P A desc k j 0
  let W := outerWidth G P desc (ell:=ell)
  let V := rate G P desc s U (ell:=ell)
  let W₀ := H G P desc (ell:=ell)
  have sh : Short d W₀ := PackedLeafSize.bound G P desc v k hk (A v bits) (ha v bits)
  have context (i) : ((params G desc w) i).length ≤ W₀ := by
    fin_cases i
    · exact sh 0
    · exact sh 3
    · exact sh 4
    · exact sh 5
    · exact sh 6
    · exact sh 7
    · exact sh 8
  have roomb (i) : (base i).length ≤ W := by
    apply storeBound (params G desc w) _ W _ _ i
    · intro i; exact ((PackedNetworkLeafMachine.small G P A ha k hk.le j hj.le).1 i).trans (Nat.le_add_right ..)
    · intro i; exact (context i).trans (Nat.le_add_left ..)
  have eq := input_eq (s:=s) G P A desc v k xs
  change (fun i => (pipesrc s i).read base)=boot (S:=PackedEntryPipeline.scratch s) (PackedEntryPipeline.visible d 9) at eq
  have smallargs (i) : ((pipesrc s i).read base).length ≤ W := by
    change ((fun i => (pipesrc s i).read base) i).length ≤ W
    rw [eq]; refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [boot,HarnessLift.clearBank,wide,Fin.addCases_left]
      exact (PackedEntryPipeline.vbound sh 9 i).trans (Nat.le_add_left ..)
    · simp [boot,HarnessLift.clearBank,wide,SubroutineHarness.empty]
  have free : base (14:Fin (19+7))=[] := rfl
  have got := localRate Q it G P A desc v k hk ha hp hℓ T U eval
  have call : fits (PackedEntryPipeline.machine Q it) (fun i => (pipesrc s i).read base)
      ((15:Fin 16).castAdd (PackedEntryPipeline.scratch s)) z.bits (T+7*V) V := by
    rw [eq]; intro r
    obtain ⟨t,rf,ht,tr⟩ := got r
    refine ⟨t,rf,_,ht,tr,?_⟩
    simp only [boot,HarnessLift.clearBank,wide,Fin.addCases_left]
    rfl
  have value : fac G P A k j=z := by simp [fac,PackedNetworkLeafMachine.factor,hj]; rfl
  have first : Runs (raw Q it)
      (HarnessLift.clearBank (pad s) base) (HarnessLift.clearBank (pad s) (Function.update base (14:Fin (19+7)) z.bits))
      (cost G P desc s T U (ell:=ell)) (peak G P desc s U (ell:=ell)) :=
    fun r => HarnessLift.run _ (pipesrc s) _ _ _ base W (T+7*V) V z.bits r roomb smallargs free call
  have eq1 : Function.update base (14:Fin (19+7)) z.bits=old G P A desc k j (fac G P A k j) :=
    (output_eq G P A desc k j z).trans (by rw [value])
  rw [eq1] at first
  exact regroupRun (raw Q it) _ _ _ _ _ _ first
end DetDLP.PackedLeafCallback
end

noncomputable section
namespace DetDLP.FullScalarLeaf
open OAI.Algorithms.SubexponentialSAT BitProgram BoundedProgramLoop
open BitArithmeticUnit LeafScanFrame LeafAssignmentLoops PackedLeafWiring PackedLeafCallback
open PackedLeafContraction
variable {s l ell : ℕ} (Q : Program 8 (s+3) l) (it : Fin s)
abbrev program := LeafAssignmentLoops.table (PackedLeafWiring.machine Q it)
variable (G : BipartiteMultigraph) (P : ℕ) (A : PackedLeafContraction.table G ell) (desc : List Bool)
theorem paramSize (i : Fin 7) : ((params G desc (width G P ell)) i).length ≤ H G P desc (ell:=ell) := by
  let w := width G P ell
  let room := H G P desc (ell:=ell)
  obtain ⟨r,c,_,_⟩ := GraphAssignmentProgram.packed_bounds G
  have sr := Nat.size_le_size r
  have sc := Nat.size_le_size c
  change (PackedEntryIO.graphCode G).size ≤ (2^GraphAssignmentProgram.width G).size at sc
  rw [Nat.size_pow] at sr sc
  have tail := (Nat.size_le_size (Nat.div_le_self (PackedEntryIO.graphCode G) (G.nV+3))).trans sc
  have graph : GraphAssignmentProgram.width G+1 ≤ room := by dsimp only [room,H,PackedLeafSize.wordLimit]; omega
  have word : w+1 ≤ room := by dsimp only [room,w,H,PackedLeafSize.wordLimit]; rw [Nat.mul_add,Nat.mul_one]; omega
  have pw := Nat.size_pow (n:=w)
  have m := (Nat.size_le_size (Nat.sub_le (2^w) 1)).trans pw.le
  have lo := (Nat.size_le_size (Nat.sub_le (2^w-1) 2)).trans m
  fin_cases i
  · change desc.length ≤ room; dsimp only [room,H,PackedLeafSize.wordLimit]; omega
  · change (G.nV+3).bits.length ≤ room; rw [Nat.size_eq_bits_len]; exact sr.trans graph
  · change (PackedEntryIO.graphCode G).bits.length ≤ room; rw [Nat.size_eq_bits_len]; exact sc.trans graph
  · change (PackedEntryIO.graphCode G/(G.nV+3)).bits.length ≤ room; rw [Nat.size_eq_bits_len]; exact tail.trans graph
  · change (2^w-1).bits.length ≤ room; rw [Nat.size_eq_bits_len]; exact m.trans word
  · change (2^w).bits.length ≤ room; rw [Nat.size_eq_bits_len]; exact pw.le.trans word
  · change (2^w-1-2).bits.length ≤ room; rw [Nat.size_eq_bits_len]; exact lo.trans word
abbrev T0 (s T U : ℕ) := 4+2^G.nE*(sumCost G.nV (cost G P desc s T U (ell:=ell)) (outerWidth G P desc (ell:=ell))+1)
abbrev U0 (s U : ℕ) := space (outerWidth G P desc (ell:=ell)) (peak G P desc s U (ell:=ell))
def start (G : BipartiteMultigraph) (P ell s : ℕ) (desc : List Bool) :=
  let K := 2^G.nE
  let v : BitRegisterBank.Vars 11 := ![K,G.nV,0,0,1,0,0,0,1,1,K]
  wide (BitRegisterCode.frame v) (ctx s G desc (width G P ell))
theorem zeroBank (K J : ℕ) (F : ℕ→ℕ→ℕ) :
    bank K J F 0 0 0=![K,J,0,0,1,0,0,0,1,1,K] := by
  simp [bank,part,LeafAssignmentLoops.total,LeafScanControl.core]
set_option maxRecDepth 12000 in
theorem run (ha : ∀ v t i,A v t i<2^P) (hp : 1 ≤ P) (hℓ : 0 < ell) (T U : ℕ)
    (ev : ∀ (v : Fin G.nV) (t : Fin (G.deg v)→Bool),PackedEntryCall.Eval Q it desc v.val (List.ofFn t) (encodeNatListBin (List.ofFn (A v t))) T U)
    (reg : Regs) :
    let w := width G P ell
    let total := PackedLeafScan.scan G A (2^w) (2^G.nE) 0 0
    let Z := BTNContract G (fun v t => ∑ i : Fin ell,Polynomial.monomial i.val (A v t i:ℤ))
    ∃ t rf o,t ≤ T0 G P desc s T U (ell:=ell) ∧
      SafeTrace (step (program Q it)) (cap (U0 G P desc s U (ell:=ell))) t
        ⟨some (program Q it).entry,reg,start G P ell s desc⟩ ⟨none,rf,o⟩ ∧
      o ((BitRegisterBank.port (5:Fin 11)).castAdd (7+pad s))=total.bits ∧
      encodeNatListBin (List.ofFn fun i : Fin ell => total/(2^w)^i.val%(2^w)%(2^P)) =
        encodeNatListBin (List.ofFn fun i : Fin ell => (Z.coeff i.val:ZMod (2^P)).val) := by
  intro w total Z
  have cb := action Q it G P A desc ha hp hℓ T U ev
  have ctxb (i) : ((ctx s G desc w) i).length ≤ H G P desc (ell:=ell) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [ctx,wide,Fin.addCases_left] using paramSize G P desc j (ell:=ell)
    · simp [ctx,wide,SubroutineHarness.empty]
  have run := PackedNetworkLeafMachine.run G P A ha (PackedLeafWiring.machine Q it)
    (ctx s G desc w) (cost G P desc s T U (ell:=ell)) (peak G P desc s U (ell:=ell)) (H G P desc (ell:=ell)) cb ctxb reg
  have eq : mem (2^G.nE) G.nV (fac G P A) (ctx s G desc w) 0 0 0=start G P ell s desc := by
    exact congrArg (fun v => wide (BitRegisterCode.frame v) (ctx s G desc w)) (zeroBank _ _ _)
  obtain ⟨t,rf,o,ht,tr,hout,word⟩ := run
  rw [eq] at tr
  exact ⟨t,rf,o,ht,tr,hout,word⟩
end DetDLP.FullScalarLeaf
end

noncomputable section
namespace DetDLP.LeafPolynomialBound
variable {α : Type} (N : α→ℕ)
def Bdd (f : α→ℕ) := ∃ c d : ℕ,∀ a,f a ≤ c*(N a+1)^d
theorem const (c : ℕ) : Bdd N (fun _ => c) := ⟨c,0,by simp⟩
theorem below {f h : α→ℕ} (cap : Bdd N h) (le : ∀ a,f a ≤ h a) : Bdd N f := by
  obtain ⟨c,d,all⟩ := cap; exact ⟨c,d,fun a => (le a).trans (all a)⟩
theorem input : Bdd N N := ⟨1,1,by intro x; simp⟩
theorem add {f h : α→ℕ} (bf : Bdd N f) (bh : Bdd N h) : Bdd N (fun a => f a+h a) := by
  obtain ⟨c,d,u⟩ := bf; obtain ⟨b,e,v⟩ := bh
  refine ⟨c+b,d+e,fun a => ?_⟩
  rw [Nat.add_mul]
  exact Nat.add_le_add ((u a).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))))
    ((v a).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))))
theorem mul {f h : α→ℕ} (bf : Bdd N f) (bh : Bdd N h) : Bdd N (fun a => f a*h a) := by
  obtain ⟨c,d,u⟩ := bf; obtain ⟨b,e,v⟩ := bh
  exact ⟨c*b,d+e,fun a => (Nat.mul_le_mul (u a) (v a)).trans_eq (by rw [pow_add]; ring)⟩
theorem pow {f : α→ℕ} (k : ℕ) (bf : Bdd N f) : Bdd N (fun a => f a^k) := by
  obtain ⟨c,d,u⟩ := bf
  refine ⟨c^k,d*k,fun a => ?_⟩
  rw [pow_mul,←mul_pow]; exact Nat.pow_le_pow_left (u a) _
theorem major {f : α→ℕ} (h : Bdd N f) : ∃ K,∀ a,f a ≤ K*(N a+1)^K := by
  obtain ⟨c,d,all⟩ := h; exact ⟨c+d,fun a => (all a).trans (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega)))⟩
structure Data where
  G : BipartiteMultigraph
  desc : List Bool
  P : ℕ
  ell : ℕ
  U : ℕ
def size (d : Data) := d.G.nE+d.G.nV+d.desc.length+d.P+d.ell+d.U+1
open PackedLeafCallback PackedLeafContraction LeafScanControl
noncomputable def overhead (s : ℕ) (d : Data) :=
  let W := outerWidth d.G d.P d.desc (ell:=d.ell)
  let F := cost d.G d.P d.desc s 0 d.U (ell:=d.ell)
  10+(d.G.nV+1)*(F+time innerOps W+1)+time outerOps W+FullScalarLeaf.U0 d.G d.P d.desc s d.U (ell:=d.ell)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem growing (s : ℕ) : Bdd size (overhead s) := by
  have nE : Bdd size (fun d => d.G.nE) := below _ (input size) (by intro a; simp only [size]; omega)
  have nV : Bdd size (fun d => d.G.nV) := below _ (input size) (by intro a; simp only [size]; omega)
  have desc : Bdd size (fun d => d.desc.length) := below _ (input size) (by intro a; simp only [size]; omega)
  have P : Bdd size (fun d => d.P) := below _ (input size) (by intro a; simp only [size]; omega)
  have ell : Bdd size (fun d => d.ell) := below _ (input size) (by intro a; simp only [size]; omega)
  have U : Bdd size (fun d => d.U) := below _ (input size) (by intro a; simp only [size]; omega)
  have logN : Bdd size (fun d => Nat.clog 2 d.ell) :=
    below _ ell (fun d => Nat.clog_le_of_le_pow (Nat.lt_two_pow_self : d.ell < 2^d.ell).le)
  have w : Bdd size (fun d => width d.G d.P d.ell) := by unfold width; exact (add size (add size (add size nE (mul size nV (add size P logN))) (const size _)) P)
  have graph : Bdd size (fun d => GraphAssignmentProgram.width d.G) := by unfold GraphAssignmentProgram.width; exact (mul size (add size nV (const size _)) (add size (mul size (const size _) nE) (const size _)))
  have H' : Bdd size (fun d => H d.G d.P d.desc (ell:=d.ell)) := by unfold H PackedLeafSize.wordLimit; exact (add size (add size (add size (add size (add size (add size desc nV) nE) graph) (mul size w (add size ell (const size _)))) (mul size ell (add size (mul size (const size _) (add size P (const size _))) (const size _)))) (const size _))
  have W : Bdd size (fun d => outerWidth d.G d.P d.desc (ell:=d.ell)) := by unfold outerWidth PackedNetworkLeafMachine.limit; exact (add size (add size (add size (add size nE (mul size w (mul size ell nV))) nV) (const size _)) H')
  have proj : Bdd size (fun d => PackedEntryIO.projectTime d.G) := by
    unfold PackedEntryIO.projectTime
    exact mul size (mul size (const size _) (add size nE (const size _))) (pow size _ (add size graph (const size _)))
  have digits : Bdd size (fun d => width d.G d.P d.ell*(d.ell+1)+H d.G d.P d.desc (ell:=d.ell)+2) := by
    exact (add size (add size (mul size w (add size ell (const size _))) H') (const size _))
  have R : Bdd size (fun d => rate d.G d.P d.desc s d.U (ell:=d.ell)) := by
    dsimp only [rate,bound,PackedEntryPipeline.bound,scalarWidth,EntryEvaluatorCall.budget,PackedEntryStages.incTime]
    exact (mul size (const size _) (mul size (const size _) (add size (add size H' (add size (add size (add size (add size (add size (add size (add size H' (add size (mul size (const size _) (pow size _ (add size H' (const size _)))) (const size _))) proj) (mul size (const size _) H')) (const size _)) (mul size (const size _) (mul size (const size _) (add size (add size (mul size (const size _) H') U) (const size _))))) (add size digits (const size _))) (add size (mul size ell (add size (mul size (mul size (const size _) (add size H' (const size _))) (pow size _ (add size digits (const size _)))) (const size _))) (const size _)))) (const size _))))
  have prep : Bdd size (fun d => SubroutineHarness.extra (16+PackedEntryPipeline.scratch s)
      (outerWidth d.G d.P d.desc (ell:=d.ell)) (rate d.G d.P d.desc s d.U (ell:=d.ell))) := by
    unfold SubroutineHarness.extra SubroutineHarness.prepareTime SubroutineHarness.collectTime; exact (add size (add size (mul size (const size _) (add size (mul size (const size _) W) (const size _))) (const size _)) (add size (add size (mul size (const size _) (add size W R)) (const size _)) (mul size (const size _) (add size (mul size (const size _) (add size W R)) (const size _)))))
  have fin : Bdd size (fun d => cost d.G d.P d.desc s 0 d.U (ell:=d.ell)) := by unfold cost; exact (add size (add size (const size _) (mul size (const size _) R)) prep)
  have space : Bdd size (fun d => peak d.G d.P d.desc s d.U (ell:=d.ell)) := by unfold peak; exact (add size (add size W R) prep)
  have ops (L : List LeafScanControl.I) : Bdd size (fun d => time L (outerWidth d.G d.P d.desc (ell:=d.ell))) := by unfold time; exact (add size (mul size (const size _) (pow size _ (add size W (const size _)))) (const size _))
  have inner := ops innerOps
  have outer := ops outerOps
  change Bdd size (fun d => overhead s d)
  dsimp only [overhead,FullScalarLeaf.U0,LeafAssignmentLoops.space]
  exact (add size (add size (add size (const size _) (mul size (add size nV (const size _)) (add size (add size fin inner) (const size _)))) outer) (add size (add size (add size (add size W space) inner) outer) (const size _)))
theorem time_arith (k j t f a b u : ℕ) (hk : 1 ≤ k) :
    4+k*(4+j*(t+f+a+1)+b+1) ≤ k*(t+1)*(10+(j+1)*(f+a+1)+b+u) := by
  have h : t+f+a+1 ≤ (t+1)*(f+a+1) := by
    rw [Nat.add_mul,Nat.one_mul]; nlinarith only [Nat.zero_le (t*f),Nat.zero_le (t*a)]
  have x := Nat.mul_le_mul_left j h
  have y : 9+b ≤ (t+1)*(10+b+u) := by
    exact (show 9+b ≤ 10+b+u by omega).trans (Nat.le_mul_of_pos_left _ (by omega))
  have z : 9+j*(t+f+a+1)+b ≤ (t+1)*(10+(j+1)*(f+a+1)+b+u) := by
    have hh := Nat.add_le_add x y
    calc
      _ = j*(t+f+a+1)+(9+b) := by ring
      _ ≤ j*((t+1)*(f+a+1))+(t+1)*(10+b+u) := hh
      _ ≤ _ := by
        rw [Nat.add_mul,Nat.one_mul]
        nlinarith only [Nat.zero_le ((t+1)*(f+a+1))]
  calc
    _ ≤ 4*k+k*(4+j*(t+f+a+1)+b+1) := by omega
    _ = k*(9+j*(t+f+a+1)+b) := by ring
    _ ≤ _ := (Nat.mul_le_mul_left k z).trans_eq (by ring)
theorem uniform (s : ℕ) : ∃ K,∀ (d : Data) (T : ℕ),
    FullScalarLeaf.T0 d.G d.P d.desc s T d.U (ell:=d.ell) ≤ 2^d.G.nE*(T+1)*(K*(size d+1)^K) ∧
    FullScalarLeaf.U0 d.G d.P d.desc s d.U (ell:=d.ell) ≤ K*(size d+1)^K := by
  obtain ⟨K,hK⟩ := major size (growing s)
  refine ⟨K,fun d T => ⟨?_,?_⟩⟩
  · apply le_trans _ (Nat.mul_le_mul_left _ (hK d))
    let F := cost d.G d.P d.desc s 0 d.U (ell:=d.ell)
    let W := outerWidth d.G d.P d.desc (ell:=d.ell)
    have eq : cost d.G d.P d.desc s T d.U (ell:=d.ell)=T+F := by
      dsimp only [cost,F]; omega
    dsimp only [FullScalarLeaf.T0,LeafAssignmentLoops.sumCost,LeafAssignmentLoops.productCost,LeafAssignmentLoops.oneCost]
    rw [eq]
    exact time_arith _ _ _ _ _ _ _ (Nat.one_le_two_pow)
  · exact (Nat.le_add_left _ _).trans (hK d)
end DetDLP.LeafPolynomialBound
end

noncomputable section
namespace DetDLP.ExhaustiveLeafExport
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open Finset Polynomial
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1600000 in
theorem full (E : PrimitiveMachine) (out : Fin E.tapeCount) :
    ∃ (s l K : ℕ) (M : BitProgram.Program 8 (19+(7+s)) l),
      ∀ (G : BipartiteMultigraph) (P ell : ℕ) (desc : List Bool)
        (A : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→Fin ell→ℕ)
        (T U : ℕ),0<P → 0<ell → (∀ v t i,A v t i<2^P) →
        (∀ v t,RunsWithin E out (encodePortQuery desc v.val (List.ofFn t))
          (encodeNatListBin (List.ofFn (A v t))) T U) →
        let w := G.nE+G.nV*(P+Nat.clog 2 ell)+1+P
        let r := G.nV+3
        let pairs := (List.finRange G.nE).map fun e => ((G.endpoints e).1.val,(G.endpoints e).2.val)
        let code := Nat.ofDigits r (pairs.flatMap fun xy => [xy.1,xy.2])+r^(2*pairs.length)
        let frame := Fin.addCases (m:=8) (n:=11) (fun _ => ([]:List Bool))
          (fun j => ((![2^G.nE,G.nV,0,0,1,0,0,0,1,1,2^G.nE] : Fin 11→ℕ) j).bits)
        let metadata : Fin 7→List Bool := ![desc,r.bits,code.bits,(code/r).bits,(2^w-1).bits,(2^w).bits,(2^w-1-2).bits]
        let input := Fin.addCases frame (Fin.addCases metadata (fun _ : Fin s => ([]:List Bool)))
        let cap := K*(G.nE+G.nV+desc.length+P+ell+(U+8)+1+1)^K
        let Z := BTNContract G (fun v t => ∑ i : Fin ell,monomial i.val (A v t i:ℤ))
        ∀ reg : Fin 8→Bool,
        let start : BitProgram.Cfg 8 (19+(7+s)) l := ⟨some M.entry,reg,input⟩
        ∃ (z steps : ℕ) (rf : Fin 8→Bool) (o : Fin (19+(7+s))→List Bool),steps ≤ 2^G.nE*(8*T+1)*cap ∧
          BitProgram.Trace M steps start ⟨none,rf,o⟩ ∧
          (∀ j c,j ≤ steps → BitProgram.Trace M j start c → ∀ i,(c.stacks i).length ≤ cap) ∧
          o ((13:Fin 19).castAdd (7+s))=z.bits ∧
          encodeNatListBin (List.ofFn fun i : Fin ell => z/(2^w)^i.val%(2^w)%(2^P))=
          encodeNatListBin (List.ofFn fun i : Fin ell => (Z.coeff i.val:ZMod (2^P)).val) := by
  obtain ⟨s,l,Q,it,H⟩ := reusable_primitive_tensor_entry_call E out
  obtain ⟨K,h⟩ := LeafPolynomialBound.uniform s
  refine ⟨PackedLeafWiring.pad s,_,K,FullScalarLeaf.program Q it,?_⟩
  intro G P ell desc A T U hp he ha calls w r pairs code frame metadata input cap Z reg start
  have sub (v : Fin G.nV) (t : Fin (G.deg v)→Bool) : PackedEntryCall.Eval Q it desc v.val
      (List.ofFn t) (encodeNatListBin (List.ofFn (A v t))) (8*T) (U+8) := by
    exact H desc v.val (List.ofFn t) _ T U (calls v t)
  obtain ⟨n,rf,o,tm,run,word,exactWord⟩ := FullScalarLeaf.run Q it G P A desc ha hp he (8*T) (U+8) sub reg
  obtain ⟨time,room⟩ := h ⟨G,desc,P,ell,U+8⟩ (8*T)
  refine ⟨_,n,rf,o,tm.trans time,run.forget,?_,word,exactWord⟩
  intro j c hj pref i
  exact (run.within j c hj pref i).trans room
end DetDLP.ExhaustiveLeafExport
end

open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation Finset Polynomial
set_option maxRecDepth 16000 in
set_option maxHeartbeats 2400000 in
theorem solution (E : PrimitiveMachine) (out : Fin E.tapeCount) :
    ∃ (s l K : ℕ) (M : BitProgram.Program 8 (19+(7+s)) l),
      ∀ (G : BipartiteMultigraph) (P ell : ℕ) (desc : List Bool)
        (A : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→Fin ell→ℕ)
        (T U : ℕ),0<P → 0<ell → (∀ v t i,A v t i<2^P) →
        (∀ v t,RunsWithin E out (encodePortQuery desc v.val (List.ofFn t))
          (encodeNatListBin (List.ofFn (A v t))) T U) →
        let w := G.nE+G.nV*(P+Nat.clog 2 ell)+1+P
        let r := G.nV+3
        let pairs := (List.finRange G.nE).map fun e => ((G.endpoints e).1.val,(G.endpoints e).2.val)
        let code := Nat.ofDigits r (pairs.flatMap fun xy => [xy.1,xy.2])+r^(2*pairs.length)
        let frame := Fin.addCases (m:=8) (n:=11) (fun _ => ([]:List Bool))
          (fun j => ((![2^G.nE,G.nV,0,0,1,0,0,0,1,1,2^G.nE] : Fin 11→ℕ) j).bits)
        let metadata : Fin 7→List Bool := ![desc,r.bits,code.bits,(code/r).bits,(2^w-1).bits,(2^w).bits,(2^w-1-2).bits]
        let input := Fin.addCases frame (Fin.addCases metadata (fun _ : Fin s => ([]:List Bool)))
        let cap := K*(G.nE+G.nV+desc.length+P+ell+(U+8)+1+1)^K
        let Z := BTNContract G (fun v t => ∑ i : Fin ell,monomial i.val (A v t i:ℤ))
        ∀ reg : Fin 8→Bool,
        let start : BitProgram.Cfg 8 (19+(7+s)) l := ⟨some M.entry,reg,input⟩
        ∃ (z steps : ℕ) (rf : Fin 8→Bool) (o : Fin (19+(7+s))→List Bool),steps ≤ 2^G.nE*(8*T+1)*cap ∧
          BitProgram.Trace M steps start ⟨none,rf,o⟩ ∧
          (∀ j c,j ≤ steps → BitProgram.Trace M j start c → ∀ i,(c.stacks i).length ≤ cap) ∧
          o ((13:Fin 19).castAdd (7+s))=z.bits ∧
          encodeNatListBin (List.ofFn fun i : Fin ell => z/(2^w)^i.val%(2^w)%(2^P))=
          encodeNatListBin (List.ofFn fun i : Fin ell => (Z.coeff i.val:ZMod (2^P)).val) := by
  exact ExhaustiveLeafExport.full E out
