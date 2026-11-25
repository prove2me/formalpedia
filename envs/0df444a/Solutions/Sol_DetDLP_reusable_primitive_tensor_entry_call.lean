-- Prove2me | solution 1 for DetDLP.reusable_primitive_tensor_entry_call
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T18:29:10.603833+00:00
-- url     : https://prove2.me/submissions/c027518c-ca86-43c9-9024-c3adab702268

import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S067
import Definitions.Def_DetDLP_Machine
import Definitions.Def_DetDLP_FilterAndCoset
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S045
import Theorems.Thm_DetDLP_bounded_entry_evaluator_stack_simulation

section

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

private theorem value_append_zero (xs : List Bool) : BinaryArithmetic.toNat (xs++[false]) = BinaryArithmetic.toNat xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [ih]

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

section

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

section

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

section

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

private theorem step_result (s : State) : result (step s) = result s := by
  by_cases hr : s.r = 0
  · simp [step,hr]
  · simp only [result,step,if_neg hr]
    exact (Nat.xgcdAux_rec (Nat.pos_of_ne_zero hr)).symm

private theorem run_result (k : ℕ) (s : State) : result (run k s) = result s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact (ih (step s)).trans (step_result s)

private theorem mod_twice (a b : ℕ) (h : 0 < b) (hle : b ≤ a) : 2*(a%b) ≤ a := by
  by_cases half : 2*b ≤ a
  · have := Nat.mod_lt a h; omega
  · rw [Nat.mod_eq_sub_mod hle,Nat.mod_eq_of_lt (by omega : a-b < b)]; omega

private theorem shrink (s : State) : 2*(step (step s)).r ≤ s.r := by
  by_cases h : s.r = 0
  · simp [step,h]
  · have hg : (step s).r = s.oldR%s.r := by simp [step,h]
    have ho : (step s).oldR = s.r := by simp [step,h]
    by_cases hz : (step s).r = 0
    · have eqs : step (step s) = step s := if_pos hz
      rw [eqs,hz]; simp
    · have ht : (step s).r < s.r := by rw [hg]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero h)
      calc
        _ = 2*(s.r % (step s).r) := by have hg2 : (step (step s)).r = (step s).oldR % (step s).r := congrArg State.r (if_neg hz : step (step s) = _)
                                       rw [hg2,ho]
        _ ≤ _ := mod_twice _ _ (Nat.pos_of_ne_zero hz) ht.le

private theorem stopped (h : ℕ) (s : State) (hs : s.r < 2^h) : (run (2*h) s).r = 0 := by
  induction h generalizing s with
  | zero => simp [run] at *; omega
  | succ h ih =>
    rw [Nat.mul_succ]
    change (run (2*h) (step (step s))).r = 0
    apply ih
    have := shrink s; rw [pow_succ] at hs; omega

private def Bounded (M A : ℕ) (s : State) :=
  s.r ≤ M ∧ s.oldR ≤ M ∧ s.u.natAbs ≤ A ∧ s.v.natAbs ≤ A ∧ s.oldU.natAbs ≤ A ∧ s.oldV.natAbs ≤ A

private theorem bound_step {M A : ℕ} {s : State} (h : Bounded M A s) : Bounded M ((M+1)*A) (step s) := by
  obtain ⟨hr,ho,hu,hv,hou,hov⟩ := h
  have ha : A ≤ (M+1)*A := by rw [Nat.add_mul]; omega
  by_cases hz : s.r = 0
  · simp only [step,if_pos hz,Bounded]; omega
  · have hq : s.oldR/s.r ≤ M := (Nat.div_le_self ..).trans ho
    have hcomb (x y : ℤ) (hx : x.natAbs ≤ A) (hy : y.natAbs ≤ A) :
        (x-((s.oldR/s.r : ℕ):ℤ)*y).natAbs ≤ (M+1)*A := by
      apply (Int.natAbs_sub_le ..).trans
      rw [Int.natAbs_mul,Int.natAbs_natCast,Nat.add_mul,one_mul]
      exact (Nat.add_le_add hx (Nat.mul_le_mul hq hy)).trans_eq (add_comm ..)
    simp only [step,if_neg hz,Bounded]
    exact ⟨(Nat.mod_le ..).trans ho,hr,hcomb _ _ hou hu,hcomb _ _ hov hv,hu.trans ha,hv.trans ha⟩

private theorem bound_run (k M A : ℕ) (s : State) (h : Bounded M A s) :
    Bounded M ((M+1)^k*A) (run k s) := by
  induction k generalizing s A with
  | zero => simpa [run] using h
  | succ k ih => simpa [run,pow_succ,mul_assoc] using ih ((M+1)*A) (step s) (bound_step h)

def init (x y : ℕ) : State := ⟨x,1,0,y,0,1⟩

/-- A logarithmic, input-independent iteration cap suffices for the exact coefficients
used in the column program. The polynomial bit bound covers every prefix, even before stopping. -/
theorem costed_xgcd {M : ℕ} (x y : ℕ) (hx : x ≤ M) (hy : y ≤ M) :
    let h := bitLen M+1
    let z := run (2*h) (init x y)
    z.r = 0 ∧ z.oldR = x.gcd y ∧ z.oldU = x.gcdA y ∧ z.oldV = x.gcdB y ∧
      ∀ k ≤ 2*h, let s := run k (init x y)
        s.r ≤ M ∧ s.oldR ≤ M ∧
          ∀ a ∈ [s.u,s.v,s.oldU,s.oldV], a.natAbs ≤ 2^(2*h^2) := by
  intro h z
  have hM := Nat.le_pow_clog (b := 2) (by decide) M
  have hh : M+1 ≤ 2^h := by
    dsimp [h,bitLen]; rw [pow_succ]
    have hp : 0 < 2^Nat.clog 2 M := by positivity
    omega
  have hz : z.r = 0 := stopped h _ (by change x < 2^h; omega)
  have he := run_result (2*h) (init x y)
  change Nat.xgcdAux z.r z.u z.v z.oldR z.oldU z.oldV = Nat.xgcdAux x 1 0 y 0 1 at he
  rw [hz,Nat.xgcd_zero_left] at he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg (fun z => z.2.1) he
  have h3 := congrArg (fun z => z.2.2) he
  refine ⟨hz,h1.trans (Nat.xgcdAux_fst ..),h2,h3,?_⟩
  intro k hk s
  have hh0 : Bounded M 1 (init x y) := by simp [Bounded,init,hx,hy]
  obtain ⟨hr,ho,h1,h2,h3,h4⟩ := bound_run k M 1 _ hh0
  have hab : (M+1)^k*1 ≤ 2^(2*h^2) := by
    rw [mul_one]
    calc
      _ ≤ (2^h)^k := Nat.pow_le_pow_left hh _
      _ = 2^(h*k) := (pow_mul ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith only [Nat.mul_le_mul_left h hk])
  refine ⟨hr,ho,?_⟩
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl <;> first | exact h1.trans hab | exact h2.trans hab | exact h3.trans hab | exact h4.trans hab
end DetDLP.BoundedExtendedEuclid
end

section

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

private theorem move_eval (src dst : Fin 8) (hs : src ≠ 1) (hd : dst ≠ 1) (hsd : src ≠ dst)
    (r : regs) (st : Stk) (ht : st 1 = []) (he : st dst = []) :
    ∃ rf, Eval (move src dst) (6*(st src).length+6)
      ⟨r,st⟩ ⟨rf, Function.update (Function.update st src []) dst (st src)⟩ := by
  have h₁ := ArrayUpdatePrograms.transfer_eval src 1 0 1 hs (by decide) r st
  have h₂ := ArrayUpdatePrograms.transfer_eval 1 dst 0 1 (Ne.symm hd) (by decide)
    (readRegs r 0 1 none) (transferStacks src 1 st)
  have h := Eval.seq h₁ h₂
  have heq : transferStacks 1 dst (transferStacks src 1 st) =
      Function.update (Function.update st src []) dst (st src) := by
    funext i
    by_cases h1 : i = 1
    · subst i; simp [transferStacks,Function.update_apply,hs,hd,Ne.symm hs,Ne.symm hd,ht]
    · by_cases h2 : i = dst
      · subst i; simp [transferStacks,Function.update_apply,hs,hd,hsd,Ne.symm hs,Ne.symm hsd,ht,he]
      · simp [transferStacks,Function.update_apply,h1,h2]
  rw [heq] at h
  refine ⟨readRegs (readRegs r 0 1 none) 0 1 none,?_⟩
  have eqn : 3*(st src).length+3+(3*(transferStacks src 1 st 1).length+3) = 6*(st src).length+6 := by
    simp [transferStacks,ht]; omega
  rw [eqn] at h
  exact h

private def peek : Code := .base (.atom (.peek 5 0 1))
private abbrev peekR (r : regs) (w : List Bool) := readRegs r 0 1 w.head?
private theorem peek_eval (r : regs) (st : Stk) :
    Eval peek 1 ⟨r,st⟩ ⟨peekR r (st 5),st⟩ :=
  .base (.atom _ _)

private def body : Code := .seq (.call BitEuclidDivision.divide)
  (.seq (ArithmeticExpressionSupport.clearCmd 7)
    (.seq (move 5 6) (.seq (move 0 5) peek)))
def code : Code := .seq peek (.while 1 body)

private abbrev store (d x : ℕ) : Stk := quotientStacks [] d.bits x.bits []

private theorem guard (r : regs) (d : ℕ) :
    peekR r d.bits 1 = decide (d ≠ 0) := by
  simp only [peekR,readRegs,Function.update_self]
  cases hw : d.bits with
  | nil =>
    have h : d = 0 := Nat.size_eq_zero.mp (by rw [← Nat.size_eq_bits_len,hw]; rfl)
    simp [h]
  | cons b bs =>
    have h : d ≠ 0 := fun e => by simp [e] at hw
    simp [h]

private theorem body_eval (r : regs) (d x M : ℕ) (hp : 0 < d)
    (hd : d ≤ M) (hx : x ≤ M) :
    ∃ n rf, n ≤ 600*(M.size+1)^2 ∧
      Eval body n ⟨r,store d x⟩ ⟨rf,store (x%d) d⟩ ∧ rf 1 = decide (x%d ≠ 0) := by
  have hp' : 0 < BinaryArithmetic.toNat d.bits := by rwa [nat_bits]
  obtain ⟨r₁,n,hn,ht⟩ := BitEuclidDivision.divide_correct r d.bits x.bits hp'
  simp only [nat_bits] at ht
  let a := (x%d).bits
  let b := (x/d).bits
  have e₁ : Eval (.call BitEuclidDivision.divide) n ⟨r,store d x⟩ ⟨r₁,quotientStacks a d.bits [] b⟩ := .call _ ht
  have e₂ := ArithmeticExpressionSupport.clear_eval 7 (⟨r₁,quotientStacks a d.bits [] b⟩ : Data)
  have eq₂ : Function.update (quotientStacks a d.bits [] b) 7 [] = quotientStacks a d.bits [] [] := by
    funext i; fin_cases i <;> rfl
  rw [eq₂] at e₂
  obtain ⟨r₃,e₃⟩ := move_eval 5 6 (by decide) (by decide) (by decide)
    (readRegs r₁ 0 1 none) (quotientStacks a d.bits [] []) rfl rfl
  have eq₃ : Function.update (Function.update (quotientStacks a d.bits [] []) 5 []) 6 d.bits =
      quotientStacks a [] d.bits [] := by funext i; fin_cases i <;> rfl
  change Eval _ (6*d.bits.length+6) _ ⟨r₃,Function.update (Function.update _ 5 []) 6 d.bits⟩ at e₃
  rw [eq₃] at e₃
  obtain ⟨r₄,e₄⟩ := move_eval 0 5 (by decide) (by decide) (by decide) r₃ (quotientStacks a [] d.bits []) rfl rfl
  have eq₄ : Function.update (Function.update (quotientStacks a [] d.bits []) 0 []) 5 a =
      store (x%d) d := by funext i; fin_cases i <;> rfl
  change Eval _ (6*a.length+6) _ ⟨r₄,Function.update (Function.update _ 0 []) 5 a⟩ at e₄
  rw [eq₄] at e₄
  have ht := Eval.seq e₁ (Eval.seq e₂ (Eval.seq e₃ (Eval.seq e₄ (peek_eval r₄ (store (x%d) d)))))
  refine ⟨_,_,?_,ht,guard _ _⟩
  change n+(2*b.length+3+(6*d.bits.length+6+(6*a.length+6+1))) ≤ _
  dsimp only [a,b]
  simp only [Nat.size_eq_bits_len] at hn ⊢
  have hd' := Nat.size_le_size hd
  have hx' := Nat.size_le_size hx
  have hr := Nat.size_le_size ((Nat.mod_le x d).trans hx)
  have hq := Nat.size_le_size ((Nat.div_le_self x d).trans hx)
  have hsq := Nat.pow_le_pow_left (show d.size+x.size+1 ≤ 2*(M.size+1) by omega) 2
  nlinarith only [hn,hsq,hr,hq,hd',hx',Nat.zero_le (M.size^2),Nat.zero_le M.size]

open BoundedExtendedEuclid in
private theorem run_zero (k : ℕ) (s : BoundedExtendedEuclid.State) (hz : s.r=0) : run k s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [run,BoundedExtendedEuclid.step,hz] using ih

open BoundedExtendedEuclid in
private theorem loop_eval (k M : ℕ) (s : BoundedExtendedEuclid.State)
    (r : regs) (hr : s.r ≤ M) (hx : s.oldR ≤ M) (hg : r 1 = decide (s.r ≠ 0))
    (hstop : (run k s).r = 0) :
    ∃ n rf, n ≤ k*(600*(M.size+1)^2+1)+1 ∧
      Eval (.while 1 body) n ⟨r,store s.r s.oldR⟩ ⟨rf,store 0 (run k s).oldR⟩ := by
  by_cases hz : s.r = 0
  · refine ⟨1,r,by omega,?_⟩
    rw [run_zero k s hz, hz]
    exact .while_false (by simpa [hz] using hg)
  induction k generalizing s r with
  | zero => exact False.elim (hz hstop)
  | succ k ih =>
    obtain ⟨n₁,r₁,hn₁,he₁,hg₁⟩ := body_eval r s.r s.oldR M (Nat.pos_of_ne_zero hz) hr hx
    have hs : (step s).r = s.oldR%s.r := by simp [BoundedExtendedEuclid.step,hz]
    have ho : (step s).oldR = s.r := by simp [BoundedExtendedEuclid.step,hz]
    have hrem := (Nat.mod_le s.oldR s.r).trans hx
    have hnext : ∃ n rf, n ≤ k*(600*(M.size+1)^2+1)+1 ∧
        Eval (.while 1 body) n ⟨r₁,store (step s).r (step s).oldR⟩
          ⟨rf,store 0 (run k (step s)).oldR⟩ := by
      by_cases hnew : (step s).r = 0
      · refine ⟨1,r₁,by omega,?_⟩
        rw [run_zero k _ hnew,hnew]
        exact .while_false (by simpa [← hs,hnew] using hg₁)
      · exact ih (step s) r₁ (hs ▸ hrem) (ho ▸ hr) (hs ▸ hg₁) hstop hnew
    obtain ⟨n₂,rf,hn₂,he₂⟩ := hnext
    rw [hs,ho] at he₂
    refine ⟨_,rf,?_,.while_true (by simpa [hz] using hg) he₁ he₂⟩
    rw [Nat.succ_mul]; omega

/-- Fixed eight-stack GCD table, including the zero case. Every division returns
canonical words before the next guard is tested. -/
def program := compiled code 5 6

theorem gcd_trace (r : regs) (d x : ℕ) :
    ∃ rf, RunsIn program (2*(bitLen (max d x)+1)*(600*((max d x).size+1)^2+1)+3)
      ⟨some program.entry,r,store d x⟩ ⟨none,rf,store 0 (d.gcd x)⟩ := by
  let M := max d x
  let k := 2*(bitLen M+1)
  obtain ⟨hz,hg,-⟩ := BoundedExtendedEuclid.costed_xgcd d x (le_max_left d x) (le_max_right d x)
  have h := loop_eval k M (BoundedExtendedEuclid.init d x) (peekR r d.bits)
    (le_max_left d x) (le_max_right d x) (guard r d) hz
  obtain ⟨n,rf,hn,he⟩ := h
  rw [hg] at he
  have hfull := compiled_halt_trace (Eval.seq (peek_eval r (store d x)) he) 5 6
  refine ⟨rf,_,?_,hfull⟩
  dsimp [k,M] at hn
  omega
end DetDLP.BitEuclidLoop
end

section

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

section
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

section
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

section

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

section

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

section

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

section

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

section

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

section

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

section

namespace DetDLP.CosetTapeBounds

open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem frame_length (xs : List Bool) : (Encoding.frame xs).length = 2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x l ih => change (Encoding.frame l).length+1+1 = _; rw [ih]; simp; omega

theorem list_length {α : Type*} (f : α → List Bool) (xs : List α) :
    (Encoding.encodeList f xs).length = 1+(xs.map (fun x => 2*(f x).length+2)).sum := by
  induction xs with
  | nil => rfl
  | cons x l ih => simp [Encoding.encodeList,frame_length,ih]; omega

private theorem list_bound {α : Type*} (f : α → List Bool) (xs : List α) (d : ℕ)
    (h : ∀ x ∈ xs,(f x).length ≤ d) :
    (Encoding.encodeList f xs).length ≤ 1+xs.length*(2*d+2) := by
  induction xs with
  | nil => simp [Encoding.encodeList]
  | cons x l ih =>
    have hi := ih (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    change ((Encoding.frame (f x) ++ Encoding.encodeList f l).length+1) ≤ _
    rw [List.length_append,frame_length]
    calc
      _ ≤ (2*d+1)+(1+l.length*(2*d+2))+1 := by omega
      _ = _ := by simp only [List.length_cons]; ring

theorem count_bound (m k : ℕ) (hk : k ≤ m) : (countWord k).length ≤ bitLen m+1 := by
  rw [countWord]; split
  · simp
  · rw [Nat.size_eq_bits_len,Nat.size_le,bitLen,pow_succ]
    have := Nat.le_pow_clog (b := 2) (by decide) m
    have hp : 0 < 2^Nat.clog 2 m := by positivity
    omega

private theorem count_dim (n : ℕ) : (countWord n).length ≤ n+1 := by
  rw [countWord]; split
  · simp
  · rw [Nat.size_eq_bits_len,Nat.size_le]
    have h (k : ℕ) : k < 2^(k+1) := by
      induction k with
      | zero => decide
      | succ k ih => rw [pow_succ]; omega
    exact h n

theorem rep_bound {n m : ℕ} (x : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ)
    (hx : ∀ i,x i ≤ m) (hB : ∀ i j, |B i j| ≤ (m:ℤ)) :
    (encodeCosetRep x B).length ≤ 9+2*(n*(2*(bitLen m+1)+2))+2*((n*n)*(2*(bitLen m+2)+2)) := by
  let vs := List.ofFn x
  let bs := (List.finRange n).flatMap fun i => (List.finRange n).map fun j => B i j
  have hv : (encodeNatListBin vs).length ≤ 1+n*(2*(bitLen m+1)+2) := by
    refine (list_bound countWord vs (bitLen m+1) ?_).trans_eq ?_
    · intro v hv; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv; exact count_bound _ _ (hx i)
    · simp [vs]
  have hb : (Encoding.encodeList encodeIntBin bs).length ≤ 1+n*n*(2*(bitLen m+2)+2) := by
    refine (list_bound encodeIntBin bs (bitLen m+2) ?_).trans_eq ?_
    · intro z hz
      obtain ⟨i,_,hz⟩ := List.mem_flatMap.mp hz
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hz
      change (countWord (B i j).natAbs).length+1 ≤ _
      have ha : (B i j).natAbs ≤ m := by rw [← Nat.cast_le (α := ℤ),Int.natCast_natAbs]; exact hB i j
      have := count_bound m _ ha; omega
    · simp [bs,List.length_flatMap,Fin.sum_univ_def]
  change (Encoding.encodeList id [encodeNatListBin vs,Encoding.encodeList encodeIntBin bs]).length ≤ _
  rw [list_length]; simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,id_eq]; omega

/-- Bit length of the actual framed word on the input tape. -/
theorem input_bound {n m : ℕ} (x a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (c : ℕ)
    (hx : ∀ i,x i ≤ m) (ha : ∀ i,a i ≤ m) (hc : c ≤ m) (hB : ∀ i j, |B i j| ≤ (m:ℤ)) :
    (encodeCosetUpdateInput m x B a c).length ≤ 100*(n+bitLen m+2)^3 := by
  have hrep := rep_bound x B hx hB
  have hm := count_bound m m le_rfl
  have hn := count_dim n
  have hcw := count_bound m c hc
  have hw : (encodeNatListBin (List.ofFn a)).length ≤ 1+n*(2*(bitLen m+1)+2) := by
    refine (list_bound countWord (List.ofFn a) (bitLen m+1) ?_).trans_eq ?_
    · intro z hz; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz; exact count_bound _ _ (ha i)
    · simp
  unfold encodeCosetUpdateInput; rw [list_length]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,id_eq]
  nlinarith only [hrep,hm,hn,hcw,hw,Nat.zero_le (n^3),Nat.zero_le ((bitLen m)^3),
    Nat.zero_le (n^2*bitLen m),Nat.zero_le (n*(bitLen m)^2),Nat.zero_le (n*bitLen m),
    Nat.zero_le (n^2),Nat.zero_le ((bitLen m)^2),Nat.zero_le n,Nat.zero_le (bitLen m)]

end DetDLP.CosetTapeBounds
end

section

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

theorem parses_eval {n L} {ps : List (Pop n)} {v w : Vars n} (h : Parses L ps v w)
    (hv : ∀ j,v j ≤ 2^(L+1)) (r : Regs) :
    ∃ t rf,t ≤ ps.length * (SerializedFieldCall.cost*(L+4)*((2^(L+1)).size+2)^2) ∧
      Eval (sequence ps) t ⟨r,frame (merge clean v)⟩ ⟨rf,frame (merge clean w)⟩ := by
  induction h generalizing r with
  | nil v => exact ⟨0,r,by simp,.base (.skip _)⟩
  | @cons p ps v w x tail he hx ht next ih =>
    let N := 2^(L+1)
    have wb (s : List Bool) (hs : s.length ≤ L) : word s ≤ N :=
      (word_bound s).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
    have hp : 2^x.length ≤ N := Nat.pow_le_pow_right (by decide) (by omega)
    obtain ⟨a,ra,ha,ea⟩ := SerializedFieldCall.eval v p.src p.raw p.field x tail he N
      (by dsimp [N]; rw [pow_succ]; have := Nat.two_pow_pos L; omega) hv hp (wb _ ht) r
    have hh : ∀ j,SerializedFieldCall.result v p.src p.raw p.field x tail j ≤ N := by
      intro j
      simp only [SerializedFieldCall.result,Function.update_apply]
      split_ifs <;> first | apply wb; assumption | exact (BitWordFrames.value_lt x).le.trans hp | exact hv _
    obtain ⟨b,rb,hb,eb⟩ := ih hh ra
    refine ⟨a+b,rb,?_,.seq ea eb⟩
    have hcost := Nat.mul_le_mul_right ((N.size+2)^2)
      (Nat.mul_le_mul_left SerializedFieldCall.cost (show x.length+4 ≤ L+4 by omega))
    rw [List.length_cons,Nat.succ_mul]
    have ha' := ha.trans hcost
    dsimp only [N] at ha'
    omega

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

theorem decode {n} (m : ℕ) (x a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (c : ℕ) :
    let input := encodeCosetUpdateInput m x B a c
    let start : Vars 11 := ![word input,0,0,0,0,0,0,0,0,0,0]
    Parses input.length pops start (fields m x a B c) := by
  intro input start
  let X := encodeNatListBin (List.ofFn x)
  let A := encodeNatListBin (List.ofFn a)
  let F := Encoding.encodeList encodeIntBin ((List.finRange n).flatMap fun i =>
    (List.finRange n).map fun j => B i j)
  let rep := Encoding.encodeList id [X,F]
  let es := Encoding.encodeList (α:=List Bool) id
  have all : (es [countWord m,countWord n,rep,A,countWord c]).length ≤ input.length := le_rfl
  have lim {b : List Bool} {ls : List (List Bool)} (h : (es (b::ls)).length ≤ input.length) :
      b.length ≤ input.length ∧ (es ls).length ≤ input.length :=
    ⟨(head_length b _).trans h,(tail_length b _).trans h⟩
  obtain ⟨hm,tail₁⟩ := lim all
  obtain ⟨hn,tail₂⟩ := lim tail₁
  obtain ⟨hr,tail₃⟩ := lim tail₂
  obtain ⟨ha,tail₄⟩ := lim tail₃
  obtain ⟨hc,tail₅⟩ := lim tail₄
  obtain ⟨hX,tail₆⟩ := lim (b:=X) (ls:=[F]) hr
  obtain ⟨hF,tail₇⟩ := lim tail₆
  refine .cons (countWord m) _ rfl hm tail₁ (.cons (countWord n) _ rfl hn tail₂
    (.cons rep _ rfl hr tail₃ (.cons A _ rfl ha tail₄ (.cons (countWord c) _ rfl hc tail₅
      (.cons X _ rfl hX tail₆ (.cons F _ rfl hF tail₇ ?_))))))
  convert Parses.nil _ using 1
  funext j; fin_cases j <;> simp [SerializedFieldCall.result,fields,BitWordFrames.value_count,X,F,A,start,es,Encoding.encodeList]

end DetDLP.BinaryUpdateFields
end

section
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
theorem decode (desc : List Bool) (G : BipartiteMultigraph) (β P ell : ℕ) :
    let xs := encodeBTNInstance desc G β P ell
    Parses xs.length pops (start xs) (fields desc G β P ell) := by
  intro xs
  let es := Encoding.encodeList (α:=List Bool) id
  have lim {b : List Bool} {ls : List (List Bool)} (h : (es (b::ls)).length≤xs.length) :
      b.length≤xs.length ∧ (es ls).length≤xs.length :=
    ⟨(BinaryUpdateFields.head_length b _).trans h,(BinaryUpdateFields.tail_length b _).trans h⟩
  have all : (es [desc,G.encode,countWord β,countWord P,countWord ell]).length≤xs.length := le_rfl
  obtain ⟨hd,t₁⟩ := lim all
  obtain ⟨hg,t₂⟩ := lim t₁
  obtain ⟨hb,t₃⟩ := lim t₂
  obtain ⟨hp,t₄⟩ := lim t₃
  obtain ⟨hl,t₅⟩ := lim t₄
  obtain ⟨hv,t₆⟩ := lim (b:=countWord G.nV) (ls:=[countWord G.nE,List.ofFn G.side,ends G]) hg
  obtain ⟨he,t₇⟩ := lim t₆
  obtain ⟨hs,t₈⟩ := lim t₇
  obtain ⟨ha,t₉⟩ := lim t₈
  refine .cons desc _ rfl hd t₁ (.cons G.encode _ rfl hg t₂ (.cons (countWord β) _ rfl hb t₃
    (.cons (countWord P) _ rfl hp t₄ (.cons (countWord ell) _ rfl hl t₅
      (.cons (countWord G.nV) _ rfl hv t₆ (.cons (countWord G.nE) _ rfl he t₇
        (.cons (List.ofFn G.side) _ rfl hs t₈ (.cons (ends G) _ rfl ha t₉ ?_))))))))
  convert Parses.nil _ using 1
  funext i; fin_cases i <;> simp [fields,start,SerializedFieldCall.result,BitWordFrames.value_count,es,Encoding.encodeList]

def program := StructuredCalls.compiled (BinaryUpdateFields.sequence pops) (port (10:Fin 23)) (port (19:Fin 23))
theorem run (desc : List Bool) (G : BipartiteMultigraph) (β P ell : ℕ) (reg : Fin 8→Bool) :
    let xs := encodeBTNInstance desc G β P ell
    let a := frame (SerializedFieldCall.merge SerializedFieldCall.clean (start xs))
    let b := frame (SerializedFieldCall.merge SerializedFieldCall.clean (fields desc G β P ell))
    ∃ t rf,t≤9*(SerializedFieldCall.cost*(xs.length+4)*(xs.length+4)^2)+1 ∧
      Trace program t ⟨some program.entry,reg,a⟩ ⟨none,rf,b⟩ := by
  intro xs a b
  obtain ⟨t,rf,cost,eval⟩ := BinaryUpdateFields.parses_eval (decode desc G β P ell) (r:=reg) (by
    intro i; fin_cases i <;> simp only [start,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.cons_val_fin_one] <;>
      first | exact (BinaryUpdateFields.word_bound xs).le | exact Nat.zero_le _)
  refine ⟨t+1,rf,?_,StructuredCalls.compiled_halt_trace eval _ _⟩
  change t≤9*(SerializedFieldCall.cost*(xs.length+4)*((2^(xs.length+1)).size+2)^2) at cost
  simpa only [Nat.size_pow,Nat.add_assoc] using Nat.add_le_add_right cost 1
end DetDLP.ContractionInputFields
end

section
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

/-- A block is a complete callback trace. Only its maximum stack length is charged across calls. -/
theorem run {S : Type} (cost : S → ℕ) (next : S → S) (R : S → Fin r → Bool) (V : S → Fin s → List Bool)
    (W : ℕ) (s0 : S) (n : ℕ)
    (terminal : R (next^[n] s0) flag=false)
    (stored : ∀ j,j≤n → ∀ i,(V (next^[j] s0) i).length≤W)
    (blocks : ∀ j,j<n → let z := next^[j] s0
      R z flag=true ∧ SafeTrace (step p) (cap W) (cost z)
        ⟨some p.entry,R z,V z⟩ ⟨none,R (next z),V (next z)⟩) :
    let P := loop p flag
    let total := 2+n+∑ j∈Finset.range n,cost (next^[j] s0)
    SafeTrace (step P) (cap W) total ⟨some P.entry,R s0,V s0⟩ ⟨none,R (next^[n] s0),V (next^[n] s0)⟩ := by
  intro P total
  induction n generalizing s0 with
  | zero =>
    have endbit : R s0 flag=false := terminal
    have space := stored 0 (by omega)
    let z : Cfg r s (2+l) := ⟨some head,R s0,V s0⟩
    have go := test p flag z rfl
    simp only [z,endbit,cond_false] at go
    exact .cons space go (.cons space (halt p flag _ rfl) (.refl _ space))
  | succ n ih =>
    have start := blocks 0 (by omega)
    change R s0 flag=true ∧ _ at start
    have st := stored 0 (by omega)
    let z : Cfg r s (2+l) := ⟨some head,R s0,V s0⟩
    have go := test p flag z rfl
    simp only [z,start.1,cond_true] at go
    have consume := SafeTrace.cons (show cap W z from st) go (block p flag start.2)
    have rest := ih (next s0) (by simpa only [Function.iterate_succ_apply] using terminal)
      (fun j hj => by simpa only [Function.iterate_succ_apply] using stored (j+1) (by omega))
      (fun j hj => by simpa only [Function.iterate_succ_apply] using blocks (j+1) (by omega))
    have both := consume.trans rest
    change SafeTrace _ _ ((cost s0+1)+(2+n+∑ j∈Finset.range n,cost (next^[j] (next s0)))) _ _ at both
    simpa only [z,P,total,loop,Finset.sum_range_succ',Function.iterate_succ_apply,Function.iterate_zero_apply,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using both
end DetDLP.BoundedProgramLoop
end

section
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

section

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

theorem initial_grows {r s l : ℕ} {p : BitProgram.Program r s l} {b : BitProgram.Cfg r s l}
    {k : ℕ} {input : List Bool} (h : BitProgram.Trace p k (BitProgram.initial p input) b) (i : Fin s) :
    (b.stacks i).length ≤ input.length+k := by
  apply (trace_grows h i).trans
  simp [BitProgram.initial]; split_ifs <;> simp

theorem absorb_cost (s k u t I : ℕ) (hu : 1 ≤ u)
    (ht : t ≤ (u+2)^k) (hI : I ≤ 100*(u+2)^3) :
    let K := (s+1)*(2*k+300)
    7*t ≤ K*(u+1)^K ∧ s*(I+t+I+15) ≤ K*(u+1)^K := by
  intro K
  have hk : 2*k ≤ K := by dsimp [K]; nlinarith only [Nat.zero_le (s*k),Nat.zero_le s]
  have hc : 6 ≤ K := by dsimp [K]; nlinarith only [Nat.zero_le (s*k),Nat.zero_le s,Nat.zero_le k]
  have hb : u+2 ≤ (u+1)^2 := by nlinarith only [hu,Nat.zero_le (u^2)]
  have comp (j : ℕ) (hj : 2*j ≤ K) : (u+2)^j ≤ (u+1)^K := by
    calc
      _ ≤ ((u+1)^2)^j := Nat.pow_le_pow_left hb _
      _ = (u+1)^(2*j) := (pow_mul ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hj
  let X := (u+1)^K
  have hT : t ≤ X := ht.trans (comp k hk)
  have hIn : I ≤ 100*X := hI.trans (Nat.mul_le_mul_left _ (comp 3 hc))
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have hk7 : 7 ≤ K := by dsimp [K]; nlinarith only [Nat.zero_le (s*k),Nat.zero_le s,Nat.zero_le k]
  have hsc : s*216 ≤ K := by dsimp [K]; nlinarith only [Nat.zero_le (s*k),Nat.zero_le s,Nat.zero_le k]
  refine ⟨Nat.mul_le_mul hk7 hT,?_⟩
  calc
    s*(I+t+I+15) ≤ s*(216*X) := Nat.mul_le_mul_left _ (by omega)
    _ = (s*216)*X := by ring
    _ ≤ K*X := Nat.mul_le_mul_right _ hsc

end DetDLP.BitTracePolynomial
end

section
namespace DetDLP.RawContractionInput
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitRegisterBank BitRegisterCode BitArithmeticUnit ContractionInputFields
abbrev Cmd₀ := StructuredCalls.Cmd 8 31
def zeroBit (i : Fin 31) : Cmd₀ := (.base (.atom (.set 2 false)) : Cmd₀).seq (.base (.atom (.push i 2)))
theorem zero_eval (i : Fin 31) (r : Regs) (s : Fin 31→List Bool) :
    Eval (zeroBit i) 2 ⟨r,s⟩ ⟨Function.update r 2 false,Function.update s i (false::s i)⟩ := by
  apply Eval.seq (n:=1) (m:=1) (.base (.atom _ _))
  simpa only [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,StructuredProgram.State.withPC,
    StructuredProgram.State.ofCfg,execInstr,Function.update_self] using
    (Eval.base (StructuredProgram.Eval.atom (.push i 2) ⟨Function.update r 2 false,s⟩))
def boot : Cmd₀ := (BitWordBridge.encode 18 0).seq ((BitWordBridge.mark 10).seq
  ((BitWordBridge.mark 16).seq ((BitWordBridge.mark 17).seq (zeroBit 17))))
def machine := compiled (boot.seq (BinaryUpdateFields.sequence ContractionInputFields.pops)) (18:Fin 31) (27:Fin 31)
def raw (xs : List Bool) (j : Fin 31) := if j=18 then xs else []
set_option maxRecDepth 6000 in
theorem boot_eval (xs : List Bool) (r : Regs) :
    ∃ rf,Eval boot (6*xs.length+16) ⟨r,raw xs⟩
       ⟨rf,frame (SerializedFieldCall.merge SerializedFieldCall.clean (ContractionInputFields.start xs))⟩ := by
  obtain ⟨rr,e⟩ := BitWordBridge.encode_eval (18:Fin 31) 0 (by decide) r (raw xs) rfl
  let s₁ := Function.update (raw xs) (18:Fin 31) (BitWordFrames.word xs).bits
  let s₂ := Function.update s₁ 10 [true]
  let s₃ := Function.update s₂ 16 [true]
  let s₄ := Function.update s₃ 17 [true]
  have f := BitWordBridge.mark_eval (10:Fin 31) rr s₁
  have g := BitWordBridge.mark_eval (16:Fin 31) (Function.update rr 2 true) s₂
  let rr' := Function.update (Function.update rr 2 true) 2 true
  have h := BitWordBridge.mark_eval (17:Fin 31) rr' s₃
  have q := zero_eval 17 (Function.update rr' 2 true) s₄
  change Eval _ (6*xs.length+8) _ ⟨rr,s₁⟩ at e
  change Eval _ 2 _ ⟨_,s₂⟩ at f
  change Eval _ 2 _ ⟨rr',s₃⟩ at g
  change Eval _ 2 _ ⟨_,s₄⟩ at h
  have endEq : Function.update s₄ 17 [false,true] =
      frame (SerializedFieldCall.merge SerializedFieldCall.clean (ContractionInputFields.start xs)) := by
    funext j; fin_cases j <;> first | rfl | exact (by decide : [true]=(1:ℕ).bits) | skip
    change Function.update s₄ 17 [false,true] (17:Fin 31)=_
    rw [Function.update_self]
    change [false,true]=frame (SerializedFieldCall.merge SerializedFieldCall.clean (ContractionInputFields.start xs)) (port (SerializedFieldCall.low (9:Fin 10)))
    simp only [frame,store_port,SerializedFieldCall.get_low]
    exact (by decide : [false,true]=(2:ℕ).bits)
  change Eval _ 2 _ ⟨_,Function.update s₄ 17 [false,true]⟩ at q
  rw [endEq] at q
  have tr := Eval.seq e (.seq f (.seq g (.seq h q)))
  exact ⟨_,tr⟩
theorem run (desc : List Bool) (G : BipartiteMultigraph) (β P ell : ℕ) :
    let xs := encodeBTNInstance desc G β P ell
    let out := frame (SerializedFieldCall.merge SerializedFieldCall.clean (fields desc G β P ell))
    ∃ t rf,t≤6*xs.length+17+9*(SerializedFieldCall.cost*(xs.length+4)*(xs.length+4)^2) ∧
      Trace machine t (initial machine xs) ⟨none,rf,out⟩ ∧
      ∀ j c,j≤t → Trace machine j (initial machine xs) c → ∀ i,(c.stacks i).length≤xs.length+t := by
  intro xs out
  obtain ⟨r,b⟩ := boot_eval xs (fun _ => false)
  obtain ⟨u,rf,cost,e⟩ := BinaryUpdateFields.parses_eval (decode desc G β P ell) (r:=r) (by
    intro i; fin_cases i <;> simp only [ContractionInputFields.start,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.cons_val_fin_one] <;>
      first | exact (BinaryUpdateFields.word_bound xs).le | exact Nat.zero_le _)
  have tr := compiled_halt_trace (Eval.seq b e) (18:Fin 31) (27:Fin 31)
  refine ⟨_,rf,?_,tr,?_⟩
  · change u≤9*(SerializedFieldCall.cost*(xs.length+4)*((2^(xs.length+1)).size+2)^2) at cost
    simp only [Nat.size_pow,Nat.add_assoc] at cost
    change u≤9*(SerializedFieldCall.cost*(xs.length+4)*(xs.length+4)^2) at cost; omega
  · intro j c hj hp i
    have z := BitTracePolynomial.trace_grows hp i
    have h : ((initial machine xs).stacks i).length≤xs.length := by
      change (if i=machine.inputStack then xs else []).length≤_; split <;> simp
    exact z.trans (Nat.add_le_add h hj)
end DetDLP.RawContractionInput
end

section
namespace DetDLP.EntryQueryBuilder
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls SqrtLogSpace
open BitArithmeticUnit
def cfg (desc vertex bits tmp result : List Bool) : Fin 5→List Bool := ![desc,vertex,bits,tmp,result]
def setup : Cmd 8 5 := (.base (.atom (.set 2 false)) : Cmd 8 5).seq (.base (.atom (.push 4 2)))
def cmd : Cmd 8 5 := setup.seq ((RecoveryFrame.field 2 3 4).seq
  ((RecoveryFrame.field 1 3 4).seq ((RecoveryFrame.field 0 3 4).seq (.base (.atom (.pop 4 0 1))))))
theorem init (desc vert bits : List Bool) (r : Regs) :
    Eval setup 2 ⟨r,cfg desc vert bits [] []⟩ ⟨Function.update r 2 false,cfg desc vert bits [] [false]⟩ := by
  let s := cfg desc vert bits [] []
  have eq : Function.update s (4:Fin 5) [false]=cfg desc vert bits [] [false] := by
    funext j; fin_cases j <;> rfl
  rw [←eq]; apply Eval.seq (n:=1) (m:=1) (.base (.atom _ _))
  simpa only [StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,StructuredProgram.State.withPC,StructuredProgram.State.ofCfg,
    execInstr,Function.update_self,show s 4=[] from rfl] using
    (Eval.base (StructuredProgram.Eval.atom (.push 4 2) ⟨Function.update r 2 false,s⟩))
private theorem push2 (a b x y : List Bool) : Function.update (Function.update (cfg a b x [] y) (2:Fin 5) []) 4
    (true::(Encoding.frame x++y))=cfg a b [] [] (true::(Encoding.frame x++y)) := by funext i; fin_cases i <;> rfl
private theorem push1 (a b y : List Bool) : Function.update (Function.update (cfg a b [] [] y) (1:Fin 5) []) 4
    (true::(Encoding.frame b++y))=cfg a [] [] [] (true::(Encoding.frame b++y)) := by funext i; fin_cases i <;> rfl
private theorem push0 (a y : List Bool) : Function.update (Function.update (cfg a [] [] [] y) (0:Fin 5) []) 4
    (true::(Encoding.frame a++y))=cfg [] [] [] [] (true::(Encoding.frame a++y)) := by funext i; fin_cases i <;> rfl
theorem run (desc : List Bool) (v : ℕ) (bits : List Bool) (r : Regs) :
    let q := (encodePortQuery desc v bits).tail
    ∃ rf,Eval cmd (7*(desc.length+(countWord v).length+bits.length)+36) ⟨r,cfg desc (countWord v) bits [] []⟩
      ⟨rf,cfg [] [] [] [] q⟩ := by
  intro q
  let vert := countWord v
  let tail₂ := true::(Encoding.frame bits++[false])
  let tail₁ := true::(Encoding.frame vert++tail₂)
  let tail₀ := true::(Encoding.frame desc++tail₁)
  obtain ⟨r₂,e₂⟩ := RecoveryFrame.field_eval (2:Fin 5) 3 4 (by decide) (by decide) (by decide)
    (Function.update r 2 false) (cfg desc vert bits [] [false]) rfl
  change Eval _ (7*bits.length+11) _ ⟨_,Function.update (Function.update (cfg desc vert bits [] [false]) 2 []) 4 tail₂⟩ at e₂
  rw [push2] at e₂
  obtain ⟨r₁,e₁⟩ := RecoveryFrame.field_eval (1:Fin 5) 3 4 (by decide) (by decide) (by decide) r₂ (cfg desc vert [] [] tail₂) rfl
  change Eval _ (7*vert.length+11) _ ⟨_,Function.update (Function.update (cfg desc vert [] [] tail₂) 1 []) 4 tail₁⟩ at e₁
  rw [push1] at e₁
  obtain ⟨r₀,e₀⟩ := RecoveryFrame.field_eval (0:Fin 5) 3 4 (by decide) (by decide) (by decide) r₁ (cfg desc [] [] [] tail₁) rfl
  change Eval _ (7*desc.length+11) _ ⟨_,Function.update (Function.update (cfg desc [] [] [] tail₁) 0 []) 4 tail₀⟩ at e₀
  rw [push0] at e₀
  have pop := BitWordBridge.pop_eval (4:Fin 5) r₀ (cfg [] [] [] [] tail₀) (xs:=q) rfl
  have endeq : Function.update (cfg [] [] [] [] tail₀) (4:Fin 5) q=cfg [] [] [] [] q := by funext i; fin_cases i <;> rfl
  rw [endeq] at pop
  have all := Eval.seq (init desc vert bits r) (.seq e₂ (.seq e₁ (.seq e₀ pop)))
  refine ⟨readRegs r₀ 0 1 (some true),?_⟩
  rw [show 7*(desc.length+(countWord v).length+bits.length)+36=2+(7*bits.length+11+(7*vert.length+11+(7*desc.length+11+1))) by dsimp only [vert]; omega]
  exact all
end DetDLP.EntryQueryBuilder
end

section
namespace DetDLP.QueryPresence
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls StackRoutines
open BitArithmeticUnit
variable {n : ℕ} (v t p : Fin n)
abbrev C := StructuredCalls.Cmd 8 n
abbrev Stk := Fin n→List Bool
def pop : C (n:=n) := .base (.atom (.pop v 0 1))
def push (i : Fin n) (r : Fin 8) : C (n:=n) := .base (.atom (.push i r))
def body := (push t 0).seq ((push p 1).seq (pop v))
def cmd := (pop v).seq ((Cmd.while 1 (body v t p)).seq (BitWordBridge.transfer t v))
private theorem pop0 (r : Regs) (s : Stk (n:=n)) : Eval (pop v) 1 ⟨r,s⟩
    ⟨readRegs r 0 1 (s v).head?,Function.update s v (s v).tail⟩ := .base (.atom _ _)
private theorem push0 (i : Fin n) (j : Fin 8) (r : Regs) (s : Stk (n:=n)) :
    Eval (push i j) 1 ⟨r,s⟩ ⟨r,Function.update s i (r j::s i)⟩ := .base (.atom _ _)
private theorem loop_trace (vt : v≠t) (vp : v≠p) (tp : t≠p) (xs : List Bool) (r : Regs) (s : Stk (n:=n))
    (hv : s v=xs) :
    ∃ rf,Eval ((pop v).seq (.while 1 (body v t p))) (4*xs.length+2) ⟨r,s⟩
      ⟨rf,Function.update (Function.update (Function.update s v []) t (xs.reverse++s t)) p (List.replicate xs.length true++s p)⟩ := by
  induction xs generalizing s r with
  | nil =>
    have q := pop0 v r s
    rw [hv] at q
    have f : readRegs r (0:Fin 8) 1 none 1=false := by simp [readRegs]
    let st := Function.update s v []
    have stop := Eval.while_false (test:=1) (a:=⟨readRegs r 0 1 none,st⟩) (body:=body v t p) f
    have doneEq : Function.update (Function.update st t (s t)) p (s p)=st := by
      funext i; by_cases ht : i=t <;> by_cases hp : i=p <;> simp_all [st,Function.update_apply]
    simp only [List.reverse_nil,List.nil_append,List.length_nil,List.replicate_zero,Nat.mul_zero,Nat.zero_add]
    rw [doneEq]; exact ⟨_,.seq q stop⟩
  | cons b xs ih =>
    have q := pop0 v r s
    rw [hv] at q
    let r' := readRegs r 0 1 (some b)
    let st := Function.update s v xs
    have yes : r' 1=true := by simp [r',readRegs]
    have b' : r' 0=b := by simp [r',readRegs]
    let s₁ := Function.update st t (b::s t)
    let s₂ := Function.update s₁ p (true::s p)
    have z := push0 t 0 r' st
    have y := push0 p 1 r' s₁
    have t0 : st t=s t := Function.update_of_ne vt.symm ..
    have p0 : s₁ p=s p := by simp [s₁,st,Function.update_of_ne tp.symm,Function.update_of_ne vp.symm]
    rw [b',t0] at z; rw [yes,p0] at y
    have v0 : s₂ v=xs := by simp [s₂,s₁,st,Function.update_of_ne vt,Function.update_of_ne vp]
    obtain ⟨rf,rec'⟩ := ih r' s₂ v0
    generalize eqtime : 4*xs.length+2 = work at rec'
    cases rec' with
    | @seq _ _ n₁ n₂ _ _ _ first later =>
      have done := Eval.seq q (Eval.while_true (test:=1) yes (Eval.seq z (.seq y first)) later)
      let out := Function.update (Function.update (Function.update s₂ v []) t (xs.reverse++s₂ t)) p (List.replicate xs.length true++s₂ p)
      have endEq : out=Function.update (Function.update (Function.update s v []) t ((b::xs).reverse++s t)) p
            (List.replicate (b::xs).length true++s p) := by
        funext i
        by_cases ep : i=p
        · subst i; simp only [out,s₂,Function.update_self,List.length_cons,List.replicate_succ',List.append_assoc,List.singleton_append]
        by_cases et : i=t
        · subst i; simp [out,s₂,s₁,Function.update_of_ne ep,List.reverse_cons,List.append_assoc]
        by_cases ev : i=v
        · subst i; simp [out,Function.update_of_ne ep,Function.update_of_ne et]
        simp [out,s₂,s₁,st,Function.update_of_ne ep,Function.update_of_ne et,Function.update_of_ne ev]
      refine ⟨rf,?_⟩
      rw [←endEq]
      have tm : 4*(b::xs).length+2=1+(1+(1+n₁)+n₂+1) := by simp only [List.length_cons]; omega
      rw [tm]; exact done
theorem run (vt : v≠t) (vp : v≠p) (tp : t≠p) (r : Regs) (s : Stk (n:=n)) (ht : s t=[]) (hp : s p=[]) :
    ∃ rf, Eval (cmd v t p) (7*(s v).length+5) ⟨r,s⟩ ⟨rf,Function.update s p (List.replicate (s v).length true)⟩ := by
  obtain ⟨rr,q⟩ := loop_trace v t p vt vp tp (s v) r s rfl
  simp only [ht,hp,List.append_nil] at q
  let st := Function.update (Function.update (Function.update s v []) t (s v).reverse) p (List.replicate (s v).length true)
  have z := ArrayUpdatePrograms.transfer_eval t v 0 1 vt.symm (by decide : (0:Fin 8)≠1) rr st
  have et : st t=(s v).reverse := by simp [st,Function.update_of_ne tp]
  have ev : st v=[] := by simp [st,Function.update_of_ne vp,Function.update_of_ne vt]
  have eq : transferStacks t v st=Function.update s p (List.replicate (s v).length true) := by
    funext j; by_cases e : j=t <;> by_cases f : j=v <;> by_cases g : j=p <;>
      simp_all [transferStacks,st,Function.update_apply]
  rw [eq,et,List.length_reverse] at z
  generalize eqtime : 4*(s v).length+2 = work at q
  cases q with
  | @seq _ _ n₁ n₂ _ _ _ first later =>
    refine ⟨readRegs rr 0 1 none,?_⟩
    have done := Eval.seq first (Eval.seq later z)
    have tm : 7*(s v).length+5=n₁+(n₂+(3*(s v).length+3)) := by omega
    rw [tm]; exact done
end DetDLP.QueryPresence
end

section
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

section
namespace DetDLP.EntryCallPreparation
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls SqrtLogSpace
open BitArithmeticUnit BoundedProgramLoop EntryQueryBuilder
def program := compiled (EntryQueryBuilder.cmd.seq (QueryPresence.cmd 4 1 0)) (0:Fin 5) 4
def size (desc vert bits : List Bool) := desc.length+vert.length+bits.length
def cost (desc : List Bool) (v : ℕ) (bits : List Bool) := 7*size desc (countWord v) bits+7*(encodePortQuery desc v bits).tail.length+42
theorem run (desc : List Bool) (v : ℕ) (bits : List Bool) (r : Regs) :
    let w := countWord v
    let q := (encodePortQuery desc v bits).tail
    ∃ rf,SafeTrace (step program) (cap (size desc w bits+cost desc v bits)) (cost desc v bits)
      ⟨some program.entry,r,cfg desc w bits [] []⟩ ⟨none,rf,cfg (List.replicate q.length true) [] [] [] q⟩ := by
  intro w q
  obtain ⟨r₁,tr⟩ := EntryQueryBuilder.run desc v bits r
  let st := cfg [] [] [] [] q
  obtain ⟨r₂,end'⟩ := QueryPresence.run (4:Fin 5) 1 0 (by decide) (by decide) (by decide) r₁ st rfl rfl
  have eq : Function.update st (0:Fin 5) (List.replicate q.length true)=cfg (List.replicate q.length true) [] [] [] q := by
    funext i; fin_cases i <;> rfl
  change Eval _ (7*q.length+5) _ ⟨r₂,Function.update st 0 (List.replicate q.length true)⟩ at end'
  rw [eq] at end'
  have combine := compiled_halt_trace (Eval.seq tr end') (0:Fin 5) 4
  have time : 7*(desc.length+w.length+bits.length)+36+(7*q.length+5)+1=cost desc v bits := by
    dsimp only [cost,size,q,w]; omega
  rw [time] at combine
  refine ⟨r₂,SafeTrace.of_trace combine ?_⟩
  intro j c hj pref i
  have base : (cfg desc w bits [] [] i).length ≤ size desc w bits := by
    fin_cases i <;> simp [cfg,size] <;> omega
  exact (BitTracePolynomial.trace_grows pref i).trans (Nat.add_le_add base hj)
end DetDLP.EntryCallPreparation
end

section
namespace DetDLP.QueryOutputZip
open OAI.Algorithms.SubexponentialSAT BitProgram
def machine : Program 2 3 7 where
  inputStack:=0
  outputStack:=2
  entry:=0
  code:=![.pop 0 0 1 1,.branch 1 2 6,.branch 0 3 6,.pop 1 0 1 4,.branch 1 5 6,.push 2 0 0,.halt]
private def cfg (pc : Option (Fin 7)) (r : Fin 2→Bool) (t v a : List Bool) : Cfg 2 3 7 := ⟨pc,r,![t,v,a]⟩
private def empty (r : Fin 2→Bool) := readRegs r 0 1 none
private def reg (r : Fin 2→Bool) (b : Bool) := readRegs r 0 1 (some b)
private theorem popT (r : Fin 2→Bool) (t v a : List Bool) :
    step machine (cfg (some 0) r t v a)=some (cfg (some 1) (readRegs r 0 1 t.head?) t.tail v a) := by
  have eq : Function.update ![t,v,a] (0:Fin 3) t.tail=![t.tail,v,a] := by funext i; fin_cases i <;> rfl
  change some (⟨some 1,readRegs r 0 1 t.head?,Function.update ![t,v,a] 0 t.tail⟩ : Cfg 2 3 7)=some (cfg (some 1) _ t.tail v a); rw [eq] <;> rfl
private theorem popV (r : Fin 2→Bool) (t v a : List Bool) :
    step machine (cfg (some 3) r t v a)=some (cfg (some 4) (readRegs r 0 1 v.head?) t v.tail a) := by
  have eq : Function.update ![t,v,a] (1:Fin 3) v.tail=![t,v.tail,a] := by funext i; fin_cases i <;> rfl
  change some (⟨some 4,readRegs r 0 1 v.head?,Function.update ![t,v,a] 1 v.tail⟩ : Cfg 2 3 7)=some (cfg (some 4) _ t v.tail a); rw [eq] <;> rfl
private theorem push (r : Fin 2→Bool) (t v a : List Bool) (b : Bool) (h : r 0=b) :
    step machine (cfg (some 5) r t v a)=some (cfg (some 0) r t v (b::a)) := by
  have eq : Function.update ![t,v,a] (2:Fin 3) (r 0::a)=![t,v,b::a] := by rw [h]; funext i; fin_cases i <;> rfl
  change some (⟨some 0,r,Function.update ![t,v,a] 2 (r 0::a)⟩ : Cfg 2 3 7)=some (cfg (some 0) r t v (b::a)); rw [eq] <;> rfl
private theorem test (i : Fin 2) (j k : Fin 7) (r : Fin 2→Bool) (t v a : List Bool) (b : Bool)
    (pc : Fin 7) (code : machine.code pc=.branch i j k) (h : r i=b) :
    step machine (cfg (some pc) r t v a)=some (cfg (some (if b then j else k)) r t v a) := by
  simp [step,cfg,code,execInstr,h]
private theorem last (r : Fin 2→Bool) (t v a : List Bool) :
    Trace machine 1 (cfg (some 6) r t v a) (cfg none r t v a) := .cons (by rfl) (.refl _)
def value (t v : List Bool) := (((t.zip v).takeWhile Prod.fst).map Prod.snd)
theorem run (tags vals acc : List Bool) (r₀ : Fin 2→Bool) :
    ∃ t rf ts vs,t ≤ 6*(value tags vals).length+6 ∧ Trace machine t (cfg (some 0) r₀ tags vals acc)
      (cfg none rf ts vs ((value tags vals).reverse++acc)) := by
  induction tags generalizing vals acc r₀ with
  | nil =>
    have q := popT r₀ [] vals acc
    have t := test 1 2 6 (empty r₀) [] vals acc false 1 rfl (by simp [empty,readRegs])
    exact ⟨3,empty r₀,[],vals,by simp [value],.cons q (.cons t (last ..))⟩
  | cons tag tags ih =>
    have q := popT r₀ (tag::tags) vals acc
    let r := reg r₀ tag
    have first := test 1 2 6 r tags vals acc true 1 rfl (by simp [r,reg,readRegs])
    have second := test 0 3 6 r tags vals acc tag 2 rfl (by simp [r,reg,readRegs])
    cases tag with
    | false =>
      refine ⟨4,r,tags,vals,by omega,?_⟩
      have ev : value (false::tags) vals=[] := by cases vals <;> rfl
      rw [ev]; exact .cons q (.cons first (.cons second (last ..)))
    | true =>
      have pop := popV r tags vals acc
      cases vals with
      | nil =>
        have v := test 1 5 6 (empty r) tags [] acc false 4 rfl (by simp [empty,readRegs])
        exact ⟨6,empty r,tags,[],by simp [value],.cons q (.cons first (.cons second (.cons pop (.cons v (last ..)))))⟩
      | cons bit vals =>
        let rf := reg r bit
        have yes := test 1 5 6 rf tags vals acc true 4 rfl (by simp [rf,reg,readRegs])
        have ins := push rf tags vals acc bit (by simp [rf,reg,readRegs])
        obtain ⟨t,fin,ts,vs,ht,tail⟩ := ih vals (bit::acc) rf
        have eq : value (true::tags) (bit::vals)=bit::value tags vals := rfl
        rw [eq,List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
        refine ⟨t+6,fin,ts,vs,by omega,?_⟩
        exact .cons q (.cons first (.cons second (.cons pop (.cons yes (.cons ins tail)))))
end DetDLP.QueryOutputZip
end

section
namespace DetDLP.EntryCallFrame
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BoundedProgramLoop SqrtLogSpace
open BitArithmeticUnit
variable {e : ℕ} (it iv : Fin e)
abbrev Bank (n : ℕ) := Fin n→List Bool
def join (a : Bank e) (b : Bank 3) : Bank (e+3) := Fin.addCases a b
@[simp] theorem low (a : Bank e) (b : Bank 3) (j : Fin e) : join a b (j.castAdd 3)=a j := Fin.addCases_left ..
@[simp] theorem high (a : Bank e) (b : Bank 3) (j : Fin 3) : join a b (Fin.natAdd e j)=b j := Fin.addCases_right ..
abbrev lo (j : Fin e) := j.castAdd 3
abbrev up (j : Fin 3) := Fin.natAdd e j
theorem disjoint (j : Fin e) (k : Fin 3) : lo j≠up (e:=e) k := by
  intro h; have eq := congrArg Fin.val h; change j.val=e+k.val at eq; have := j.isLt; omega
def preports : Fin 5→Fin (e+3) := ![lo it,up 0,up 1,up 2,lo iv]
def zipports : Fin 3→Fin (e+3) := ![lo it,lo iv,up 2]
theorem distinguish (h : it≠iv) : Function.Injective (preports it iv) := by
  have d (k) (l) := disjoint (e:=e) k l
  intro j k hk
  fin_cases j <;> fin_cases k <;> simp_all [preports,lo,up,Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd] <;> omega
theorem distinguishZip (h : it≠iv) : Function.Injective (zipports it iv) := by
  have d (k) (l) := disjoint (e:=e) k l
  intro j k hk
  fin_cases j <;> fin_cases k <;> simp_all [zipports,lo,up,Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd] <;> omega

def source (desc vert bits : List Bool) : Bank (e+3) :=
  join (fun j => if j=it then desc else []) ![vert,bits,[]]
def initQ (w : List Bool) : Bank e :=
  fun j => if j=it then List.replicate w.length true else if j=iv then w else []
def pre := liftProgram EntryCallPreparation.program id (preports it iv)
theorem prepare (h : it≠iv) (desc : List Bool) (v : ℕ) (bits : List Bool) (r : Regs) :
    let w := countWord v
    let q := (encodePortQuery desc v bits).tail
    let cost := EntryCallPreparation.cost desc v bits
    ∃ rf,SafeTrace (step (pre it iv)) (cap (EntryCallPreparation.size desc w bits+cost)) cost
      ⟨some (pre it iv).entry,r,source it desc w bits⟩ ⟨none,rf,join (initQ it iv q) (fun _ => [])⟩ := by
  intro w q cost
  obtain ⟨rf,tr⟩ := EntryCallPreparation.run desc v bits r
  apply CallOnPorts.run _ id (preports it iv) Function.injective_id (distinguish it iv h) _ _ _ _ r rf _ _ _ _ tr
  · intro j; fin_cases j <;> simp [preports,source,EntryQueryBuilder.cfg,lo,up,h.symm,w]
  · intro j; fin_cases j <;> simp [preports,initQ,EntryQueryBuilder.cfg,lo,up,h.symm,q]
  · intro j; refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro outside
      have a : j≠it := fun eq => outside ⟨0,by subst j; rfl⟩
      have b : j≠iv := fun eq => outside ⟨4,by subst j; rfl⟩
      simp [source,initQ,a,b]
    · intro outside; fin_cases j
      · exact False.elim (outside ⟨1,rfl⟩)
      · exact False.elim (outside ⟨2,rfl⟩)
      · exact False.elim (outside ⟨3,rfl⟩)
  · intro j; refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro outside
      have a : j≠it := fun eq => outside ⟨0,by subst j; rfl⟩
      simp [source,a]
    · intro outside; fin_cases j
      · exact False.elim (outside ⟨1,rfl⟩)
      · exact False.elim (outside ⟨2,rfl⟩)
      · exact False.elim (outside ⟨3,rfl⟩)
end DetDLP.EntryCallFrame
end

section
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

section
namespace DetDLP.EntryCallHarvest
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BoundedProgramLoop StructuredCalls StackRoutines
open BitArithmeticUnit EntryCallFrame
variable {e : ℕ} (ot ov : Fin e)
def program := liftProgram QueryOutputZip.machine (Fin.castAdd 6) (zipports ot ov)
def middle (w : List Bool) : Bank 3 := ![[],[],w.reverse]
def endBank (w : List Bool) : Bank (e+3) := join (fun _ => []) ![w,[],[]]
theorem word_length (tags vals : List Bool) : (QueryOutputZip.value tags vals).length ≤ tags.length := by
  simp only [QueryOutputZip.value,List.length_map]
  exact (List.takeWhile_sublist (l:=tags.zip vals) Prod.fst).length_le.trans (by simp)
theorem harvest (h : ot≠ov) (a : Bank e) (r : Regs) (U : ℕ) (bound : ∀ j,(a j).length ≤ U) :
    let word := QueryOutputZip.value (a ot) (a ov)
    ∃ n rf b,n ≤ 6*U+6 ∧ (∀ j,(b j).length ≤ 7*U+6) ∧
      SafeTrace (step (program ot ov)) (cap (7*U+6)) n ⟨some (program ot ov).entry,r,join a (fun _ => [])⟩
      ⟨none,rf,join b (middle word)⟩ := by
  intro word
  obtain ⟨n,rf,ts,vs,time,tr⟩ := QueryOutputZip.run (a ot) (a ov) [] (r ∘ Fin.castAdd 6)
  let b := Function.update (Function.update a ot ts) ov vs
  have sz := (word_length (a ot) (a ov)).trans (bound ot)
  have hn : n ≤ 6*U+6 := by omega
  have safe := SafeTrace.of_trace tr (P:=cap (7*U+6)) (by
    intro j c hj pref i
    have x := BitTracePolynomial.trace_grows pref i
    have base : (![a ot,a ov,[]] i).length ≤ U := by fin_cases i <;> simp [bound]
    change (c.stacks i).length ≤ (![a ot,a ov,[]] i).length+j at x
    omega)
  have e₁ : ∃ rf',SafeTrace (step (program ot ov)) (cap (7*U+6)) n
      ⟨some (program ot ov).entry,r,join a (fun _ => [])⟩ ⟨none,rf',join b (middle word)⟩ := by
    apply CallOnPorts.run QueryOutputZip.machine (Fin.castAdd 6) (zipports ot ov) (Fin.castAdd_injective ..)
      (distinguishZip ot ov h) _ _ _ _ r rf _ _ _ _ safe
    · intro j; fin_cases j <;> simp [zipports,lo,up]
    · intro j; fin_cases j <;> simp [zipports,lo,up,b,middle,h,h.symm,word]
    · intro j; refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · intro outside
        have ne : j≠ot := fun eq => outside ⟨0,by subst j; rfl⟩
        have nf : j≠ov := fun eq => outside ⟨1,by subst j; rfl⟩
        simp [b,ne,nf]
      · intro outside; fin_cases j
        · simp [middle]
        · simp [middle]
        · exact False.elim (outside ⟨2,rfl⟩)
    · intro j; refine Fin.addCases (fun j _ => ?_) (fun j _ => ?_) j
      · rw [low]; have := bound j; omega
      · simp
  obtain ⟨rf',tr'⟩ := e₁
  refine ⟨n,rf',b,hn,?_,tr'⟩
  intro j; have bd := (tr'.within n _ le_rfl tr'.forget) (lo j)
  change ((join b (middle word)) (j.castAdd 3)).length ≤ _ at bd; simpa using bd

def cleanCmd (e : ℕ) := (EntryScratchReset.reset (e:=e)).seq
  (BitWordBridge.transfer (up (e:=e) 2) (up 0))
def clean (e : ℕ) := compiled (cleanCmd e) (up 2) (up 0)
theorem cleanup (r : Regs) (b : Bank e) (word : List Bool) (U : ℕ)
    (bd : ∀ i,(b i).length ≤ U) (bw : word.length ≤ U) :
    let budget := e*(2*U+3)+3*U+4
    ∃ n rf,n ≤ budget ∧ SafeTrace (step (clean e)) (cap (U+budget)) n
      ⟨some (clean e).entry,r,join b (middle word)⟩ ⟨none,rf,endBank word⟩ := by
  intro budget
  have bc (j : Fin 3) : (middle word j).length ≤ U := by fin_cases j <;> simp [middle,bw]
  obtain ⟨n,rf,time,tr⟩ := EntryScratchReset.reset_eval b (middle word) r U bd bc
  let s := join (fun _ : Fin e => []) (middle word)
  have ne : up (e:=e) 2≠up 0 := by exact fun h => (by decide : (2:Fin 3)≠0) (Fin.natAdd_injective _ _ h)
  have push := ArrayUpdatePrograms.transfer_eval (up (e:=e) 2) (up 0) (0:Fin 8) 1 ne (by decide) rf s
  have eq : transferStacks (up (e:=e) 2) (up 0) s=endBank word := by
    funext j; refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [transferStacks,Function.update_apply,s,endBank,show j.castAdd 3≠up (e:=e) 0 from EntryCallFrame.disjoint j 0,
          show j.castAdd 3≠up (e:=e) 2 from EntryCallFrame.disjoint j 2]
    · fin_cases j <;> simp [transferStacks,Function.update_apply,s,endBank,middle,up]
  rw [eq] at push
  have whole := compiled_halt_trace (Eval.seq tr push) (up 2) (up 0)
  have len : (s (up 2)).length=word.length := by simp [s,up,middle]
  let t := n+(3*(s (up 2)).length+3)+1
  have cost : t ≤ budget := by dsimp only [t,budget]; rw [len]; omega
  refine ⟨t,_,cost,SafeTrace.of_trace whole ?_⟩
  intro j c hj pref i
  have base : ((join b (middle word)) i).length ≤ U := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using bd j
    · simpa using bc j
  exact (BitTracePolynomial.trace_grows pref i).trans (Nat.add_le_add base (hj.trans cost))
end DetDLP.EntryCallHarvest
end

section
namespace DetDLP.EntryEvaluatorCall
open OAI.Algorithms.SubexponentialSAT BitProgram ProgramLinking BoundedProgramLoop SqrtLogSpace
open BitArithmeticUnit EntryCallFrame
variable {e l : ℕ} (Q : Program 3 e l) (it iv ot ov : Fin e)
def inner := liftProgram Q (Fin.castAdd 5) (Fin.castAdd 3)
def table := link (pre it iv) (link (inner Q) (link (EntryCallHarvest.program ot ov) (EntryCallHarvest.clean e)))
def budget (e s U : ℕ) := (e+4)*(20*(s+U+10))
theorem mono {r s l W W' : ℕ} {p : Program r s l} {n : ℕ} {x y : Cfg r s l}
    (h : SafeTrace (step p) (cap W) n x y) (le : W ≤ W') : SafeTrace (step p) (cap W') n x y :=
  h.map id (fun _ _ h => h) (fun _ h i => (h i).trans le)
theorem run (hi : it≠iv) (ho : ot≠ov) (desc : List Bool) (v : ℕ) (bits word : List Bool) (T U : ℕ)
    (eval : ∀ (r : Fin 3→Bool),
      let q := (encodePortQuery desc v bits).tail
      ∃ (n : ℕ) (c : Cfg 3 e l),n ≤ T ∧ Trace Q n ⟨some Q.entry,r,initQ it iv q⟩ c ∧ c.pc=none ∧
        QueryOutputZip.value (c.stacks ot) (c.stacks ov)=word ∧
        ∀ j b,j ≤ n → Trace Q j ⟨some Q.entry,r,initQ it iv q⟩ b → ∀ k,(b.stacks k).length ≤ U)
    (r : Regs) :
    let V := budget e (EntryCallPreparation.size desc (countWord v) bits) U
    ∃ n rf,n ≤ T+V ∧ SafeTrace (step (table Q it iv ot ov)) (cap V) n
      ⟨some (table Q it iv ot ov).entry,r,source it desc (countWord v) bits⟩ ⟨none,rf,EntryCallHarvest.endBank word⟩ := by
  intro V
  let q := (encodePortQuery desc v bits).tail
  let s := EntryCallPreparation.size desc (countWord v) bits
  let pcost := EntryCallPreparation.cost desc v bits
  obtain ⟨r₁,tr₁⟩ := prepare it iv hi desc v bits r
  obtain ⟨n,⟨pc,reg,a⟩,time,body,hpc,out,room⟩ := eval (r₁ ∘ Fin.castAdd 5)
  dsimp only at hpc; subst pc
  have hq : q.length ≤ U := by
    have h := room 0 _ (Nat.zero_le _) (.refl _) iv
    simpa [initQ,hi.symm,q] using h
  have bd (j : Fin e) : (a j).length ≤ U := room n _ le_rfl body j
  have safe := SafeTrace.of_trace body room
  have call : ∃ rf,SafeTrace (step (inner Q)) (cap U) n
      ⟨some (inner Q).entry,r₁,join (initQ it iv q) (fun _ => [])⟩ ⟨none,rf,join a (fun _ => [])⟩ := by
    apply CallOnPorts.run Q (Fin.castAdd 5) (Fin.castAdd 3) (Fin.castAdd_injective ..) (Fin.castAdd_injective ..)
      _ _ _ _ r₁ reg _ _ _ _ safe
    · intro j; simp [q]
    · intro j; simp
    · intro j; refine Fin.addCases (fun j outside => False.elim (outside ⟨j,rfl⟩)) (fun j _ => ?_) j
      simp
    · intro j; refine Fin.addCases (fun j outside => False.elim (outside ⟨j,rfl⟩)) (fun j _ => ?_) j
      simp
  obtain ⟨r₂,tr₂⟩ := call
  obtain ⟨k,r₃,b,hk,bs,tr₃⟩ := EntryCallHarvest.harvest ot ov ho a r₂ U bd
  have output : QueryOutputZip.value (a ot) (a ov)=word := out
  rw [output] at tr₃
  have wl := (EntryCallHarvest.word_length (a ot) (a ov)).trans (bd ot)
  rw [output] at wl
  let Z := 7*U+6
  obtain ⟨f,r₄,hf,tr₄⟩ := EntryCallHarvest.cleanup r₃ b word Z bs (by dsimp [Z]; omega)
  have pcosteq : pcost=7*s+7*q.length+42 := rfl
  have huge : s+pcost+U+Z+(e*(2*Z+3)+3*Z+4)+6*U+6 ≤ V := by
    change _ ≤ (e+4)*(20*(s+U+10))
    have p : e*(2*Z+3) ≤ e*(20*(s+U+10)) := Nat.mul_le_mul_left _ (by dsimp [Z]; omega)
    rw [Nat.add_mul]; dsimp only [Z] at *; omega
  have b₁ : s+pcost ≤ V := by omega
  have b₂ : U ≤ V := by omega
  have b₃ : Z ≤ V := by omega
  have b₄ : Z+(e*(2*Z+3)+3*Z+4) ≤ V := by omega
  have block := BoundedProgramLink.join _ _ (mono tr₁ b₁)
    (BoundedProgramLink.join _ _ (mono tr₂ b₂) (BoundedProgramLink.join _ _ (mono tr₃ b₃) (mono tr₄ b₄)))
  refine ⟨_,r₄,?_,block⟩
  change pcost+(n+(k+f)) ≤ T+V
  omega
end DetDLP.EntryEvaluatorCall
end

section
namespace DetDLP.EntryEvaluatorExport
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
theorem full (E : PrimitiveMachine) (out : Fin E.tapeCount) :
    ∃ (s l : ℕ) (caller : BitProgram.Program 8 (s+3) l) (src : Fin s),
      ∀ (desc : List Bool) (v : ℕ) (bits word : List Bool) (T U : ℕ),
      RunsWithin E out (encodePortQuery desc v bits) word T U →
      ∀ r : Fin 8→Bool,
      let vert := SqrtLogSpace.countWord v
      let V := (s+4)*(20*(desc.length+vert.length+bits.length+(U+8)+10))
      let input := Fin.addCases (m:=s) (n:=3) (fun j => if j=src then desc else []) ![vert,bits,[]]
      let output := Fin.addCases (m:=s) (n:=3) (fun _ => ([]:List Bool)) ![word,[],[]]
      let start : BitProgram.Cfg 8 (s+3) l := ⟨some caller.entry,r,input⟩
      ∃ steps rf,steps ≤ 8*T+V ∧ BitProgram.Trace caller steps start ⟨none,rf,output⟩ ∧
        ∀ j c,j ≤ steps → BitProgram.Trace caller j start c → ∀ i,(c.stacks i).length ≤ V := by
  obtain ⟨s,l,Q,it,iv,ot,ov,hi,ho,H⟩ := bounded_entry_evaluator_stack_simulation E out
  refine ⟨s,_,EntryEvaluatorCall.table Q it iv ot ov,it,?_⟩
  intro desc v bits word T U exec r vert V input output start
  let q := (encodePortQuery desc v bits).tail
  have run := H q word T U (by exact exec)
  have core (regs : Fin 3→Bool) := run regs
  have localRun (regs : Fin 3→Bool) :
      ∃ (n : ℕ) (c : BitProgram.Cfg 3 s l),n ≤ 8*T ∧
      BitProgram.Trace Q n ⟨some Q.entry,regs,EntryCallFrame.initQ it iv q⟩ c ∧ c.pc=none ∧
      QueryOutputZip.value (c.stacks ot) (c.stacks ov)=word ∧ ∀ j b,j ≤ n →
        BitProgram.Trace Q j ⟨some Q.entry,regs,EntryCallFrame.initQ it iv q⟩ b → ∀ k,(b.stacks k).length ≤ U+8 := by
    obtain ⟨n,c,time,body,halt,word',room⟩ := core regs
    refine ⟨n,c,by exact_mod_cast time,body,halt,word',?_⟩
    intro j b hj pref k
    simpa only [Nat.floor_natCast] using room j b hj pref k
  obtain ⟨n,rf,time,tr⟩ := EntryEvaluatorCall.run Q it iv ot ov hi ho desc v bits word (8*T) (U+8) localRun r
  exact ⟨n,rf,time,tr.forget,tr.within⟩
end DetDLP.EntryEvaluatorExport
end

open DetDLP
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem solution (E : PrimitiveMachine) (out : Fin E.tapeCount) :
    ∃ (s l : ℕ) (caller : BitProgram.Program 8 (s+3) l) (src : Fin s),
      ∀ (desc : List Bool) (v : ℕ) (bits word : List Bool) (T U : ℕ),
      RunsWithin E out (encodePortQuery desc v bits) word T U →
      ∀ r : Fin 8→Bool,
      let vert := SqrtLogSpace.countWord v
      let V := (s+4)*(20*(desc.length+vert.length+bits.length+(U+8)+10))
      let input := Fin.addCases (m:=s) (n:=3) (fun j => if j=src then desc else []) ![vert,bits,[]]
      let output := Fin.addCases (m:=s) (n:=3) (fun _ => ([]:List Bool)) ![word,[],[]]
      let start : BitProgram.Cfg 8 (s+3) l := ⟨some caller.entry,r,input⟩
      ∃ steps rf,steps ≤ 8*T+V ∧ BitProgram.Trace caller steps start ⟨none,rf,output⟩ ∧
        ∀ j c,j ≤ steps → BitProgram.Trace caller j start c → ∀ i,(c.stacks i).length ≤ V := by
  exact EntryEvaluatorExport.full E out
