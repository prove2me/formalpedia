-- Prove2me | solution 1 for DetDLP.bordered_binary_input_preparation
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T14:45:42.118817+00:00
-- url     : https://prove2.me/submissions/aeb59bfb-0ca1-46c5-a29b-47f2875f1e9e

import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S067
import Definitions.Def_DetDLP_Machine
import Definitions.Def_DetDLP_BorderedBitIO
import Definitions.Def_DetDLP_FilterAndCoset
import Definitions.Def_DetDLP_BorderedHermite

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

namespace DetDLP.UpdateCosts
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode BitRegisterCall

structure Input where
  m : ℕ
  n : ℕ
  x : Fin n → ℕ
  a : Fin n → ℕ
  B : Matrix (Fin n) (Fin n) ℤ
  c : ℕ
  valid : BorderedBitIO.Valid m x a B c
def U (z : Input) := z.n+bitLen z.m+2
theorem u_two (z : Input) : 2 ≤ U z := by dsimp [U]; omega
def Bnd (f : Input → ℕ) := ∃ k : ℕ,∀ z,f z ≤ (U z)^k
theorem const_bnd (c : ℕ) : Bnd (fun _ => c) := by
  refine ⟨c,fun z => ?_⟩
  exact (Nat.le_of_lt (Nat.lt_two_pow_self)).trans (Nat.pow_le_pow_left (u_two z) _)
theorem base_bnd : Bnd U := ⟨1,by simp⟩
theorem bnd_mono {f g} (hf : Bnd f) (h : ∀ z,g z ≤ f z) : Bnd g := by
  obtain ⟨k,hk⟩ := hf; exact ⟨k,fun z => (h z).trans (hk z)⟩
theorem bnd_add {f g} (hf : Bnd f) (hg : Bnd g) : Bnd (fun z => f z+g z) := by
  obtain ⟨k,hk⟩ := hf; obtain ⟨j,hj⟩ := hg
  refine ⟨max k j+1,fun z => ?_⟩
  have H := u_two z
  have a := (hk z).trans (Nat.pow_le_pow_right (by omega : 0 < U z) (le_max_left k j))
  have b := (hj z).trans (Nat.pow_le_pow_right (by omega : 0 < U z) (le_max_right k j))
  rw [pow_succ]; nlinarith only [a,b,Nat.mul_le_mul_left ((U z)^(max k j)) H]
theorem bnd_mul {f g} (hf : Bnd f) (hg : Bnd g) : Bnd (fun z => f z*g z) := by
  obtain ⟨k,hk⟩ := hf; obtain ⟨j,hj⟩ := hg
  exact ⟨k+j,fun z => by rw [pow_add]; exact Nat.mul_le_mul (hk z) (hj z)⟩
theorem bnd_pow {f} (hf : Bnd f) (t : ℕ) : Bnd (fun z => (f z)^t) := by
  obtain ⟨k,hk⟩ := hf
  exact ⟨k*t,fun z => by rw [pow_mul]; exact Nat.pow_le_pow_left (hk z) t⟩

abbrev St (s : ℕ) := Fin s → List Bool
def Width {s} (f : Input → St s) := ∃ k : ℕ,∀ z i,(f z i).length ≤ (U z)^k
def Executes {s} (q : Cmd 8 s) (A B : Input → St s) :=
  ∃ k : ℕ,∀ z (r : Regs),∃ t rf,t ≤ (U z)^k ∧ Eval q t ⟨r,A z⟩ ⟨rf,B z⟩

theorem of_bound {s} {q : Cmd 8 s} {A B : Input → St s} {f : Input → ℕ} (h : Bnd f)
    (ev : ∀ z (r : Regs),∃ t rf,t ≤ f z ∧ Eval q t ⟨r,A z⟩ ⟨rf,B z⟩) : Executes q A B := by
  obtain ⟨k,hk⟩ := h
  refine ⟨k,fun z r => ?_⟩
  obtain ⟨t,rf,ht,e⟩ := ev z r
  exact ⟨t,rf,ht.trans (hk z),e⟩

theorem compose {s} {a b : Cmd 8 s} {A B D : Input → St s} (h : Executes a A B) (g : Executes b B D) :
    Executes (a.seq b) A D := by
  obtain ⟨k,hk⟩ := h; obtain ⟨j,hj⟩ := g
  apply of_bound (bnd_add (bnd_pow base_bnd k) (bnd_pow base_bnd j))
  intro z r
  obtain ⟨t,rt,ht,e⟩ := hk z r; obtain ⟨v,rv,hv,f⟩ := hj z rt
  exact ⟨_,rv,Nat.add_le_add ht hv,.seq e f⟩

theorem output_width {s} [NeZero s] {q : Cmd 8 s} {A B : Input → St s} (h : Executes q A B) (w : Width A) : Width B := by
  obtain ⟨k,hk⟩ := h; obtain ⟨j,hj⟩ := w
  obtain ⟨l,hl⟩ := bnd_add (bnd_pow base_bnd j) (bnd_add (bnd_pow base_bnd k) (const_bnd 1))
  refine ⟨l,fun z i => ?_⟩
  obtain ⟨t,rf,ht,et⟩ := hk z (fun _ => false)
  have e := BitTracePolynomial.trace_grows (compiled_halt_trace et 0 0) i
  exact (show (B z i).length ≤ (A z i).length+(t+1) from e).trans
    ((Nat.add_le_add (hj z i) (Nat.add_le_add_right ht 1)).trans (hl z))

abbrev bank {s} (f : Input → Vars s) := fun z => frame (f z)
theorem straight {n} (c : List (BitRegisterCode.Instr n)) (v w : Input → Vars n)
    (bounds : Width (bank v)) (hv : ∀ z,BitRegisterCode.Valid c (v z))
    (eq : ∀ z,run c (v z)=w z) : Executes (compile c) (bank v) (bank w) := by
  obtain ⟨k,hk⟩ := bounds
  apply of_bound (bnd_mul (const_bnd (1000^(c.length+1))) (bnd_pow (bnd_add (bnd_pow base_bnd k) (const_bnd 2)) 2))
  intro z r
  obtain ⟨t,rf,ht,et⟩ := run_eval c (v z) r ((U z)^k) (fun j => by simpa [bank,frame,Nat.size_eq_bits_len] using hk z (port j)) (hv z)
  rw [eq z] at et
  exact ⟨t,rf,ht,et⟩

def liftCode {m u : ℕ} (q : Code m) := subroutine (compiled q (low 0) (low 0)) (@left m u)
def join {m u : ℕ} (v : Vars m) (w : Vars u) : Vars (m+u) :=
  fun j => Fin.addCases (m:=m) (n:=u) (motive:=fun _ => ℕ) v w j
theorem push_left {m u : ℕ} {q : Code m} {v w : Input → Vars m} (p : Input → Vars u)
    (h : Executes q (bank v) (bank w)) :
    Executes (liftCode (u:=u) q) (bank fun z => join (v z) (p z)) (bank fun z => join (w z) (p z)) := by
  obtain ⟨k,hk⟩ := h
  apply of_bound (bnd_add (bnd_pow base_bnd k) (const_bnd 1))
  intro z r
  obtain ⟨t,rf,ht,et⟩ := hk z r
  exact ⟨_,rf,Nat.add_le_add_right ht 1,call_left _ _ _ _ _ _ _ (compiled_halt_trace et (low 0) (low 0))⟩
end DetDLP.UpdateCosts
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

namespace DetDLP.BorderedHermite

/-- The underlying two-column Euclidean operation has determinant one. -/
theorem pivot_unimodular (p t : ℤ) (hp : 0 < p) :
    let g : ℤ := p.gcd t
    p.gcdA t * (p/g) + p.gcdB t * (t/g) = 1 := by
  intro g
  have hp' : g*(p/g) = p := Int.mul_ediv_cancel' (Int.gcd_dvd_left ..)
  have ht' : g*(t/g) = t := Int.mul_ediv_cancel' (Int.gcd_dvd_right ..)
  have hne : g ≠ 0 := by intro h; rw [h,zero_mul] at hp'; omega
  apply mul_left_cancel₀ hne
  calc
    _ = p.gcdA t*(g*(p/g))+p.gcdB t*(g*(t/g)) := by ring
    _ = _ := by rw [hp',ht',mul_one]; simpa [g,mul_comm] using (Int.gcd_eq_gcd_ab p t).symm

theorem pivot_row {n : ℕ} (m : ℤ) (j : Fin n) (v w : Column n) (hp : 0 < (v.get j)) :
    (pivotPair m j v w).1.get j = ((v.get j).gcd (w.get j) : ℤ) ∧ (pivotPair m j v w).2.get j = 0 := by
  let p := (v.get j)
  let t := (w.get j)
  let g : ℤ := p.gcd t
  by_cases hz : (w.get j) = 0
  · simp [pivotPair,hz,abs_of_pos hp]
  · simp only [pivotPair,if_neg hz]
    simp only [get_ofFn,trim,lt_irrefl,if_false]
    constructor
    · change p.gcdA t * p + p.gcdB t * t = _
      linear_combination (Int.gcd_eq_gcd_ab p t).symm
    · change -(t/g)*p+(p/g)*t = 0
      have hp' : g*(p/g) = p := Int.mul_ediv_cancel' (Int.gcd_dvd_left ..)
      have ht' : g*(t/g) = t := Int.mul_ediv_cancel' (Int.gcd_dvd_right ..)
      linear_combination -(t/g)*hp'.symm + (p/g)*ht'.symm

abbrev Subgroup (n : ℕ) := AddSubgroup (Fin n → ℤ)

private def grid {n : ℕ} (m : ℤ) (j : Fin n) : Fin n → ℤ := Pi.single j m

private def reserves {n : ℕ} (m : ℤ) (k : ℕ) (H : Subgroup n) : Prop :=
  ∀ i : Fin n, k ≤ i.val → grid m i ∈ H

private def held {n : ℕ} (H : Subgroup n) (xs : Array (Column n)) :=
  ∀ c ∈ xs, c.get ∈ H

private theorem held_push {n : ℕ} (H : Subgroup n) (xs : Array (Column n)) (v) :
    held H (xs.push v) ↔ held H xs ∧ v.get ∈ H := by
  simp [held,Array.mem_push,or_imp,forall_and]

private theorem reserves_succ {n : ℕ} (m : ℤ) (j : Fin n) (H : Subgroup n) :
    reserves m j.val H ↔ grid m j ∈ H ∧ reserves m (j.val+1) H := by
  constructor
  · intro h; exact ⟨h _ le_rfl,fun i hi => h i (by omega)⟩
  · rintro ⟨hj,hs⟩ i hi
    by_cases he : i.val = j.val
    · simpa [Fin.ext he] using hj
    · exact hs i (by omega)

private theorem sub_iff {n : ℕ} (H : Subgroup n) {u v : Fin n → ℤ} (hv : v ∈ H) :
    u-v ∈ H ↔ u ∈ H :=
  ⟨fun h => by simpa using H.add_mem h hv,fun h => H.sub_mem h hv⟩

/-- A reduction by reserved pure columns preserves membership in every subgroup
containing those columns. This handles intermediate tail normalization as well. -/
private theorem reduce_mem_iff {n : ℕ} (m : ℤ) (k : ℕ) (H : Subgroup n)
    (h : reserves m k H) (v : Fin n → ℤ) :
    (fun i : Fin n => if k ≤ i.val then v i % m else v i) ∈ H ↔ v ∈ H := by
  classical
  let q (j : Fin n) := if k ≤ j.val then v j / m else 0
  have hs : ∑ j : Fin n, q j • grid m j ∈ H := by
    apply H.sum_mem
    intro j _
    by_cases hj : k ≤ j.val
    · exact H.zsmul_mem (h j hj) _
    · simp [q,hj]
  have he : (fun i : Fin n => if k ≤ i.val then v i % m else v i) =
      v - ∑ j : Fin n, q j • grid m j := by
    ext i
    simp only [Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp [grid,q,Pi.single_apply,Int.emod_def,mul_comm]
      split_ifs <;> simp_all
    · intro b _ hb
      simp [grid,Pi.single_apply,hb,Ne.symm hb]
    · simp
  rw [he]
  exact sub_iff H hs

private theorem trim_mem {n : ℕ} (m : ℤ) (j : Fin n) (H : Subgroup n)
    (h : reserves m (j.val+1) H) (v : Fin n → ℤ) :
    (fun i => trim m j i (v i)) ∈ H ↔ v ∈ H := by
  simpa only [trim,Fin.lt_def,Nat.succ_le_iff] using reduce_mem_iff m (j.val+1) H h v

private theorem pair_mem {n : ℕ} (m : ℤ) (j : Fin n) (H : Subgroup n)
    (h : reserves m (j.val+1) H) (v w : Column n) (hp : 0 < v.get j) :
    (pivotPair m j v w).1.get ∈ H ∧ (pivotPair m j v w).2.get ∈ H ↔
      v.get ∈ H ∧ w.get ∈ H := by
  classical
  let p := v.get j
  let t := w.get j
  let g : ℤ := p.gcd t
  let a := p.gcdA t
  let b := p.gcdB t
  let C := a • v.get + b • w.get
  let D := -(t/g) • v.get + (p/g) • w.get
  by_cases hz : w.get j = 0
  · simp [pivotPair,hz]
  · have hv : (pivotPair m j v w).1.get = fun i => trim m j i (C i) := by
      funext i; simp [pivotPair,hz,C,a,b,p,t]
    have hw : (pivotPair m j v w).2.get = fun i => trim m j i (D i) := by
      funext i; simp [pivotPair,hz,D,g,p,t]
    rw [hv,hw,trim_mem m j H h C,trim_mem m j H h D]
    have det : a*(p/g)+b*(t/g)=1 := pivot_unimodular p t hp
    constructor
    · rintro ⟨hC,hD⟩
      have ev : (p/g) • C - b • D = v.get := by
        ext i; simp [C,D]; linear_combination v.get i * det
      have ew : (t/g) • C + a • D = w.get := by
        ext i; simp [C,D]; linear_combination w.get i * det
      exact ⟨ev ▸ H.sub_mem (H.zsmul_mem hC (p/g)) (H.zsmul_mem hD b),
        ew ▸ H.add_mem (H.zsmul_mem hC (t/g)) (H.zsmul_mem hD a)⟩
    · rintro ⟨hV,hW⟩
      exact ⟨H.add_mem (H.zsmul_mem hV a) (H.zsmul_mem hW b),
        H.add_mem (H.zsmul_mem hV (-(t/g))) (H.zsmul_mem hW (p/g))⟩

private def oldZero {n : ℕ} (k : ℕ) (v : Column n) : Prop :=
  ∀ i : Fin n, i.val < k → v.get i = 0

private theorem pair_past {n : ℕ} (m : ℤ) (j : Fin n) (v w : Column n)
    (hv : oldZero j.val v) (hw : oldZero j.val w) :
    oldZero j.val (pivotPair m j v w).1 ∧ oldZero j.val (pivotPair m j v w).2 := by
  by_cases hz : w.get j = 0
  · simpa [pivotPair,hz] using And.intro hv hw
  · constructor <;> intro i hi <;> simp [pivotPair,hz,trim,hv i hi,hw i hi]

private theorem fold_pairs {n : ℕ} (m : ℤ) (j : Fin n) (ws : List (Column n))
    (st : Column n × Array (Column n)) (hp : 0 < st.1.get j)
    (hz : oldZero j.val st.1) (ht : ∀ v ∈ st.2, oldZero (j.val+1) v)
    (hw : ∀ w ∈ ws, oldZero j.val w) :
    let out := ws.foldl (pairStep m j) st
    0 < out.1.get j ∧ oldZero j.val out.1 ∧
      (∀ v ∈ out.2, oldZero (j.val+1) v) ∧
      ∀ H : Subgroup n, reserves m (j.val+1) H →
        (out.1.get ∈ H ∧ held H out.2 ↔
          st.1.get ∈ H ∧ held H st.2 ∧ ∀ w ∈ ws, w.get ∈ H) := by
  induction ws generalizing st with
  | nil => exact ⟨hp,hz,ht,fun _ _ => by simp⟩
  | cons w ws ih =>
    have pw := pivot_row m j st.1 w hp
    have gp : 0 < (pivotPair m j st.1 w).1.get j := by
      rw [pw.1]; exact_mod_cast Int.gcd_pos_of_ne_zero_left _ hp.ne'
    obtain ⟨zo,zr⟩ := pair_past m j st.1 w hz (hw w (by simp))
    have zz : oldZero (j.val+1) (pivotPair m j st.1 w).2 := by
      intro i hi
      by_cases he : i.val = j.val
      · simpa [Fin.ext he] using pw.2
      · exact zr i (by omega)
    have ha : ∀ v ∈ (pairStep m j st w).2, oldZero (j.val+1) v := by
      intro v hv
      rcases Array.mem_push.mp hv with h|rfl
      · exact ht v h
      · exact zz
    obtain ⟨p,z,t,H⟩ := ih (pairStep m j st w) gp zo ha (fun v h => hw v (by simp [h]))
    refine ⟨p,z,t,fun L hL => ?_⟩
    rw [List.foldl_cons,H L hL]
    change (_ ∈ L ∧ held L (st.2.push _) ∧ _) ↔ _
    rw [held_push]
    simp only [List.mem_cons,forall_eq_or_imp]
    have e := pair_mem m j L hL st.1 w hp
    tauto

/-- Each processed row has one positive pivot and the required reduced entries. -/
private def shape {n : ℕ} (k : ℕ) (cols : Array (Column n)) : Prop :=
  cols.size = k ∧ ∀ i : Fin n, i.val < k →
    ∃ d : ℤ, 0 < d ∧ ∀ j : Fin cols.size,
      (if i.val < j.val then cols[j].get i = 0
       else if i.val = j.val then cols[j].get i = d
       else 0 ≤ cols[j].get i ∧ cols[j].get i < d)

private theorem reduceFixed_pre {n : ℕ} (m : ℤ) (j : Fin n) (p c : Column n)
    (hz : oldZero j.val p) (i : Fin n) (hi : i < j) :
    (reduceFixed m j p c).get i = c.get i := by
  simp [reduceFixed,trim,hz i hi,not_lt.mpr hi.le]

private theorem reduceFixed_self {n : ℕ} (m : ℤ) (j : Fin n) (p c : Column n) :
    (reduceFixed m j p c).get j = c.get j % p.get j := by
  simp [reduceFixed,trim,Int.emod_def,mul_comm]

private theorem push_shape {n : ℕ} (m : ℤ) (j : Fin n) (cols : Array (Column n))
    (hs : shape j.val cols) (p : Column n) (hp : 0 < p.get j) (hz : oldZero j.val p) :
    shape (j.val+1) ((cols.map (reduceFixed m j p)).push p) := by
  obtain ⟨hsize,hrows⟩ := hs
  refine ⟨by simp [hsize],?_⟩
  intro i hi
  have hcase (a : Fin ((cols.map (reduceFixed m j p)).push p).size) :
      a.val < cols.size ∨ a.val = cols.size := by
    have ha := a.isLt
    simp only [Array.size_push,Array.size_map] at ha
    omega
  by_cases h : i.val = j.val
  · have ei : i = j := Fin.ext h
    subst i
    refine ⟨p.get j,hp,fun a => ?_⟩
    rcases hcase a with ha|ha
    · have haj : a.val < j.val := by omega
      simp [Array.getElem_push,Array.getElem_map,ha,hsize,show ¬j.val<a.val by omega,
        show j.val≠a.val by omega,haj,reduceFixed_self,Int.emod_nonneg _ hp.ne',Int.emod_lt_of_pos _ hp]
    · simp [Array.getElem_push,ha,hsize]
  · have hi' : i.val < j.val := by omega
    obtain ⟨d,hd,hrow⟩ := hrows i hi'
    refine ⟨d,hd,fun a => ?_⟩
    rcases hcase a with ha|ha
    · have e := hrow (⟨a.val,ha⟩ : Fin cols.size)
      simpa [Array.getElem_push,Array.getElem_map,ha,reduceFixed_pre m j p _ hz i hi'] using e
    · simp [Array.getElem_push,ha,hsize,hi',hz i hi']

private theorem reduceFixed_mem {n : ℕ} (m : ℤ) (j : Fin n) (H : Subgroup n)
    (hr : reserves m (j.val+1) H) (p c : Column n) (hp : p.get ∈ H) :
    (reduceFixed m j p c).get ∈ H ↔ c.get ∈ H := by
  let q := c.get j / p.get j
  have he : (reduceFixed m j p c).get = fun i => trim m j i ((c.get - q • p.get) i) := by
    ext; simp [reduceFixed,q]
  rw [he,trim_mem m j H hr, sub_iff H (H.zsmul_mem hp q)]

private def represents {n : ℕ} (m : ℤ) (k : ℕ) (st : Array (Column n) × Array (Column n))
    (H : Subgroup n) := held H st.1 ∧ held H st.2 ∧ reserves m k H

private theorem stage_inv {n : ℕ} {m : ℤ} (hm : 0 < m) (j : Fin n)
    (st : Array (Column n) × Array (Column n)) (hs : shape j.val st.1)
    (hw : ∀ w ∈ st.2, oldZero j.val w) :
    let st' := pivotStage m j st
    shape (j.val+1) st'.1 ∧ (∀ w ∈ st'.2, oldZero (j.val+1) w) ∧
      ∀ H : Subgroup n, represents m (j.val+1) st' H ↔ represents m j.val st H := by
  let e : Column n := Vector.ofFn (fun i => if i = j then m else 0)
  have eg : e.get = grid m j := by ext i; simp [e,grid,Pi.single_apply]
  have ez : oldZero j.val e := by intro i hi; simp [e,Fin.ne_of_val_ne (by omega : i.val ≠ j.val)]
  let f := st.2.toList.foldl (pairStep m j) (e,#[])
  obtain ⟨hp,hz,ht,hf⟩ := fold_pairs m j st.2.toList (e,#[])
    (by simpa [e] using hm) ez (by simp) (by simpa using hw)
  change shape _ ((st.1.map (reduceFixed m j f.1)).push f.1) ∧
    (∀ w ∈ f.2, _) ∧ _
  refine ⟨push_shape m j st.1 hs f.1 hp hz,ht,fun H => ?_⟩
  change (held H ((st.1.map (reduceFixed m j f.1)).push f.1) ∧ held H f.2 ∧ _) ↔ _
  rw [held_push]
  change _ ↔ held H st.1 ∧ held H st.2 ∧ reserves m j.val H
  rw [reserves_succ m j H]
  by_cases hr : reserves m (j.val+1) H
  · have he : f.1.get ∈ H ∧ held H f.2 ↔ grid m j ∈ H ∧ held H st.2 := by
      simpa [f,held,eg] using hf H hr
    have hh (hp' : f.1.get ∈ H) :
        held H (st.1.map (reduceFixed m j f.1)) ↔ held H st.1 := by
      simp [held,Array.mem_map,reduceFixed_mem m j H hr f.1 _ hp']
    constructor
    · rintro ⟨⟨hm',hp'⟩,ht',_⟩
      obtain ⟨hg,ht''⟩ := he.mp ⟨hp',ht'⟩
      exact ⟨(hh hp').mp hm',ht'',hg,hr⟩
    · rintro ⟨hm',ht',hg,_⟩
      obtain ⟨hp',ht''⟩ := he.mpr ⟨hg,ht'⟩
      exact ⟨⟨(hh hp').mpr hm',hp'⟩,ht'',hr⟩
  · tauto

private theorem rows_inv {n : ℕ} {m : ℤ} (hm : 0 < m) (cols : Array (Column n))
    (k : ℕ) (hk : k ≤ n) :
    let st := runRows m cols k
    shape k st.1 ∧ (∀ w ∈ st.2, oldZero k w) ∧
      ∀ H : Subgroup n, represents m k st H ↔ held H cols ∧ reserves m 0 H := by
  induction k with
  | zero =>
    refine ⟨⟨rfl,by simp⟩,by simp [oldZero],fun H => ?_⟩
    change held H #[] ∧ held H (cols.map fun c => c.map (· % m)) ∧ reserves m 0 H ↔ _
    have he (c : Column n) (hr : reserves m 0 H) : (c.map (· % m)).get ∈ H ↔ c.get ∈ H := by
      have he' : (c.map (· % m)).get = fun i => c.get i % m := by
        ext i; change (c.map (· % m))[i.val] = (c.get i) % m; rw [Vector.getElem_map]; rfl
      rw [he']; simpa using reduce_mem_iff m 0 H hr c.get
    by_cases h : reserves m 0 H
    · simp [held,Array.mem_map,h,he _ h]
    · tauto
  | succ k ih =>
    have hlt : k < n := by omega
    obtain ⟨hs,hw,hr⟩ := ih (by omega)
    obtain ⟨hs',hw',hr'⟩ := stage_inv hm (⟨k,hlt⟩ : Fin n) _ hs hw
    simp only [runRows, dif_pos hlt]
    exact ⟨hs',hw',fun H => (hr' H).trans (hr H)⟩

theorem normalForm_certificate {n : ℕ} {m : ℤ} (hm : 0 < m) (cols : Array (Column n)) :
    let out := normalForm m cols
    out.size = n ∧ IsColumnHNF (asMatrix out) ∧
      ∀ H : AddSubgroup (Fin n → ℤ), (∀ c ∈ out, c.get ∈ H) ↔
        (∀ c ∈ cols, c.get ∈ H) ∧ (∀ i : Fin n, (Pi.single i m : Fin n → ℤ) ∈ H) := by
  intro out
  obtain ⟨⟨hs,hrows⟩,hzero,hspan⟩ := rows_inv hm cols n le_rfl
  change out.size = n at hs
  have entry (i j : Fin n) : asMatrix out i j = (out[j.val]'(by rw [hs]; exact j.isLt)).get i := by
    simp [asMatrix,show j.val < out.size by rw [hs]; exact j.isLt]
  have row (i : Fin n) : ∃ d : ℤ, 0 < d ∧ ∀ j : Fin n,
      (if i < j then asMatrix out i j = 0 else if i = j then asMatrix out i j = d
       else 0 ≤ asMatrix out i j ∧ asMatrix out i j < d) := by
    obtain ⟨d,hd,hr⟩ := hrows i i.isLt
    refine ⟨d,hd,fun j => ?_⟩
    rw [entry]
    simpa only [Fin.lt_def,Fin.ext_iff,Fin.getElem_fin,out,normalForm] using hr ⟨j.val,by change j.val < out.size; rw [hs]; exact j.isLt⟩
  refine ⟨hs,⟨?_,?_,?_⟩,?_⟩
  · intro i j hij
    obtain ⟨d,_,hr⟩ := row i
    simpa [hij] using hr j
  · intro i
    obtain ⟨d,hd,hr⟩ := row i
    simpa [show asMatrix out i i = d by simpa using hr i] using hd
  · intro i j hji
    obtain ⟨d,_,hr⟩ := row i
    rw [show asMatrix out i i = d by simpa using hr i]
    simpa [not_lt.mpr hji.le,ne_of_gt hji] using hr j
  · intro H
    have hz : held H (runRows m cols n).2 := by
      intro w hw
      have he : w.get = 0 := funext fun i => hzero w hw i i.isLt
      rw [he]; exact H.zero_mem
    have hr : reserves m n H := fun i h => False.elim (Nat.not_le_of_lt i.isLt h)
    have eq := hspan H
    simp only [represents,hz,hr,and_true] at eq
    simpa only [reserves,Nat.zero_le,forall_true_left,grid,held,out,normalForm] using eq

end DetDLP.BorderedHermite
end

section

namespace DetDLP.UnsignedHermitePivot
open BorderedHermite
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterCode

def signedColumn {n} (v : Fin n → ℕ) : Column n := Vector.ofFn (fun i => (v i : ℤ))

def tail (m a b t' p' v w : ℕ) : ℕ × ℕ :=
  ((a*v+b*w)%m,(((m-1)*t')*v+p'*w)%m)

private theorem minus_one {m} [NeZero m] : ((m-1:ℕ):ZMod m) = -1 := by
  have hm := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [Nat.cast_sub (by omega),ZMod.natCast_self,Nat.cast_one,zero_sub]

private theorem congr_mod {m} [NeZero m] (n : ℕ) (x : ℤ) (h : (n:ZMod m)=(x:ZMod m)) :
    ((n%m:ℕ):ℤ) = x%(m:ℤ) := by
  rw [← ZMod.val_intCast]
  exact_mod_cast (ZMod.val_natCast m n).symm.trans (congrArg ZMod.val h)

theorem tail_correct {m : ℕ} [NeZero m] (p t v w : ℕ) :
    let g := p.gcd t
    let A := ((p.gcdA t:ℤ):ZMod m).val
    let B := ((p.gcdB t:ℤ):ZMod m).val
    let z := tail m A B (t/g) (p/g) v w
    (z.1:ℤ) = (p.gcdA t*(v:ℤ)+p.gcdB t*(w:ℤ))%(m:ℤ) ∧
    (z.2:ℤ) = (-((t/g:ℕ):ℤ)*(v:ℤ)+((p/g:ℕ):ℤ)*(w:ℤ))%(m:ℤ) := by
  intro g A B z
  constructor
  · apply congr_mod
    simp [A,B]
  · apply congr_mod
    simp [minus_one,← Int.natCast_ediv]

def operation {n} (m : ℕ) (j : Fin n) (v w : Fin n → ℕ) (i : Fin n) : ℕ × ℕ :=
  let p := v j; let t := w j; let g := p.gcd t
  if t=0 then (v i,w i) else if i<j then (0,0) else if i=j then (g,0) else
    tail m ((p.gcdA t:ℤ):ZMod m).val ((p.gcdB t:ℤ):ZMod m).val (t/g) (p/g) (v i) (w i)

theorem operation_correct {m n : ℕ} [NeZero m] (j : Fin n) (v w : Fin n → ℕ) (hp : 0 < v j)
    (h0 : ∀ i < j, v i=0 ∧ w i=0) (i : Fin n) :
    let z := pivotPair (m:ℤ) j (signedColumn v) (signedColumn w)
    let a := operation m j v w i
    z.1.get i = (a.1:ℤ) ∧ z.2.get i = (a.2:ℤ) := by
  intro z a
  by_cases ht : w j=0
  · simp [z,a,pivotPair,operation,signedColumn,ht]
  by_cases hi : i<j
  · obtain ⟨hx,hy⟩ := h0 i hi
    simp [z,a,pivotPair,operation,signedColumn,ht,hi,trim,hx,hy]
  by_cases he : i=j
  · subst i
    have eq := pivot_row (m:ℤ) j (signedColumn v) (signedColumn w) (by simpa [signedColumn] using hp)
    simpa [z,a,operation,signedColumn,ht] using eq
  have hji := lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm he)
  obtain ⟨hc,hd⟩ := tail_correct (m:=m) (v j) (w j) (v i) (w i)
  simpa [z,a,operation,pivotPair,signedColumn,ht,hi,he,trim,hji,Int.gcdA,Int.gcdB,Int.gcd,← Int.natCast_ediv] using And.intro hc.symm hd.symm

/-- 0 modulus, 1 its predecessor, 2 and 3 Bézout residues, 4 and 5 divided pivot
entries, 6 and 7 tail entries. The two output coordinates are on ports 8 and 9. -/
def tailCode : List (BitRegisterCode.Instr 11) :=
  [⟨.mul,2,6,8⟩,⟨.mul,3,7,10⟩,⟨.add,8,10,8⟩,⟨.rem,0,8,8⟩,
   ⟨.mul,1,4,9⟩,⟨.mul,9,6,9⟩,⟨.mul,5,7,10⟩,⟨.add,9,10,9⟩,⟨.rem,0,9,9⟩]
theorem tail_program {m : ℕ} [NeZero m] (a b t' p' v w : ℕ)
    (h : ∀ j ∈ [a,b,t',p',v,w], j ≤ m) (r : Regs) :
    let input : BitRegisterBank.Vars 11 := ![m,m-1,a,b,t',p',v,w,0,0,0]
    ∃ n rf z, n ≤ 1000^(tailCode.length+1)*(m.size+2)^2 ∧
      Eval (compile tailCode) n ⟨r,frame input⟩ ⟨rf,frame z⟩ ∧
      (z 8,z 9) = tail m a b t' p' v w := by
  intro input
  have hm := Nat.pos_of_ne_zero (NeZero.ne m)
  have hv : Valid tailCode input := by
    simp [Valid,tailCode,BitRegisterCode.Instr.step,Op.Valid,Function.update_apply,input,hm]
  have hs (j : Fin 11) : (input j).size ≤ m.size := by
    apply Nat.size_le_size; fin_cases j <;> simp [input] <;> apply h <;> simp
  obtain ⟨n,rf,hn,he⟩ := run_eval _ input r m.size hs hv
  exact ⟨n,rf,_,hn,he,rfl⟩
end DetDLP.UnsignedHermitePivot
end

section

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

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem instruction_step (q : Coeff) (hm : 0 < q.m) (x y s t w : ℕ) :
    let f := q.row (x%q.radix,y%q.radix)
    Valid stepCode (data q x y s t w) ∧
      run stepCode (data q x y s t w) =
        data q (x/q.radix) (y/q.radix) (s+w*f.1) (t+w*f.2) (w*q.radix) := by
  intro f
  have hr : 0 < q.radix := Nat.succ_pos _
  constructor
  · simp [Valid,stepCode,Op.Valid,BitRegisterCode.Instr.step,Function.update_apply,data,hm,hr]
  · funext i; fin_cases i <;> rfl

private theorem pack_cons (b : ℕ) (z : ℕ × ℕ) (zs : List (ℕ × ℕ)) :
    pack b (z::zs) = (z.1+b*(pack b zs).1,z.2+b*(pack b zs).2) := rfl

private theorem map_zero (q : Coeff) (zs : List (ℕ × ℕ)) (h : pack q.radix zs = (0,0)) :
    pack q.radix (zs.map q.row) = (0,0) := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    have hb : 0 < q.radix := Nat.succ_pos _
    rw [pack_cons, Prod.mk.injEq] at h
    obtain ⟨hz₁,hp₁⟩ := Nat.add_eq_zero_iff.mp h.1
    obtain ⟨hz₂,hp₂⟩ := Nat.add_eq_zero_iff.mp h.2
    have hs := ih (Prod.ext ((Nat.mul_eq_zero.mp hp₁).resolve_left hb.ne') ((Nat.mul_eq_zero.mp hp₂).resolve_left hb.ne'))
    simp [List.map_cons,pack_cons,hs,Coeff.row,hz₁,hz₂]

private theorem packed_lt (b : ℕ) (hb : 1<b) (zs : List (ℕ × ℕ))
    (hz : ∀ z ∈ zs, z.1<b ∧ z.2<b) :
    (pack b zs).1 < b^zs.length ∧ (pack b zs).2 < b^zs.length := by
  constructor
  · simpa [pack] using (Nat.ofDigits_lt_base_pow_length (l:=zs.map Prod.fst) hb
      (by simpa using fun z h => (hz z h).1))
  · simpa [pack] using (Nat.ofDigits_lt_base_pow_length (l:=zs.map Prod.snd) hb
      (by intro x hx; obtain ⟨z,hz',rfl⟩ := List.mem_map.mp hx; exact (hz z hz').2))

/-- The row pass works from the least significant digit upwards and can stop
early when both remaining columns vanish. The source code is independent of
the number of rows and of the modulus. -/
private theorem loop (q : Coeff) (hm : 0<q.m) (N : ℕ)
    (hc : ∀ z ∈ [q.m,q.radix,q.a,q.b,q.c,q.d], z ≤ N)
    (zs : List (ℕ × ℕ)) (hz : ∀ z ∈ zs, z.1<q.radix ∧ z.2<q.radix)
    (s t w : ℕ) (hs : s<w) (ht : t<w) (hw : w*q.radix^zs.length ≤ N)
    (r : Regs) (hg : r 1 = decide ((pack q.radix zs).1+(pack q.radix zs).2 ≠ 0)) :
    let h := pack q.radix zs
    let f := pack q.radix (zs.map q.row)
    ∃ k rf w', k ≤ zs.length*(1000^(stepCode.length+1)*((2*N).size+2)^2+2)+1 ∧
      w ≤ w' ∧ w' ≤ N ∧
      Eval (.while 1 body) k ⟨r,frame (data q h.1 h.2 s t w)⟩
        ⟨rf,frame (data q 0 0 (s+w*f.1) (t+w*f.2) w')⟩ := by
  induction zs generalizing s t w r with
  | nil =>
    simp only [List.length_nil,pow_zero,mul_one] at hw
    exact ⟨1,r,w,by simp,le_rfl,hw,by simpa [pack] using
      (Eval.while_false (body:=body) (a:=⟨r,frame (data q 0 0 s t w)⟩) (by simpa [pack] using hg) )⟩
  | cons z zs ih =>
    intro h f
    have hrad : 1 < q.radix := by simp [Coeff.radix,hm]
    have hwp : 0 < w := by omega
    have hwpow : w*(q.radix*q.radix^zs.length) ≤ N := by simpa [pow_succ',mul_assoc] using hw
    have hww : w*q.radix ≤ N := (Nat.le_mul_of_pos_right _ (pow_pos (by omega : 0<q.radix) _)).trans (by simpa [mul_assoc] using hwpow)
    have hwN : w ≤ N := (Nat.le_mul_of_pos_right _ (by omega : 0<q.radix)).trans hww
    have hxys := packed_lt q.radix hrad (z::zs) hz
    have hpN : q.radix^(z::zs).length ≤ N := (Nat.le_mul_of_pos_left _ hwp).trans hw
    have hx : h.1 ≤ N := hxys.1.le.trans hpN
    have hy : h.2 ≤ N := hxys.2.le.trans hpN
    by_cases hzero : h.1+h.2=0
    · have zero : h = (0,0) := Prod.ext (by omega) (by omega)
      have hmap : f = (0,0) := map_zero q _ zero
      change r 1 = decide (h.1+h.2 ≠ 0) at hg
      have hg0 : r 1=false := by simpa [hzero] using hg
      rw [zero,hmap]
      exact ⟨1,r,w,by omega,le_rfl,hwN,by simpa using (Eval.while_false (body:=body) (a:=⟨r,frame (data q 0 0 s t w)⟩) hg0)⟩
    have hv (j : Fin 17) : ((data q h.1 h.2 s t w) j).size ≤ (2*N).size := by
      apply Nat.size_le_size
      have haux {x : ℕ} (h : x ≤ N) : x ≤ 2*N := by omega
      fin_cases j <;> simp [data] <;> first | omega | apply haux; apply hc; simp
    have hzv := hz z (by simp)
    have hvt : ∀ t ∈ zs, t.1<q.radix ∧ t.2<q.radix := by intro t ht; exact hz t (by simp [ht])
    let tail := pack q.radix zs
    have ere : h = (z.1+q.radix*tail.1,z.2+q.radix*tail.2) := rfl
    have ex : h.1%q.radix=z.1 ∧ h.1/q.radix=tail.1 := by
      rw [ere]; simp [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hzv.1,Nat.add_mul_div_left _ _ hrad.le,Nat.div_eq_of_lt hzv.1]
    have ey : h.2%q.radix=z.2 ∧ h.2/q.radix=tail.2 := by
      rw [ere]; simp [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hzv.2,Nat.add_mul_div_left _ _ hrad.le,Nat.div_eq_of_lt hzv.2]
    obtain ⟨valid,eff⟩ := instruction_step q hm h.1 h.2 s t w
    obtain ⟨k,r₁,hk,ev⟩ := run_eval stepCode _ r (2*N).size hv valid
    rw [eff,ex.1,ex.2,ey.1,ey.2] at ev
    let s' := s+w*(q.row z).1
    let t' := t+w*(q.row z).2
    have es : s' < w*q.radix := by
      have hv := Nat.mod_lt (q.a*z.1+q.b*z.2) hm
      change s+w*((q.a*z.1+q.b*z.2)%q.m)<w*(q.m+1); nlinarith only [hs, Nat.mul_le_mul_left w hv.le]
    have et : t' < w*q.radix := by
      have hv := Nat.mod_lt (q.c*z.1+q.d*z.2) hm
      change t+w*((q.c*z.1+q.d*z.2)%q.m)<w*(q.m+1); nlinarith only [ht, Nat.mul_le_mul_left w hv.le]
    obtain ⟨r₂,eg,hg₂⟩ := peek_eval (11:Fin 17) (data q tail.1 tail.2 s' t' (w*q.radix)) r₁
    obtain ⟨k',rf,w',hk',hw₁,hw₂,ev'⟩ := ih hvt s' t' (w*q.radix) es et (by simpa [mul_assoc] using hwpow) r₂ hg₂
    have hyes : r 1=true := by change r 1 = decide (h.1+h.2≠0) at hg; rw [hg]; exact decide_eq_true hzero
    refine ⟨k+1+k'+1,rf,w',?_,(Nat.le_mul_of_pos_right _ hrad.le).trans hw₁,hw₂,?_⟩
    · rw [List.length_cons,Nat.succ_mul zs.length]; omega
    · have e₁ : s+w*f.1 = s'+w*q.radix*(pack q.radix (zs.map q.row)).1 := by
        change s+w*((q.row z).1+q.radix*(pack q.radix (zs.map q.row)).1)=_; dsimp only [s']; ring
      have e₂ : t+w*f.2 = t'+w*q.radix*(pack q.radix (zs.map q.row)).2 := by
        change t+w*((q.row z).2+q.radix*(pack q.radix (zs.map q.row)).2)=_; dsimp only [t']; ring
      rw [e₁,e₂]
      exact .while_true hyes (.seq ev eg) ev'
theorem scan_eval (q : Coeff) (hm : 0<q.m) (N : ℕ)
    (hc : ∀ z ∈ [q.m,q.radix,q.a,q.b,q.c,q.d], z ≤ N)
    (zs : List (ℕ × ℕ)) (hz : ∀ z ∈ zs, z.1<q.radix ∧ z.2<q.radix)
    (s t w : ℕ) (hs : s<w) (ht : t<w) (hw : w*q.radix^zs.length ≤ N) (r : Regs) :
    let h := pack q.radix zs
    let f := pack q.radix (zs.map q.row)
    ∃ k rf w', k ≤ zs.length*(1000^(stepCode.length+1)*((2*N).size+2)^2+2)+2 ∧
      w ≤ w' ∧ w' ≤ N ∧ Eval command k ⟨r,frame (data q h.1 h.2 s t w)⟩
        ⟨rf,frame (data q 0 0 (s+w*f.1) (t+w*f.2) w')⟩ := by
  intro h f
  obtain ⟨r',ep,hp⟩ := peek_eval (11:Fin 17) (data q h.1 h.2 s t w) r
  obtain ⟨k,rf,w',hk,h₁,h₂,el⟩ := loop q hm N hc zs hz s t w hs ht hw r' hp
  exact ⟨1+k,rf,w',by omega,h₁,h₂,.seq ep el⟩

def program := compiled command (port (6:Fin 17)) (port (8:Fin 17))
end DetDLP.BitColumnScan
end

section

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

private theorem project_step {m : ℕ} (s : BoundedExtendedEuclid.State) :
    encode (m := m) (BoundedExtendedEuclid.step s) = step (encode s) := by
  by_cases h : s.r = 0
  · simp [step,BoundedExtendedEuclid.step,encode,h]
  · simp [step,BoundedExtendedEuclid.step,encode,h,← Int.natCast_ediv]

private theorem project_run {m : ℕ} (k : ℕ) (s : BoundedExtendedEuclid.State) :
    encode (m := m) (BoundedExtendedEuclid.run k s) = run k (encode s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => rw [BoundedExtendedEuclid.run,run,ih,project_step]

/-- Only the two residues of the Bézout rows are needed in the tail-coordinate operations. -/
theorem result {m : ℕ} (x y : ℕ) (hx : x ≤ m) (hy : y ≤ m) :
    let z := run (2*(bitLen m+1)) (⟨x,y,1,0,0,1⟩ : Registers m)
    z.r=0 ∧ z.oldR=x.gcd y ∧ z.oldU=((x.gcdA y:ℤ):ZMod m) ∧ z.oldV=((x.gcdB y:ℤ):ZMod m) := by
  intro z
  obtain ⟨hr,hg,hu,hv,_⟩ := costed_xgcd x y hx hy
  have h := project_run (m := m) (2*(bitLen m+1)) (init x y)
  have hz : (⟨x,y,1,0,0,1⟩ : Registers m) = encode (init x y) := by simp [encode,init]
  dsimp only [z]; rw [hz,← h]
  exact ⟨hr,hg,congrArg Int.cast hu,congrArg Int.cast hv⟩

/-- An unsigned subtraction primitive with inputs in [0,m) computes the ring subtraction. -/
def subResidue (m x y : ℕ) := (x + m - y) % m

theorem subResidue_correct {m : ℕ} [NeZero m] (a b : ZMod m) :
    subResidue m a.val b.val = (a-b).val := by
  have h : b.val ≤ a.val+m := by have hb := b.val_lt; omega
  have he : (((a.val+m-b.val:ℕ):ZMod m)) = a-b := by
    rw [Nat.cast_sub h,Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val,ZMod.natCast_self,add_zero]
  rw [← he]; exact (ZMod.val_natCast m _).symm

end DetDLP.ModularBezout
end

section

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

private theorem residue {m : ℕ} [NeZero m] (a b : ZMod m) (q : ℕ) :
    (a.val + ((m-1)*q)*b.val)%m = (a - (q:ZMod m)*b).val := by
  have hm := Nat.pos_of_ne_zero (NeZero.ne m)
  have he : ((m-1:ℕ):ZMod m) = -1 := by rw [Nat.cast_sub (by omega),ZMod.natCast_self,Nat.cast_one,zero_sub]
  rw [← ZMod.val_natCast]
  simp [Nat.cast_add,Nat.cast_mul,he,sub_eq_add_neg]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem step_correct (m : ℕ) [NeZero m] (s : R m) (hr : s.r ≠ 0) :
    Valid stepCode (data m s) ∧ run stepCode (data m s) = data m (ModularBezout.step s) := by
  have hmp : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hrp := Nat.pos_of_ne_zero hr
  constructor
  · simp [Valid,stepCode,Op.Valid,BitRegisterCode.Instr.step,Function.update_apply,data,hrp,hmp]
  · funext i; fin_cases i <;>
      simp [run,stepCode,BitRegisterCode.Instr.step,Function.update_apply,data,Op.eval,ModularBezout.step,hr,residue]

private def body := (compile stepCode).seq (peek (2:Fin 13))
private def command := (peek (2:Fin 13)).seq (.while 1 body)

private theorem body_eval (m : ℕ) [NeZero m] (s : R m) (r : Regs) (hr : s.r ≠ 0)
    (h1 : s.r ≤ m) (h2 : s.oldR ≤ m) :
    ∃ t rf, t ≤ 1000^(stepCode.length+1)*(m.size+2)^2+1 ∧
      Eval body t ⟨r,frame (data m s)⟩ ⟨rf,frame (data m (ModularBezout.step s))⟩ ∧
        rf 1 = decide ((ModularBezout.step s).r ≠ 0) := by
  obtain ⟨hv,he⟩ := step_correct m s hr
  have hw (j : Fin 13) : ((data m s) j).size ≤ m.size := by
    apply Nat.size_le_size; fin_cases j <;> simp [data,h1,h2,le_of_lt (ZMod.val_lt _)]
  obtain ⟨t,r₁,ht,et⟩ := run_eval stepCode (data m s) r m.size hw hv
  rw [he] at et
  obtain ⟨r₂,eg,hg⟩ := peek_eval (2:Fin 13) (data m (ModularBezout.step s)) r₁
  exact ⟨_,_,by omega,.seq et eg,hg⟩

private theorem run_zero {m} (k : ℕ) (s : R m) (hz : s.r=0) : ModularBezout.run k s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [ModularBezout.run,ModularBezout.step,hz] using ih

private theorem loop_eval (m k : ℕ) [NeZero m] (s : R m) (r : Regs)
    (h1 : s.r ≤ m) (h2 : s.oldR ≤ m) (hg : r 1 = decide (s.r ≠ 0))
    (hstop : (ModularBezout.run k s).r=0) :
    ∃ t rf, t ≤ k*(1000^(stepCode.length+1)*(m.size+2)^2+2)+1 ∧
      Eval (.while 1 body) t ⟨r,frame (data m s)⟩ ⟨rf,frame (data m (ModularBezout.run k s))⟩ := by
  induction k generalizing s r with
  | zero =>
    have hz : s.r=0 := hstop
    exact ⟨1,r,by omega,.while_false (by simpa [hz] using hg)⟩
  | succ k ih =>
    by_cases hz : s.r=0
    · rw [run_zero (k+1) s hz]
      exact ⟨1,r,by omega,.while_false (by simpa [hz] using hg)⟩
    obtain ⟨t,r₁,ht,he,hg₁⟩ := body_eval m s r hz h1 h2
    have h₁ : (ModularBezout.step s).r ≤ m := by simpa [ModularBezout.step,hz] using (Nat.mod_le s.oldR s.r).trans h2
    have h₂ : (ModularBezout.step s).oldR ≤ m := by simpa [ModularBezout.step,hz] using h1
    obtain ⟨v,rf,hh,ef⟩ := ih (ModularBezout.step s) r₁ h₁ h₂ hg₁ hstop
    refine ⟨_,_,?_,.while_true (by simpa [hz] using hg) he ef⟩
    rw [Nat.succ_mul]; omega

def program := compiled command (port (2:Fin 13)) (port (3:Fin 13))

theorem extended_trace (m : ℕ) [NeZero m] (x y : ℕ) (hx : x ≤ m) (hy : y ≤ m) (r : Regs) :
    let s : R m := ⟨x,y,1,0,0,1⟩
    ∃ (z : R m) (rf : Regs), z.r=0 ∧ z.oldR=x.gcd y ∧ z.oldU=((x.gcdA y:ℤ):ZMod m) ∧
      z.oldV=((x.gcdB y:ℤ):ZMod m) ∧
      RunsIn program (2*(bitLen m+1)*(1000^(stepCode.length+1)*(m.size+2)^2+2)+3)
        ⟨some program.entry,r,frame (data m s)⟩ ⟨none,rf,frame (data m z)⟩ := by
  intro s
  obtain ⟨hz,hd,hu,hv⟩ := ModularBezout.result x y hx hy
  obtain ⟨r₁,hpeek,hg⟩ := peek_eval (2:Fin 13) (data m s) r
  obtain ⟨t,rf,ht,he⟩ := loop_eval m (2*(bitLen m+1)) s r₁ hx hy hg hz
  have hh := compiled_halt_trace (.seq hpeek he) (port (2:Fin 13)) (port (3:Fin 13))
  exact ⟨_,rf,hz,hd,hu,hv,_,by omega,hh⟩
end DetDLP.BitExtendedEuclid
end

section

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

theorem square_quot (m : ℕ) (hm : 0 < m) : m*m/(m+1)=m-1 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have e : (k+1)*(k+1) = 1+(k+1+1)*k := by ring
  rw [e,Nat.add_mul_div_left _ _ (by omega),Nat.div_eq_of_lt (by omega : 1 < k+1+1)]
  simp

def prepared (m p t : ℕ) : Vars 13 := ![m,m-1,p,t,1,0,0,1,0,0,0,0,0]
def saved (e : Vars 13) (w : ℕ) : Vars 13 := Function.update (Function.update e 8 w) 9 1

def coefficients (m p t g a b : ℕ) : BitColumnScan.Coeff := ⟨m,a,b,(m-1)*(t/g),p/g⟩

set_option maxRecDepth 10000 in
private theorem prepare_ok (m w x y : ℕ) (hm : 0 < m) (hw : 0 < w) :
    let b := m+1
    let p := x/w%b
    let t := y/w%b
    let v := banks blank (io m w x y)
    Valid prepare v ∧ run prepare v = banks (prepared m p t) (staged m w x y p t (x/w/b) (y/w/b)) := by
  intro b p t v
  have hb : 0 < b := Nat.succ_pos _
  constructor
  · simp [prepare,Valid,cp,Op.Valid,BitRegisterCode.Instr.step,Function.update_apply]
    all_goals repeat' apply And.intro
    all_goals first | exact hw | exact hb | exact hm
  · have h : run prepare v = banks ![m,m*m/b,p,t,1,0,0,1,0,0,0,0,0] (staged m w x y p t (x/w/b) (y/w/b)) := by
      funext j; fin_cases j <;> rfl
    simpa only [b,square_quot m hm,prepared] using h

set_option maxRecDepth 10000 in
private theorem configure_ok (m w x y p t X Y : ℕ) (e : Vars 13)
    (hneg : e 1=m-1) (hg : 0 < e 3) :
    let q := coefficients m p t (e 3) (e 5) (e 7)
    let v := banks e (staged m w x y p t X Y)
    Valid configure v ∧ run configure v =
      banks (saved e w) (BitColumnScan.data q X Y (w*(e 3)) 0 (w*(m+1))) := by
  intro q v
  constructor
  · simp [configure,Valid,cp,erase,Op.Valid,BitRegisterCode.Instr.step,Function.update_apply]
    all_goals repeat first | constructor | exact hg
  · have h : run configure v = banks (saved e w)
        (BitColumnScan.data ⟨m,e 5,e 7,e 1*(t/e 3),p/e 3⟩ X Y (w*(e 3)) 0 (w*(m+1))) := by
      funext j; fin_cases j <;> rfl
    rw [hneg] at h; exact h

set_option maxRecDepth 10000 in
private theorem finish_ok (q : BitColumnScan.Coeff) (e : Vars 13) (w x y w' : ℕ) :
    let v := banks (saved e w) (BitColumnScan.data q 0 0 x y w')
    Valid finish v ∧ run finish v = banks blank (io q.m w x y) := by
  intro v
  constructor
  · simp [finish,Valid,cp,erase,Op.Valid]
  · funext j; fin_cases j <;> rfl

abbrev Bounded {n : ℕ} (v : Vars n) (N : ℕ) := ∀ j, v j ≤ N

theorem banks_bounded {e : Vars 13} {a : Vars 17} {N : ℕ}
    (h₁ : Bounded e N) (h₂ : Bounded a N) : Bounded (banks e a) N := by
  intro j; refine Fin.addCases (m:=13) (n:=17) (fun i => ?_) (fun i => ?_) j
  · simpa only [banks,Fin.addCases_left] using h₁ i
  · simpa only [banks,Fin.addCases_right] using h₂ i

theorem step_eval (c : List I) (v z : V) (r : Regs) (N : ℕ)
    (hv : Bounded v N) (h : Valid c v ∧ run c v=z) :
    ∃ k rf, k ≤ 1000^(c.length+1)*(N.size+2)^2 ∧ Eval (compile c) k ⟨r,frame v⟩ ⟨rf,frame z⟩ := by
  obtain ⟨k,rf,hk,he⟩ := run_eval c v r N.size (fun j => Nat.size_le_size (hv j)) h.1
  exact ⟨k,rf,hk,h.2 ▸ he⟩

noncomputable def matrix (m p t : ℕ) : BitColumnScan.Coeff :=
  coefficients m p t (p.gcd t) (((p.gcdA t:ℤ):ZMod m).val) (((p.gcdB t:ℤ):ZMod m).val)

theorem radix_digits (b w p X : ℕ) (hw : 0 < w) (hb : 0 < b) (hp : p < b) :
    (w*(p+b*X))/w%b=p ∧ (w*(p+b*X))/w/b=X := by
  rw [Nat.mul_div_cancel_left _ hw,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hp,
    Nat.add_mul_div_left _ _ hb,Nat.div_eq_of_lt hp,zero_add]
  exact ⟨rfl,rfl⟩

theorem digit_bound (b p X L : ℕ) (hp : p < b) (hX : X < L) : p+b*X < b*L := by
  have hh := Nat.mul_le_mul_left b (show X+1 ≤ L by omega)
  rw [Nat.mul_succ] at hh; omega

theorem packed_lt {q : BitColumnScan.Coeff} {rows : List (ℕ × ℕ)} (hm : 0 < q.m)
    (h : ∀ z ∈ rows, z.1 < q.radix ∧ z.2 < q.radix) :
    (BitColumnScan.pack q.radix rows).1 < q.radix^rows.length ∧ (BitColumnScan.pack q.radix rows).2 < q.radix^rows.length := by
  have hb : 1 < q.radix := by simp [BitColumnScan.Coeff.radix,hm]
  constructor
  · simpa [BitColumnScan.pack] using (Nat.ofDigits_lt_base_pow_length (l:=rows.map Prod.fst) hb
      (by intro x hx; obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx; exact (h z hz).1))
  · simpa [BitColumnScan.pack] using (Nat.ofDigits_lt_base_pow_length (l:=rows.map Prod.snd) hb
      (by intro x hx; obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx; exact (h z hz).2))

def overhead := 1000^(prepare.length+1)+1000^(configure.length+1)+1000^(finish.length+1)+
  1000^(BitColumnScan.stepCode.length+1)+1000^(BitExtendedEuclid.stepCode.length+1)+10

/-- The program starts and finishes with both scratch banks clean. Its arguments
are two radix-packed columns whose coordinates below the current address vanish. -/
theorem pivot_eval (m : ℕ) [NeZero m] (hm : 2 ≤ m) (p t w : ℕ)
    (hp : 0 < p) (hpm : p ≤ m) (htm : t ≤ m) (hw : 0 < w)
    (rows : List (ℕ × ℕ)) (hd : ∀ z ∈ rows, z.1 ≤ m ∧ z.2 ≤ m) (N : ℕ)
    (hcap : w*(m+1)^(rows.length+1) ≤ N) (hsquare : (m+1)^2 ≤ N) (r : Regs) :
    let b := m+1
    let q := matrix m p t
    let u := BitColumnScan.pack b rows
    let v := BitColumnScan.pack b (rows.map q.row)
    let g := p.gcd t
    ∃ k rf, k ≤ 4*overhead*(bitLen m+rows.length+3)*((2*N).size+2)^2 ∧
      Eval command k
        ⟨r,frame (banks blank (io m w (w*(p+b*u.1)) (w*(t+b*u.2))))⟩
        ⟨rf,frame (banks blank (io m w (w*g+w*b*v.1) (w*b*v.2)))⟩ := by
  intro b q u v g
  let X := w*(p+b*u.1)
  let Y := w*(t+b*u.2)
  have hb : 1 < b := by dsimp [b]; omega
  have hm0 : 0 < m := by omega
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hp
  have hgm : g ≤ m := (Nat.gcd_le_left t hp).trans hpm
  have hbr : q.radix=b := rfl
  have hconst : b ≤ N := (Nat.le_self_pow (by decide : 2 ≠ 0) _).trans hsquare
  have hmn : m ≤ N := by omega
  have hlen : b^rows.length ≤ N := by
    have h1 : b^rows.length ≤ b^(rows.length+1) := Nat.pow_le_pow_right (by omega) (by omega)
    exact h1.trans ((Nat.le_mul_of_pos_left _ hw).trans hcap)
  have hww : w*b ≤ N := by
    have hpow := Nat.pow_le_pow_right (n:=b) (by omega : 0 < b) (show 1 ≤ rows.length+1 by omega)
    rw [pow_one] at hpow
    exact (Nat.mul_le_mul_left w hpow).trans hcap
  have hwN : w ≤ N := (Nat.le_mul_of_pos_right _ (by omega : 0 < b)).trans hww
  have hdigits : ∀ z ∈ rows,z.1 < q.radix ∧ z.2 < q.radix := by
    intro z hz; obtain ⟨ha,hb'⟩:=hd z hz; change z.1 < m+1 ∧ z.2 < m+1; omega
  have hu := packed_lt (q:=q) hm0 hdigits
  change u.1 < b^rows.length ∧ u.2 < b^rows.length at hu
  have bound (p X : ℕ) (hp : p < b) (hX : X < b^rows.length) : w*(p+b*X) ≤ N := by
    apply le_trans (Nat.mul_le_mul_left w (digit_bound b p X _ hp hX).le)
    simpa only [pow_succ'] using hcap
  have hX : X ≤ N := bound p u.1 (by omega) hu.1
  have hY : Y ≤ N := bound t u.2 (by omega) hu.2
  have hu₁ := hu.1.le.trans hlen
  have hu₂ := hu.2.le.trans hlen
  have cutX := radix_digits b w p u.1 hw (by omega) (by omega)
  have cutY := radix_digits b w t u.2 hw (by omega) (by omega)
  let side := staged m w X Y p t u.1 u.2
  let init : ModularBezout.Registers m := ⟨p,t,1,0,0,1⟩
  have one : (1:ZMod m).val=1 := by simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (show 1 < m by omega)
  have hprepared : prepared m p t = BitExtendedEuclid.data m init := by
    simp [prepared,BitExtendedEuclid.data,init,one]
  have first := prepare_ok m w X Y hm0 hw
  dsimp only at first
  change X/w%b=p ∧ X/w/b=u.1 at cutX
  change Y/w%b=t ∧ Y/w/b=u.2 at cutY
  rw [cutX.1,cutX.2,cutY.1,cutY.2,hprepared] at first
  have hmW : Bounded (banks blank (io m w X Y)) N := banks_bounded (by simp [Bounded,blank])
    (by intro i; fin_cases i <;> simp [io] <;> omega)
  obtain ⟨n₁,r₁,c₁,e₁⟩ := step_eval prepare _ _ r N hmW first
  obtain ⟨z,r₂,hz,hg',ha,hb',n₂,c₂,tr₂⟩ := BitExtendedEuclid.extended_trace m p t hpm htm r₁
  have e₂ := call_left BitExtendedEuclid.program (BitExtendedEuclid.data m init) (BitExtendedEuclid.data m z) side r₁ r₂ n₂ tr₂
  let e := BitExtendedEuclid.data m z
  have eg : e 3=g := hg'
  have ec : coefficients m p t (e 3) (e 5) (e 7) = q := by
    change coefficients m p t z.oldR z.oldU.val z.oldV.val = _
    rw [hg',ha,hb']; rfl
  have eN : Bounded e N := by
    intro i; fin_cases i <;> simp [e,BitExtendedEuclid.data,hz,hg',le_of_lt (ZMod.val_lt _)] <;>
      first | omega | exact (ZMod.val_lt _).le.trans hmn
  have sideN : Bounded side N := by
    intro i; fin_cases i <;> simp [side,staged] <;> omega
  have conf := configure_ok m w X Y p t u.1 u.2 e rfl (eg.symm ▸ hg)
  dsimp only at conf
  rw [ec,eg] at conf
  obtain ⟨n₃,r₃,c₃,e₃⟩ := step_eval configure _ _ r₂ N (banks_bounded eN sideN) conf
  have hc : ∀ z ∈ [q.m,q.radix,q.a,q.b,q.c,q.d], z ≤ N := by
    have htdiv := Nat.div_le_self t g
    have hpdiv := Nat.div_le_self p g
    have hprod : (m-1)*(t/g) ≤ N := (Nat.mul_le_mul (show m-1 ≤ b by omega) (show t/g ≤ b by omega)).trans (by simpa only [pow_two] using hsquare)
    have ha' := ZMod.val_lt (((p.gcdA t:ℤ):ZMod m))
    have hb'' := ZMod.val_lt (((p.gcdB t:ℤ):ZMod m))
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hmn
    · exact hconst
    · exact ha'.le.trans hmn
    · exact hb''.le.trans hmn
    · exact hprod
    · exact hpdiv.trans (hpm.trans hmn)
  have hwg : w*g < w*b := Nat.mul_lt_mul_of_pos_left (by omega) hw
  obtain ⟨n₄,r₄,w',c₄,_,hwn',ev₄⟩ := BitColumnScan.scan_eval q hm0 N hc rows hdigits
    (w*g) 0 (w*b) hwg (by positivity) (by simpa only [hbr,pow_succ',mul_assoc] using hcap) r₃
  let P := w*g+w*b*v.1
  let Q := w*b*v.2
  have tr₄ := compiled_halt_trace ev₄ (port (6:Fin 17)) (port (8:Fin 17))
  simp only [zero_add] at tr₄
  have e₄ := call_right BitColumnScan.program _ _ (saved e w) r₃ r₄ (n₄+1) tr₄
  have hfd : ∀ u ∈ rows.map q.row,u.1 < q.radix ∧ u.2 < q.radix := by
    intro a ha; obtain ⟨z,_,rfl⟩ := List.mem_map.mp ha
    exact ⟨(Nat.mod_lt _ hm0).trans_le (by omega : m ≤ b),(Nat.mod_lt _ hm0).trans_le (by omega : m ≤ b)⟩
  have hfv := packed_lt (q:=q) hm0 hfd
  simp only [List.length_map,hbr] at hfv
  have hP : P ≤ N := by
    have := bound g v.1 (by omega) hfv.1
    simpa [P,Nat.mul_add,Nat.mul_assoc] using this
  have hQ : Q ≤ N := by
    have := bound 0 v.2 (by omega) hfv.2
    simpa [Q,Nat.mul_assoc] using this
  have savedN : Bounded (saved e w) N := by
    intro i; by_cases he : i=9
    · subst i; simp [saved]; omega
    by_cases hw : i=8
    · subst i; simp [saved,hwN]
    simpa [saved,he,hw] using eN i
  have fsN : Bounded (BitColumnScan.data q 0 0 P Q w') N := by
    intro i; fin_cases i <;> simp [BitColumnScan.data] <;> first | assumption | apply hc; simp
  obtain ⟨n₅,rf,c₅,e₅⟩ := step_eval finish _ _ r₄ N (banks_bounded savedN fsN) (finish_ok q e w P Q w')
  refine ⟨_,rf,?_,.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))⟩
  let S := ((2*N).size+2)^2
  have hNsize := Nat.size_le_size (show N ≤ 2*N by omega)
  have hmSize := Nat.size_le_size (show m ≤ 2*N by omega)
  have hsq1 : (N.size+2)^2 ≤ S := Nat.pow_le_pow_left (by omega) _
  have hsq2 : (m.size+2)^2 ≤ S := Nat.pow_le_pow_left (by omega) _
  have c₁' := c₁.trans (Nat.mul_le_mul_left _ hsq1)
  have c₃' := c₃.trans (Nat.mul_le_mul_left _ hsq1)
  have c₅' := c₅.trans (Nat.mul_le_mul_left _ hsq1)
  have c₂' := (Nat.mul_le_mul_left (2*(bitLen m+1))
    (Nat.add_le_add_right (Nat.mul_le_mul_left (1000^(BitExtendedEuclid.stepCode.length+1)) hsq2) 2))
  change n₄ ≤ rows.length*(1000^(BitColumnScan.stepCode.length+1)*S+2)+2 at c₄
  change _ ≤ 4*overhead*(bitLen m+rows.length+3)*S
  have hS : 1 ≤ S := Nat.one_le_pow _ _ (by omega)
  dsimp only [overhead]
  generalize 1000^(prepare.length+1) = A at *
  generalize 1000^(configure.length+1) = B at *
  generalize 1000^(finish.length+1) = C at *
  generalize 1000^(BitColumnScan.stepCode.length+1) = D at *
  generalize 1000^(BitExtendedEuclid.stepCode.length+1) = E at *
  nlinarith only [c₁',c₂,c₂',c₃',c₄,c₅',Nat.mul_le_mul_left (bitLen m+1) hS,
    Nat.mul_le_mul_left rows.length hS,hS,Nat.zero_le (A*S),Nat.zero_le (B*S),Nat.zero_le (C*S)]

end DetDLP.BitPackedPivot
end

section
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

private theorem before_ok (m w x y : ℕ) (hm : 0 < m) (hw : 0 < w) (hp : 0 < x/w%(m+1)) :
    let b := m+1
    let p := x/w%b
    let t := y/w%b
    let v := banks blank (io m w x y)
    Valid before v ∧ run before v = banks (hold m w x y p t)
      (BitColumnScan.data (matrix m p t) (y/w/b) (x/w/b) (y%w+w*(t%p)) 0 (w*b)) := by
  intro b p t v
  have hb : 0 < b := Nat.succ_pos _
  constructor
  · simp [before,Valid,cp,erase,Op.Valid,BitRegisterCode.Instr.step,Function.update_apply,Op.eval]
    all_goals repeat' apply And.intro
    all_goals first | exact hp | exact hw | exact hb | exact hm
  · have h : run before v = banks ![x,w,1,m*m/b,y/w,p,t,t%p,t/p,y%w,0,0,0]
        (BitColumnScan.data ⟨m,1,(m*m/b)*(t/p),0,0⟩ (y/w/b) (x/w/b) (y%w+w*(t%p)) 0 (w*b)) := by
      funext j; fin_cases j <;> rfl
    simpa only [b,BitPackedPivot.square_quot m hm,hold,matrix] using h

private theorem after_ok (m w x y p t X Y w' : ℕ) :
    let v := banks (hold m w x y p t) (BitColumnScan.data (matrix m p t) 0 0 X Y w')
    Valid after v ∧ run after v = banks blank (io m w x X) := by
  intro v
  constructor
  · simp [after,Valid,cp,erase,Op.Valid]
  · funext j; fin_cases j <;> rfl

def overhead := 1000^(before.length+1)+1000^(BitColumnScan.stepCode.length+1)+1000^(after.length+1)+10

theorem fixed_eval (m p t w pre : ℕ) (hm : 2 ≤ m) (hp : 0 < p) (hpm : p ≤ m) (htm : t ≤ m)
    (hpre : pre < w) (rows : List (ℕ × ℕ)) (hd : ∀ z ∈ rows, z.1 ≤ m ∧ z.2 ≤ m) (N : ℕ)
    (hcap : w*(m+1)^(rows.length+1) ≤ N) (hsq : (m+1)^2 ≤ N) (r : Regs) :
    let b := m+1
    let q := matrix m p t
    let u := BitColumnScan.pack b rows
    let v := BitColumnScan.pack b (rows.map q.row)
    let x := w*(p+b*u.2)
    let y := pre+w*(t+b*u.1)
    ∃ k rf, k ≤ overhead*(rows.length+3)*((2*N).size+2)^2 ∧
      Eval command k ⟨r,frame (banks blank (io m w x y))⟩
        ⟨rf,frame (banks blank (io m w x (pre+w*(t%p)+w*b*v.1)))⟩ := by
  intro b q u v x y
  have hm0 : 0 < m := by omega
  have hb : 1 < b := by dsimp [b]; omega
  have hw : 0 < w := by omega
  have hbr : q.radix=b := rfl
  have hbn : b ≤ N := (Nat.le_self_pow (by decide : 2 ≠ 0) _).trans hsq
  have hmn : m ≤ N := by omega
  have hwN : w ≤ N := (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)).trans hcap
  have hww : w*b ≤ N := by
    have hh := Nat.pow_le_pow_right (by omega : 0 < b) (show 1 ≤ rows.length+1 by omega)
    rw [pow_one] at hh; exact (Nat.mul_le_mul_left w hh).trans hcap
  have hdi : ∀ z ∈ rows,z.1 < q.radix ∧ z.2 < q.radix := by
    intro z hz; obtain ⟨ha,hb'⟩:=hd z hz; change z.1 < m+1 ∧ z.2 < m+1; omega
  have hlen : b^rows.length ≤ N := (Nat.pow_le_pow_right (by omega) (show rows.length ≤ rows.length+1 by omega)).trans
    ((Nat.le_mul_of_pos_left _ hw).trans hcap)
  have hu := BitPackedPivot.packed_lt (q:=q) hm0 hdi
  change u.1 < b^rows.length ∧ u.2 < b^rows.length at hu
  have bound (pre' a A : ℕ) (hpre' : pre' < w) (ha : a < b) (hA : A < b^rows.length) :
      pre'+w*(a+b*A) ≤ N := by
    have h := BitPackedPivot.digit_bound w pre' (a+b*A) (b*b^rows.length) hpre'
      (BitPackedPivot.digit_bound b a A _ ha hA)
    exact h.le.trans (by simpa only [pow_succ'] using hcap)
  have hx : x ≤ N := by simpa [x] using bound 0 p u.2 hw (by omega) hu.2
  have hy : y ≤ N := bound pre t u.1 hpre (by omega) hu.1
  have ep : x/w%b=p ∧ x/w/b=u.2 := BitPackedPivot.radix_digits _ _ _ _ hw (by omega) (by omega)
  have eqy : y/w=t+b*u.1 := by dsimp [y]; rw [Nat.add_mul_div_left _ _ hw,Nat.div_eq_of_lt hpre,zero_add]
  have et : y/w%b=t ∧ y/w/b=u.1 := by rw [eqy,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by omega : t < b),
    Nat.add_mul_div_left _ _ (by omega : 0 < b),Nat.div_eq_of_lt (by omega : t < b),zero_add]; exact ⟨rfl,rfl⟩
  have el : y%w=pre := by dsimp [y]; rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hpre]
  have e₁ := before_ok m w x y hm0 hw (ep.1.symm ▸ hp)
  dsimp only at e₁; rw [ep.1,ep.2,et.1,et.2,el] at e₁
  have hstart : Bounded (banks blank (io m w x y)) N := BitPackedPivot.banks_bounded (by simp [Bounded,blank])
    (by intro i; fin_cases i <;> simp [io] <;> omega)
  obtain ⟨n₁,r₁,c₁,t₁⟩ := BitPackedPivot.step_eval before _ _ r N hstart e₁
  have hpdiv := Nat.div_le_self t p
  have hco : (m-1)*(t/p) ≤ N := (Nat.mul_le_mul (show m-1 ≤ b by omega) (show t/p ≤ b by omega)).trans (by simpa [pow_two] using hsq)
  have hc : ∀ z ∈ [q.m,q.radix,q.a,q.b,q.c,q.d], z ≤ N := by
    intro z hz; simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> first | exact hmn | exact hbn | exact hco | exact Nat.zero_le _ | exact (by change 1 ≤ N; omega)
  have htp := Nat.mod_lt t hp
  have hfirst : pre+w*(t%p) < w*b := BitPackedPivot.digit_bound w pre _ b hpre (by omega)
  obtain ⟨n₂,r₂,w',c₂,_,hw',ev⟩ := BitColumnScan.scan_eval q hm0 N hc rows hdi (pre+w*(t%p)) 0 (w*b)
    hfirst (by positivity) (by simpa only [hbr,pow_succ',mul_assoc] using hcap) r₁
  have tr := compiled_halt_trace ev (port (6:Fin 17)) (port (8:Fin 17))
  simp only [zero_add] at tr
  have t₂ := call_right BitColumnScan.program _ _ (hold m w x y p t) r₁ r₂ (n₂+1) tr
  let X := pre+w*(t%p)+w*b*v.1
  let Y := w*b*v.2
  have hvd : ∀ z ∈ rows.map q.row, z.1 < q.radix ∧ z.2 < q.radix := by
    intro z hz; obtain ⟨s,_,rfl⟩ := List.mem_map.mp hz
    exact ⟨(Nat.mod_lt _ hm0).trans_le (by omega : m ≤ b),(Nat.mod_lt _ hm0).trans_le (by omega : m ≤ b)⟩
  have hv := BitPackedPivot.packed_lt (q:=q) hm0 hvd
  simp only [List.length_map,hbr] at hv
  have hX : X ≤ N := by
    simpa [X,Nat.mul_add,Nat.mul_assoc,Nat.add_assoc] using bound pre (t%p) v.1 hpre (by omega) hv.1
  have hY : Y ≤ N := by simpa [Y,Nat.mul_assoc] using bound 0 0 v.2 hw (by omega) hv.2
  have holds : Bounded (hold m w x y p t) N := by
    have := Nat.div_le_self y w; have := Nat.mod_le t p; have := Nat.mod_le y w
    intro i; fin_cases i <;> simp [hold] <;> omega
  have endB : Bounded (BitColumnScan.data q 0 0 X Y w') N := by
    intro i; fin_cases i <;> simp [BitColumnScan.data] <;> first | assumption | apply hc; simp
  obtain ⟨n₃,rf,c₃,t₃⟩ := BitPackedPivot.step_eval after _ _ r₂ N (BitPackedPivot.banks_bounded holds endB)
    (after_ok m w x y p t X Y w')
  refine ⟨_,rf,?_,.seq t₁ (.seq t₂ t₃)⟩
  let S := ((2*N).size+2)^2
  have hW : (N.size+2)^2 ≤ S := Nat.pow_le_pow_left (by have := Nat.size_le_size (show N ≤ 2*N by omega); omega) _
  have hS : 1 ≤ S := Nat.one_le_pow _ _ (by omega)
  have c₁' := c₁.trans (Nat.mul_le_mul_left _ hW)
  have c₃' := c₃.trans (Nat.mul_le_mul_left _ hW)
  change n₂ ≤ rows.length*(1000^(BitColumnScan.stepCode.length+1)*S+2)+2 at c₂
  change _ ≤ overhead*(rows.length+3)*S
  unfold overhead
  generalize 1000^(before.length+1)=A at *
  generalize 1000^(after.length+1)=B at *
  generalize 1000^(BitColumnScan.stepCode.length+1)=C at *
  nlinarith only [c₁',c₂,c₃',Nat.mul_le_mul_left rows.length hS,hS]
end DetDLP.BitFixedColumn
end

section

namespace DetDLP.PackedHermiteRefinement
open BorderedHermite UnsignedHermitePivot

abbrev Pair := ℕ × ℕ
def rowsAt (pre : List Pair) (z : Pair) (tail : List Pair) := pre ++ z::tail
noncomputable def signed {n : ℕ} (u : Fin n → ℕ) : Column n := signedColumn u

private theorem get_low (pre : List Pair) (z : Pair) (tail : List Pair) (i : ℕ) (h : i < pre.length) :
    (rowsAt pre z tail)[i]'(by simp [rowsAt]; omega)=pre[i] := by
  exact List.getElem_append_left h

private theorem get_mid (pre : List Pair) (z : Pair) (tail : List Pair) :
    (rowsAt pre z tail)[pre.length]'(by simp [rowsAt])=z := by
  unfold rowsAt at *; rw [List.getElem_append_right (by omega)]; simp

private theorem get_hi (pre : List Pair) (z : Pair) (tail : List Pair) (i : ℕ)
    (hi : pre.length < i) (h : i < (rowsAt pre z tail).length) :
    (rowsAt pre z tail)[i] = tail[i-pre.length-1]'(by simp [rowsAt] at h; omega) := by
  unfold rowsAt at *; rw [List.getElem_append_right (by omega)]
  rw [List.getElem_cons, dif_neg (show i-pre.length ≠ 0 by omega)]

/-- Pair two lists of natural coordinates and view them as signed columns. -/
def column (s : List Pair) (f : Pair → ℕ) := signedColumn (fun i : Fin s.length => f (s.get i))

theorem row_eq {m : ℕ} [NeZero m] (hm : 2 ≤ m) (p t : ℕ) (hp : 0 < p)
    (z : Pair) (hz : z.1 < m ∧ z.2 < m) :
    let q := BitPackedPivot.matrix m p t
    q.row z = if t=0 then z else
      tail m (((p.gcdA t:ℤ):ZMod m).val) (((p.gcdB t:ℤ):ZMod m).val) (t/(p.gcd t)) (p/(p.gcd t)) z.1 z.2 := by
  intro q
  by_cases ht : t=0
  · subst t
    have ho : (1:ZMod m).val=1 := by simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (show 1 < m by omega)
    simp [q,BitPackedPivot.matrix,BitPackedPivot.coefficients,BitColumnScan.Coeff.row,Nat.gcdA_zero_right hp.ne',
      Nat.gcdB_zero_right hp.ne',ho,Nat.div_self hp,Nat.mod_eq_of_lt hz.1,Nat.mod_eq_of_lt hz.2]
  · rw [if_neg ht]; rfl

/-- The digit pass agrees coordinate-for-coordinate with the signed bounded
Hermite pivot, including a zero elimination coordinate. -/
theorem pivot (m j p t : ℕ) [NeZero m] (hm : 2 ≤ m) (hp : 0 < p)
    (s : List Pair) (hs : ∀ z ∈ s,z.1 < m ∧ z.2 < m) :
    let pre := List.replicate j ((0,0):Pair)
    let a := rowsAt pre (p,t) s
    let z := rowsAt pre (p.gcd t,0) (s.map (BitPackedPivot.matrix m p t).row)
    let J : Fin a.length := ⟨j,by simp [a,rowsAt,pre]⟩
    let result := pivotPair (m:ℤ) J (column a Prod.fst) (column a Prod.snd)
    ∀ i : Fin a.length, let k : Fin z.length := ⟨i.val,by simpa [a,z,rowsAt] using i.isLt⟩
      result.1.get i = ((z.get k).1:ℤ) ∧ result.2.get i = ((z.get k).2:ℤ) := by
  intro pre a z J result i k
  let x (l : Fin a.length) := (a.get l).1
  let y (l : Fin a.length) := (a.get l).2
  have lp : pre.length=j := by simp [pre]
  have getJ : a.get J = (p,t) := by
    have hh := get_mid pre (p,t) s
    simpa only [a,J,List.get_eq_getElem,lp] using hh
  have zero (l : Fin a.length) (hl : l < J) : x l=0 ∧ y l=0 := by
    have hlow : l.val < pre.length := by change l.val < j at hl; omega
    have hh := get_low pre (p,t) s l.val hlow
    change (a.get l).1=0 ∧ (a.get l).2=0
    simp only [a,List.get_eq_getElem,hh,pre,List.getElem_replicate]
    exact ⟨trivial,trivial⟩
  have hjx : x J=p := congrArg Prod.fst getJ
  have hjy : y J=t := congrArg Prod.snd getJ
  have eq := operation_correct (m:=m) J x y (hjx.symm ▸ hp) zero i
  change result.1.get i = _ ∧ result.2.get i = _ at eq
  have op : operation m J x y i = z.get k := by
    by_cases hl : i < J
    · obtain ⟨h₁,h₂⟩ := zero i hl
      have hlow : i.val < pre.length := by change i.val < j at hl; omega
      have hh := get_low pre (p.gcd t,0) (s.map (BitPackedPivot.matrix m p t).row) i.val hlow
      have ho : z.get k=(0,0) := by simpa only [z,k,List.get_eq_getElem,pre,List.getElem_replicate] using hh
      rw [ho]; simp [operation,hjx,hjy,hl,h₁,h₂]
    by_cases he : i=J
    · subst i
      have hh := get_mid pre (p.gcd t,0) (s.map (BitPackedPivot.matrix m p t).row)
      have ho : z.get k=(p.gcd t,0) := by simpa only [z,k,J,List.get_eq_getElem,lp] using hh
      rw [ho]; by_cases ht : t=0 <;> simp [operation,hjx,hjy,ht]
    have hbig : pre.length < i.val := by have hv : J < i := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm he); change j < i.val at hv; omega
    have hin := get_hi pre (p,t) s i.val hbig i.isLt
    have hout := get_hi pre (p.gcd t,0) (s.map (BitPackedPivot.matrix m p t).row) i.val hbig k.isLt
    let ix : Fin s.length := ⟨i.val-pre.length-1,by have hw := i.isLt; simp [a,rowsAt] at hw; omega⟩
    let v := s.get ix
    have vi : a.get i=v := hin
    have vo : z.get k=(BitPackedPivot.matrix m p t).row v := by
      simpa only [z,k,v,ix,List.get_eq_getElem,List.getElem_map] using hout
    have hval := row_eq hm p t hp v (hs v (List.get_mem ..))
    have ex : x i=v.1 := congrArg Prod.fst vi
    have ey : y i=v.2 := congrArg Prod.snd vi
    rw [vo,hval]; by_cases ht : t=0 <;> simp only [operation,hjx,hjy,ht,hl,he,ex,ey,ite_true,ite_false,Prod.mk.eta]
  rw [op] at eq; exact eq

end DetDLP.PackedHermiteRefinement
end

section

namespace DetDLP.PackedColumnWords
open BorderedHermite
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open BitPackedPivot (io banks blank)

def low {n : ℕ} (j : Fin n) (i : Fin j.val) : Fin n := ⟨i.val,lt_trans i.isLt j.isLt⟩
def high {n : ℕ} (j : Fin n) (i : Fin (n-j.val-1)) : Fin n := ⟨j.val+1+i.val,by have := i.isLt; omega⟩

theorem split {α : Type*} {n : ℕ} (f : Fin n → α) (j : Fin n) :
    List.ofFn f = List.ofFn (fun i => f (low j i)) ++ f j :: List.ofFn (fun i => f (high j i)) := by
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  have hn : i < n := by simpa using h₁
  by_cases hi : i < j.val
  · rw [List.getElem_append_left (by simpa using hi)]
    simp only [List.getElem_ofFn]; rfl
  · rw [List.getElem_append_right (by simpa using le_of_not_gt hi)]
    by_cases he : i=j.val
    · subst i; simp
    · rw [List.getElem_cons,dif_neg (by simpa using (show i-j.val≠0 by omega))]
      simp only [List.getElem_ofFn]; congr 1; apply Fin.ext
      change i = j.val+1+(i-(List.ofFn (fun i => f (low j i))).length-1)
      simp; omega

def digit {n} (c : Column n) (i : Fin n) := (c.get i).toNat
def word {n} (b : ℕ) (c : Column n) := Nat.ofDigits b (List.ofFn (digit c))
def digitsBounded {n} (m : ℕ) (c : Column n) := ∀ i, 0 ≤ c.get i ∧ c.get i ≤ (m:ℤ)
def zeroBefore {n} (j : Fin n) (c : Column n) := ∀ i < j,c.get i=0
def reducedAfter {n} (m : ℕ) (j : Fin n) (c : Column n) := ∀ i,j < i → c.get i < (m:ℤ)

theorem word_split {n} (b : ℕ) (j : Fin n) (c : Column n) :
    word b c = Nat.ofDigits b (List.ofFn fun i => digit c (low j i))+
      b^j.val*(digit c j+b*Nat.ofDigits b (List.ofFn fun i => digit c (high j i))) := by
  unfold word; rw [split (digit c) j,Nat.ofDigits_append,Nat.ofDigits_cons,List.length_ofFn]

theorem zero_low {n} (b : ℕ) (j : Fin n) (c : Column n) (h : zeroBefore j c) :
    Nat.ofDigits b (List.ofFn fun i => digit c (low j i))=0 := by
  have hh (i : Fin j.val) : digit c (low j i)=0 := by simp [digit,h _ (show low j i < j from i.isLt)]
  simp [hh]

theorem signed_digit {n} {m : ℕ} {c : Column n} (hc : digitsBounded m c) :
    UnsignedHermitePivot.signedColumn (digit c)=c := by
  ext i h
  have h' := (hc ⟨i,h⟩).1
  simp only [UnsignedHermitePivot.signedColumn,Vector.getElem_ofFn]
  change ((c.get ⟨i,h⟩).toNat:ℤ)=_ 
  exact Int.toNat_of_nonneg h'

def tailRows {n} (j : Fin n) (v w : Column n) :=
  List.ofFn fun i => (digit v (high j i),digit w (high j i))

private theorem tail_fst {n} (b : ℕ) (j : Fin n) (v w : Column n) :
    (BitColumnScan.pack b (tailRows j v w)).1 =
      Nat.ofDigits b (List.ofFn fun i => digit v (high j i)) := by
  simp [BitColumnScan.pack,tailRows,List.map_ofFn,Function.comp_def]
private theorem tail_snd {n} (b : ℕ) (j : Fin n) (v w : Column n) :
    (BitColumnScan.pack b (tailRows j v w)).2 =
      Nat.ofDigits b (List.ofFn fun i => digit w (high j i)) := by
  simp [BitColumnScan.pack,tailRows,List.map_ofFn,Function.comp_def]

theorem word_lt {n m : ℕ} (hm : 0 < m) (v : Column n) (hv : digitsBounded m v) :
    word (m+1) v < (m+1)^n := by
  apply lt_of_lt_of_eq (Nat.ofDigits_lt_base_pow_length (l:=List.ofFn (digit v)) (by omega : 1 < m+1) ?_) (by simp)
  intro d hd; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hd
  have := hv i; dsimp [digit]; omega

theorem transform {n m : ℕ} [NeZero m] (hm : 2 ≤ m) (j : Fin n) (v w : Column n)
    (hv : digitsBounded m v) (hw : digitsBounded m w) (vz : zeroBefore j v) (wz : zeroBefore j w)
    (vr : reducedAfter m j v) (wr : reducedAfter m j w) (hp : 0 < v.get j) :
    let p := digit v j
    let t := digit w j
    let q := BitPackedPivot.matrix m p t
    let out := pivotPair (m:ℤ) j v w
    (digit out.1 j=p.gcd t ∧ digit out.2 j=0) ∧
    (zeroBefore j out.1 ∧ zeroBefore j out.2) ∧
    (∀ i, j < i → (digit out.1 i,digit out.2 i)=q.row (digit v i,digit w i)) ∧
    digitsBounded m out.1 ∧ digitsBounded m out.2 ∧ reducedAfter m j out.1 ∧ reducedAfter m j out.2 := by
  intro p t q out
  have hz (i : Fin n) (hi : i < j) : digit v i=0 ∧ digit w i=0 := by simp [digit,vz _ hi,wz _ hi]
  have hp' : 0 < p := by dsimp [p,digit]; omega
  have hpM : p ≤ m := by have hh := hv j; dsimp [p,digit]; omega
  have gM : p.gcd t ≤ m := (Nat.gcd_le_left t hp').trans hpM
  have eq (i : Fin n) := UnsignedHermitePivot.operation_correct (m:=m) j (digit v) (digit w) hp' hz i
  simp only [signed_digit hv,signed_digit hw] at eq
  have mid : out.1.get j=(p.gcd t:ℕ) ∧ out.2.get j=0 := by
    have h := eq j
    change out.1.get j = _ ∧ out.2.get j = _ at h
    by_cases he : digit w j=0
    · simpa only [UnsignedHermitePivot.operation,p,t,he,ite_true,Nat.gcd_zero_right,Nat.cast_zero] using h
    · simpa only [UnsignedHermitePivot.operation,p,t,he,ite_false,lt_irrefl,ite_true,Nat.cast_zero] using h
  have past (i : Fin n) (hi : i < j) : out.1.get i=0 ∧ out.2.get i=0 := by
    have h := eq i
    obtain ⟨h₁,h₂⟩ := hz i hi
    by_cases he : digit w j=0 <;> simpa only [out,UnsignedHermitePivot.operation,he,ite_true,ite_false,hi,h₁,h₂,Nat.cast_zero] using h
  have tail (i : Fin n) (hi : j < i) :
      out.1.get i=((q.row (digit v i,digit w i)).1:ℤ) ∧ out.2.get i=((q.row (digit v i,digit w i)).2:ℤ) := by
    have h := eq i
    have hr : digit v i < m ∧ digit w i < m := by
      have := vr i hi; have := wr i hi; dsimp [digit]; omega
    have ht := PackedHermiteRefinement.row_eq hm p t hp' (digit v i,digit w i) hr
    change out.1.get i = _ ∧ out.2.get i = _ at h
    change out.1.get i = _ ∧ out.2.get i = _
    rw [ht]; change out.1.get i = _ ∧ out.2.get i = _
    by_cases he : digit w j=0 <;>
      simpa only [UnsignedHermitePivot.operation,p,t,he,ite_true,ite_false,not_lt_of_gt hi,ne_of_gt hi] using h
  have hb (i : Fin n) (hi : j < i) :
      0 ≤ out.1.get i ∧ out.1.get i < (m:ℤ) ∧ 0 ≤ out.2.get i ∧ out.2.get i < (m:ℤ) := by
    obtain ⟨h₁,h₂⟩ := tail i hi
    rw [h₁,h₂]
    have hpos : 0 < q.m := by change 0 < m; omega
    have h₁ := Nat.mod_lt (q.a*digit v i+q.b*digit w i) hpos
    have h₂ := Nat.mod_lt (q.c*digit v i+q.d*digit w i) hpos
    exact ⟨by positivity,by exact_mod_cast h₁,by positivity,by exact_mod_cast h₂⟩
  have bounds (i : Fin n) : (0 ≤ out.1.get i ∧ out.1.get i ≤ (m:ℤ)) ∧ (0 ≤ out.2.get i ∧ out.2.get i ≤ (m:ℤ)) := by
    rcases lt_trichotomy i j with hi|rfl|hi
    · obtain ⟨a,b⟩:=past i hi; simp [a,b]
    · simp [mid.1,mid.2,gM]
    · obtain ⟨a,b,c,d⟩ := hb i hi; omega
  refine ⟨by simp [digit,mid.1,mid.2],⟨fun i h => (past i h).1,fun i h => (past i h).2⟩,
    ?_,fun i => (bounds i).1,fun i => (bounds i).2,fun i h => (hb i h).2.1,fun i h => (hb i h).2.2.2⟩
  intro i hi; obtain ⟨a,b⟩ := tail i hi; simp [digit,a,b]

theorem pivot_words {n m : ℕ} [NeZero m] (hm : 2 ≤ m) (j : Fin n) (v w : Column n)
    (hv : digitsBounded m v) (hw : digitsBounded m w) (vz : zeroBefore j v) (wz : zeroBefore j w)
    (vr : reducedAfter m j v) (wr : reducedAfter m j w) (hp : 0 < v.get j) (N : ℕ)
    (hcap : (m+1)^n ≤ N) (hsq : (m+1)^2 ≤ N) (r : Regs) :
    let b := m+1
    let addr := b^j.val
    let out := pivotPair (m:ℤ) j v w
    ∃ k rf, k ≤ 4*BitPackedPivot.overhead*(bitLen m+n+3)*((2*N).size+2)^2 ∧
      Eval BitPackedPivot.command k ⟨r,frame (banks blank (io m addr (word b v) (word b w)))⟩
        ⟨rf,frame (banks blank (io m addr (word b out.1) (word b out.2)))⟩ := by
  intro b addr out
  let rows := tailRows j v w
  let p := digit v j
  let t := digit w j
  let q := BitPackedPivot.matrix m p t
  obtain ⟨⟨ep,et⟩,⟨o₁,o₂⟩,eq,_,_,_,_⟩ := transform hm j v w hv hw vz wz vr wr hp
  have hl : rows.length=n-j.val-1 := List.length_ofFn
  have ij := j.isLt
  have hcap' : addr*b^(rows.length+1) ≤ N := by
    dsimp [addr]; rw [← pow_add,hl,show j.val+(n-j.val-1+1)=n by omega]; exact hcap
  have hd (z : ℕ × ℕ) (hz : z∈rows) : z.1 ≤ m ∧ z.2 ≤ m := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    have := hv (high j i); have := hw (high j i); dsimp [digit]; omega
  have hp' : 0 < p := by dsimp [p,digit]; omega
  have hpm : p ≤ m := by have := hv j; dsimp [p,digit]; omega
  have htm : t ≤ m := by have := hw j; dsimp [t,digit]; omega
  obtain ⟨k,rf,hk,he⟩ := BitPackedPivot.pivot_eval m hm p t addr hp' hpm htm (pow_pos (Nat.succ_pos _) _) rows hd N hcap' hsq r
  have tails : tailRows j out.1 out.2 = rows.map q.row := by
    rw [show rows.map q.row=List.ofFn (fun i => q.row (digit v (high j i),digit w (high j i))) by simp [rows,tailRows,List.map_ofFn,Function.comp_def]]
    unfold tailRows; congr 1; funext i
    exact eq _ (show j.val < j.val+1+i.val by omega)
  have src (c : Column n) (hz : zeroBefore j c) : word b c =
      addr*(digit c j + b*Nat.ofDigits b (List.ofFn fun i => digit c (high j i))) := by
    rw [word_split b j c,zero_low b j c hz,zero_add]
  have A := src v vz
  have B := src w wz
  have C := src out.1 o₁
  have D := src out.2 o₂
  rw [← tail_fst b j v w] at A
  rw [← tail_snd b j v w] at B
  rw [← tail_fst b j out.1 out.2,tails,ep,Nat.mul_add,← Nat.mul_assoc] at C
  rw [← tail_snd b j out.1 out.2,tails,et,zero_add,← Nat.mul_assoc] at D
  refine ⟨k,rf,hk.trans ?_,?_⟩
  · apply Nat.mul_le_mul_right
    apply Nat.mul_le_mul_left
    omega
  · rw [A,B,C,D]
    convert he using 1 <;> simp [q,rows,b,addr,p,t,Nat.mul_assoc]


theorem fixed_coordinates {n m : ℕ} [NeZero m] (hm : 2 ≤ m) (j : Fin n) (v c : Column n)
    (hv : digitsBounded m v) (hc : digitsBounded m c) (hz : zeroBefore j v) (hp : 0 < v.get j) :
    let p := digit v j
    let t := digit c j
    let q := BitFixedColumn.matrix m p t
    let out := reduceFixed (m:ℤ) j v c
    (∀ i < j, digit out i=digit c i) ∧ digit out j=t%p ∧
    (∀ i, j < i → digit out i=(q.row (digit c i,digit v i)).1) ∧
    digitsBounded m out ∧ reducedAfter m j out := by
  intro p t q out
  have M : 0 < (m:ℤ) := by exact_mod_cast (by omega : 0 < m)
  have ps (i : Fin n) : ((digit v i):ℤ)=v.get i := Int.toNat_of_nonneg (hv i).1
  have ts (i : Fin n) : ((digit c i):ℤ)=c.get i := Int.toNat_of_nonneg (hc i).1
  have lo (i : Fin n) (hi : i < j) : out.get i=c.get i := by
    simp [out,reduceFixed,trim,not_lt_of_gt hi,hz i hi]
  have mid : out.get j=((t%p:ℕ):ℤ) := by
    simp only [out,reduceFixed,get_ofFn,trim,lt_irrefl,if_false]
    rw [Int.natCast_mod,show (p:ℤ)=v.get j from ps j,show (t:ℤ)=c.get j from ts j,Int.emod_def]
    ring
  have minusOne : ((m-1:ℕ):ZMod m) = -1 := by
    rw [Nat.cast_sub (by omega),ZMod.natCast_self,Nat.cast_one,zero_sub]
  have tail (i : Fin n) (hi : j < i) : out.get i=((q.row (digit c i,digit v i)).1:ℤ) := by
    simp only [out,reduceFixed,get_ofFn,trim,hi,if_true]
    change _ = (((1*digit c i+((m-1)*(t/p))*digit v i)%m:ℕ):ℤ)
    rw [← ZMod.val_intCast]
    have z : ((c.get i-c.get j/v.get j*v.get i:ℤ):ZMod m) =
        ((1*digit c i+((m-1)*(t/p))*digit v i:ℕ):ZMod m) := by
      rw [← ts i,← ts j,← ps j,← ps i]
      simp [t,p,minusOne,← Int.natCast_ediv,sub_eq_add_neg]
    exact_mod_cast (congrArg ZMod.val z).trans (ZMod.val_natCast _ _)
  have bd (i : Fin n) (hi : j < i) : 0 ≤ out.get i ∧ out.get i < (m:ℤ) := by
    simp only [out,reduceFixed,get_ofFn,trim,hi,if_true]
    exact ⟨Int.emod_nonneg _ M.ne',Int.emod_lt_of_pos _ M⟩
  refine ⟨fun i h => by simp [digit,lo i h],by simp only [digit,mid,Int.toNat_natCast],fun i h => by simp [digit,tail i h],?_,fun i h => (bd i h).2⟩
  intro i
  rcases lt_trichotomy i j with h|rfl|h
  · rw [lo _ h]; exact hc i
  · rw [mid]
    have := Nat.mod_le t p
    have ht := ts i
    have := hc i
    change (0:ℤ) ≤ (t%p:ℕ) ∧ ((t%p:ℕ):ℤ) ≤ m
    omega
  · have := bd i h; omega

theorem fixed_words {n m : ℕ} [NeZero m] (hm : 2 ≤ m) (j : Fin n) (v c : Column n)
    (hv : digitsBounded m v) (hc : digitsBounded m c) (hz : zeroBefore j v) (hp : 0 < v.get j)
    (N : ℕ) (hcap : (m+1)^n ≤ N) (hsq : (m+1)^2 ≤ N) (r : Regs) :
    let b := m+1
    let addr := b^j.val
    let out := reduceFixed (m:ℤ) j v c
    ∃ k rf, k ≤ BitFixedColumn.overhead*(n+3)*((2*N).size+2)^2 ∧
      Eval BitFixedColumn.command k ⟨r,frame (banks blank (io m addr (word b v) (word b c)))⟩
        ⟨rf,frame (banks blank (io m addr (word b v) (word b out)))⟩ := by
  intro b addr out
  let p := digit v j
  let t := digit c j
  let rows := tailRows j c v
  let pre := Nat.ofDigits b (List.ofFn fun i => digit c (low j i))
  let q := BitFixedColumn.matrix m p t
  have ij := j.isLt
  have hl : rows.length=n-j.val-1 := List.length_ofFn
  have hcap' : addr*b^(rows.length+1) ≤ N := by
    dsimp [addr]; rw [← pow_add,hl,show j.val+(n-j.val-1+1)=n by omega]; exact hcap
  have hpre : pre < addr := by
    apply lt_of_lt_of_eq (Nat.ofDigits_lt_base_pow_length (by dsimp [b]; omega) ?_) (by simp [addr])
    intro d hd; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hd
    have := hc (low j i); dsimp [digit,b]; omega
  have hd (z : ℕ × ℕ) (hz' : z∈rows) : z.1 ≤ m ∧ z.2 ≤ m := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz'
    have := hc (high j i); have := hv (high j i); dsimp [digit]; omega
  obtain ⟨k,rf,hk,he⟩ := BitFixedColumn.fixed_eval m p t addr pre hm
    (by dsimp [p,digit]; omega) (by have := hv j; dsimp [p,digit]; omega)
    (by have := hc j; dsimp [t,digit]; omega) hpre rows hd N hcap' hsq r
  obtain ⟨lo,mid,hi,_,_⟩ := fixed_coordinates hm j v c hv hc hz hp
  have xl := word_split b j v
  rw [zero_low b j v hz,zero_add,← tail_snd b j c v] at xl
  have yl := word_split b j c
  rw [← tail_fst b j c v] at yl
  have prefix_eq : (List.ofFn fun i => digit out (low j i))=(List.ofFn fun i => digit c (low j i)) := by
    congr 1; funext i; exact lo _ i.isLt
  have suffix : (List.ofFn fun i => digit out (high j i)) = (rows.map q.row).map Prod.fst := by
    simp only [rows,tailRows,List.map_ofFn,Function.comp_def]
    congr 1; funext i; exact hi _ (show j.val < j.val+1+i.val by omega)
  have ol := word_split b j out
  rw [prefix_eq,mid,suffix] at ol
  refine ⟨k,rf,hk.trans ?_,?_⟩
  · apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; omega
  · rw [Nat.mul_add (b^j.val),← Nat.mul_assoc (b^j.val) b,← Nat.add_assoc] at ol
    rw [xl,yl,ol]
    exact he

end DetDLP.PackedColumnWords
end

section

namespace DetDLP.BitMatrixPass
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode BitRegisterCall
open BitPackedPivot (io blank banks Bounded)

abbrev I := BitRegisterCode.Instr 38
def table (D : ℕ) (cols : List ℕ) : ℕ := Nat.ofDigits D (cols++[1])
@[simp] theorem table_nil (D : ℕ) : table D []=1 := by simp [table]
theorem table_cons (D x : ℕ) (xs : List ℕ) : table D (x::xs)=x+D*table D xs := rfl

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

private theorem load_ok (m w x D stream accum pow : ℕ) (hD : 0 < D) :
    let v := state m w x 0 D stream accum pow
    Valid loadCode v ∧ run loadCode v = state m w x (stream%D) D stream accum pow := by
  intro v
  constructor
  · change ((Op.rem=Op.quot ∨ Op.rem=Op.rem) → 0 < D) ∧ True; simp [hD]
  · funext i; fin_cases i <;> rfl

private theorem save_ok (m w x y D stream accum pow : ℕ) (hD : 0 < D) :
    let v := state m w x y D stream accum pow
    Valid saveCode v ∧ run saveCode v = state m w x 0 D (stream/D) (accum+pow*y) (pow*D) := by
  intro v
  constructor
  · simp [Valid,saveCode,Op.Valid,BitRegisterCode.Instr.step]
    all_goals exact hD
  · funext i; fin_cases i <;> rfl

theorem table_pos (D : ℕ) (hD : 0 < D) (xs : List ℕ) : 0 < table D xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => rw [table_cons]; positivity

private theorem size_state (m w x y D stream acc pow N : ℕ)
    (h : ∀ z ∈ [m+1,w,x,y,D,stream,acc,pow], z ≤ N) :
    Bounded (state m w x y D stream acc pow) N := by
  have hb := h (m+1) (by simp)
  have hs := h stream (by simp)
  have hq := Nat.div_le_self stream D
  have hw := h w (by simp)
  have hx := h x (by simp)
  have hy := h y (by simp)
  have hD := h D (by simp)
  have ha := h acc (by simp)
  have hp := h pow (by simp)
  have hm : m ≤ N := by omega
  have ho : 1 ≤ N := by omega
  have hh := hq.trans hs
  intro j; fin_cases j <;> first | exact Nat.zero_le _ | exact hb | exact hm | exact hw | exact hx | exact hy | exact hD | exact hs | exact ha | exact hp | exact ho | exact hh

private theorem execList (c : List I) (v z : Vars 38) (r : Regs) (N : ℕ)
    (hv : Bounded v N) (h : Valid c v ∧ run c v=z) :
    ∃ k rf, k ≤ 1000^(c.length+1)*(N.size+2)^2 ∧ Eval (compile c) k ⟨r,frame v⟩ ⟨rf,frame z⟩ := by
  obtain ⟨k,rf,hk,he⟩ := run_eval c v r N.size (fun j => Nat.size_le_size (hv j)) h.1
  exact ⟨k,rf,hk,h.2 ▸ he⟩

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

theorem loop_eval {l : ℕ} (P : Program 8 38 l) (m w D budget N : ℕ)
    (hD : 1 < D) (hm : m+1 ≤ N) (hw : w ≤ N) (hdn : D ≤ N)
    {x xf : ℕ} {xs ys : List ℕ} (H : Pass P m w D budget x xs xf ys)
    (acc pow : ℕ) (hacc : acc < pow) (hpow : pow*D^xs.length ≤ N)
    (htab : table D xs ≤ N) (r : Regs) (hg : r 1=decide (table D xs/D ≠ 0)) :
    ∃ k rf, k ≤ xs.length*(budget+passOverhead*(N.size+2)^2)+1 ∧
      Eval (.while 1 (body P)) k ⟨r,frame (state m w x 0 D (table D xs) acc pow)⟩
        ⟨rf,frame (state m w xf 0 D 1 (acc+pow*Nat.ofDigits D ys) (pow*D^xs.length))⟩ := by
  induction H generalizing acc pow r with
  | nil x hx =>
    have hh : r 1=false := by simpa [Nat.div_eq_of_lt hD] using hg
    refine ⟨1,r,by simp,?_⟩
    simpa only [table_nil,List.length_nil,pow_zero,mul_one,Nat.ofDigits_nil,mul_zero,add_zero] using
      (Eval.while_false (body:=body P) (a:=⟨r,frame (state m w x 0 D 1 acc pow)⟩) hh)
  | @cons x y x' y' xf xs ys hx hy hx' hy' step rest ih =>
    let s := table D (y::xs)
    let t := table D xs
    have e : s=y+D*t := rfl
    have ep : 0 < t := table_pos D (by omega) xs
    have he : s/D=t := by rw [e,Nat.add_mul_div_left _ _ (by omega : 0 < D),Nat.div_eq_of_lt hy,zero_add]
    have hd : s%D=y := by rw [e,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hy]
    have hpow' : pow*D*D^xs.length ≤ N := by simpa only [List.length_cons,pow_succ',mul_assoc] using hpow
    have hpN : pow ≤ N := (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _)).trans hpow
    have hb (X Y : ℕ) (hX : X < D) (hY : Y < D) : Bounded (state m w X Y D s acc pow) N := by
      apply size_state
      intro z hz; simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
    obtain ⟨a,ra,ha,ea⟩ := execList loadCode _ _ r N (hb x 0 hx (by omega)) (load_ok m w x D s acc pow (by omega))
    rw [hd] at ea
    obtain ⟨b,rb,hb',eb⟩ := step ra
    have eb' := call_left (n:=30) (u:=8) P (banks blank (io m w x y)) (banks blank (io m w x' y')) (params D s acc pow) ra rb b eb
    obtain ⟨c,rc,hc,ec⟩ := execList saveCode _ _ rb N (hb x' y' hx' hy') (save_ok m w x' y' D s acc pow (by omega))
    rw [he] at ec
    obtain ⟨rd,eg,hg'⟩ := peek_eval (34:Fin 38) (state m w x' 0 D t (acc+pow*y') (pow*D)) rc
    have hyN := BitPackedPivot.digit_bound pow acc y' D hacc hy'
    have htN : t ≤ N := he ▸ (Nat.div_le_self s D).trans htab
    obtain ⟨d,rf,hh,ef⟩ := ih (acc+pow*y') (pow*D) hyN hpow' htN rd hg'
    have hyes : r 1=true := by change r 1=decide (s/D≠0) at hg; rw [hg,he]; exact decide_eq_true ep.ne'
    refine ⟨(a+(b+(c+1)))+d+1,rf,?_,?_⟩
    · rw [List.length_cons,Nat.succ_mul xs.length]
      unfold passOverhead
      have hsq : 1 ≤ (N.size+2)^2 := Nat.one_le_pow _ _ (by omega)
      unfold passOverhead at hh
      nlinarith only [ha,hb',hc,hh,hsq]
    · have eacc : acc+pow*Nat.ofDigits D (y'::ys)=(acc+pow*y')+(pow*D)*Nat.ofDigits D ys := by rw [Nat.ofDigits_cons]; ring
      rw [eacc,List.length_cons,pow_succ',← mul_assoc]
      exact .while_true hyes (.seq ea (.seq eb' (.seq ec eg))) ef

theorem pass_eval {l : ℕ} (P : Program 8 38 l) (m w D budget N : ℕ)
    (hD : 1 < D) (hm : m+1 ≤ N) (hw : w ≤ N) (hdn : D ≤ N)
    {x xf : ℕ} {xs ys : List ℕ} (H : Pass P m w D budget x xs xf ys)
    (hpow : D^xs.length ≤ N) (htab : table D xs ≤ N) (r : Regs) :
    ∃ k rf, k ≤ xs.length*(budget+passOverhead*(N.size+2)^2)+2 ∧
      Eval (command P) k ⟨r,frame (state m w x 0 D (table D xs) 0 1)⟩
        ⟨rf,frame (state m w xf 0 D 1 (Nat.ofDigits D ys) (D^xs.length))⟩ := by
  obtain ⟨r₁,eg,hg⟩ := peek_eval (34:Fin 38) (state m w x 0 D (table D xs) 0 1) r
  obtain ⟨k,rf,hh,he⟩ := loop_eval P m w D budget N hD hm hw hdn H 0 1 (by decide) (by simpa using hpow) htab r₁ hg
  simp only [one_mul,zero_add] at he
  exact ⟨1+k,rf,by omega,.seq eg he⟩

end DetDLP.BitMatrixPass
end

section

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

theorem sweep_eq {n} (m : ℤ) (j : Fin n) (v : Column n) (cs : List (Column n)) (a : Array (Column n)) :
    cs.foldl (pairStep m j) (v,a) = ((sweep m j v cs).1,a++(sweep m j v cs).2.toArray) := by
  induction cs generalizing a v with
  | nil => simp [sweep]
  | cons c cs ih =>
    simp only [List.foldl_cons,pairStep,sweep]
    rw [ih]
    congr 1
    apply Array.toList_inj.mp
    simp only [Array.toList_append,Array.toList_push,List.toList_toArray,List.append_assoc,List.singleton_append]

theorem sweep_length {n} (m : ℤ) (j : Fin n) (v : Column n) (cs : List (Column n)) :
    (sweep m j v cs).2.length=cs.length := by
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih => simp [sweep,ih]

def pivotBudget (m n N : ℕ) := 4*BitPackedPivot.overhead*(bitLen m+n+3)*((2*N).size+2)^2+1

theorem sweep_pass {n m : ℕ} [NeZero m] (hm : 2 ≤ m) (j : Fin n) (N : ℕ)
    (hcN : (m+1)^n ≤ N) (hsq : (m+1)^2 ≤ N)
    (cs : List (Column n)) (hh : ∀ c∈cs, Active m j.val c)
    (v : Column n) (hv : digitsBounded m v) (vz : zeroBefore j v) (vr : reducedAfter m j v)
    (hp : 0 < v.get j) :
    let b := m+1
    let D := b^n
    let z := sweep (m:ℤ) j v cs
    (digitsBounded m z.1 ∧ zeroBefore j z.1 ∧ reducedAfter m j z.1 ∧ 0 < z.1.get j) ∧
    (∀ c∈z.2, Active m (j.val+1) c) ∧
    Pass BitPackedPivot.program m (b^j.val) D (pivotBudget m n N) (word b v)
      (cs.map (word b)) (word b z.1) (z.2.map (word b)) := by
  induction cs generalizing v with
  | nil =>
    exact ⟨⟨hv,vz,vr,hp⟩,by simp [sweep],.nil _ (word_lt (by omega) v hv)⟩
  | cons c cs ih =>
    let z := pivotPair (m:ℤ) j v c
    obtain ⟨hc,hz,hr⟩ := hh c (by simp)
    have cz : zeroBefore j c := fun i h => hz i h
    have cr : reducedAfter m j c := fun i h => hr i h.le
    obtain ⟨⟨ej,ej'⟩,⟨vz',cz'⟩,_,hv',hc',vr',cr'⟩ := transform hm j v c hv hc vz cz vr cr hp
    have ep : 0 < digit v j := by dsimp [digit]; omega
    have gp := Nat.gcd_pos_of_pos_left (digit c j) ep
    have hp' : 0 < z.1.get j := by
      have positive : 0 < digit z.1 j := ej.symm ▸ gp
      dsimp only [digit] at positive; omega
    obtain ⟨hout,ha,hrest⟩ := ih (fun cc h => hh cc (by simp [h])) z.1 hv' vz' vr' hp'
    have hnext : Active m (j.val+1) z.2 := by
      refine ⟨hc',?_,fun i h => cr' i (show j.val < i.val by omega)⟩
      intro i h
      rcases lt_or_ge i j with hij|hij
      · exact cz' i hij
      · have e : i=j := Fin.ext (by change j.val ≤ i.val at hij; omega)
        subst i; exact (pivot_row (m:ℤ) j v c hp).2
    refine ⟨hout,?_,.cons (word_lt (by omega) v hv) (word_lt (by omega) c hc)
      (word_lt (by omega) z.1 hv') (word_lt (by omega) z.2 hc') ?_ hrest⟩
    · intro u hu; rcases List.mem_cons.mp hu with rfl|h
      · exact hnext
      · exact ha u h
    · intro r
      obtain ⟨k,rf,hk,he⟩ := pivot_words hm j v c hv hc vz cz vr cr hp N hcN hsq r
      exact ⟨k+1,rf,Nat.succ_le_succ hk,compiled_halt_trace he _ _⟩

def fixedProgram := compiled BitFixedColumn.command (port (15:Fin 30)) (port (15:Fin 30))
def fixedBudget (n N : ℕ) := BitFixedColumn.overhead*(n+3)*((2*N).size+2)^2+1

theorem fixed_pass {n m : ℕ} [NeZero m] (hm : 2 ≤ m) (j : Fin n) (N : ℕ)
    (hcN : (m+1)^n ≤ N) (hsq : (m+1)^2 ≤ N)
    (v : Column n) (hv : digitsBounded m v) (vz : zeroBefore j v) (hp : 0 < v.get j)
    (cs : List (Column n)) (hh : ∀ c∈cs,digitsBounded m c) :
    let b := m+1
    let ys := cs.map (reduceFixed (m:ℤ) j v)
    (∀ c∈ys, digitsBounded m c) ∧
    Pass fixedProgram m (b^j.val) (b^n) (fixedBudget n N) (word b v)
      (cs.map (word b)) (word b v) (ys.map (word b)) := by
  induction cs with
  | nil => exact ⟨by simp,.nil _ (word_lt (by omega) v hv)⟩
  | cons c cs ih =>
    have hc := hh c (by simp)
    have hcf := (fixed_coordinates hm j v c hv hc vz hp).2.2.2.1
    obtain ⟨bs,rest⟩ := ih (fun u hu => hh u (by simp [hu]))
    refine ⟨?_,.cons (word_lt (by omega) v hv) (word_lt (by omega) c hc)
      (word_lt (by omega) v hv) (word_lt (by omega) _ hcf) ?_ rest⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl|h
      · exact hcf
      · exact bs u h
    · intro r; obtain ⟨k,rf,hk,he⟩ := fixed_words hm j v c hv hc vz hp N hcN hsq r
      exact ⟨k+1,rf,Nat.succ_le_succ hk,compiled_halt_trace he _ _⟩

end DetDLP.HermiteWordPass
end

section

namespace DetDLP.HermiteStageMachine
open BorderedHermite PackedColumnWords HermiteWordPass
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode BitRegisterCall
open BitMatrixPass (table Pass pass_eval)
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

theorem pre_ok (m D w F A : ℕ) (hD : 0 < D) :
    let v := initial m D w F A
    Valid prepare v ∧ run prepare v =
      merge (BitMatrixPass.state m w (m*w) 0 D A 0 1) (shell m D w F A) := by
  intro v
  constructor
  · simp [prepare,Valid,cp,Op.Valid,BitRegisterCode.Instr.step]; exact hD
  · funext i; fin_cases i <;> rfl

theorem switch_ok (m D w F A p u z : ℕ) (hD : 0 < D) :
    let v := merge (BitMatrixPass.state m w p 0 D 1 u z) (shell m D w F A)
    Valid switchPass v ∧ run switchPass v =
      merge (BitMatrixPass.state m w p 0 D F 0 1) (shell m D w F (u+z)) := by
  intro v
  constructor
  · simp [switchPass,Valid,cp,erase,Op.Valid,BitRegisterCode.Instr.step]; exact hD
  · funext i; fin_cases i <;> rfl

theorem finish_ok (m D w F A p u z : ℕ) (hw : 0 < w) :
    let v := merge (BitMatrixPass.state m w p 0 D 1 u z) (shell m D w F A)
    Valid finish v ∧ run finish v =
      initial m D (w*(m+1)) (u+(p+D)*z) A := by
  intro v
  constructor
  · simp [finish,Valid,cp,erase,Op.Valid,BitRegisterCode.Instr.step]
    change 0 < (m+1)*(w*(m+1))
    positivity
  · funext i; fin_cases i <;> rfl

def bounded {k} (v : Vars k) (N : ℕ) := ∀ i,v i ≤ N

theorem merged_bound (v : L) (a : R) (N : ℕ) (hv : bounded v N) (ha : bounded a N) :
    bounded (merge v a) N := by
  intro i; refine Fin.addCases (m:=38) (n:=9) (motive:=fun i => merge v a i ≤ N) (fun k => ?_) (fun k => ?_) i
  · simpa [merge] using hv k
  · simpa [merge] using ha k

theorem shell_bound (m D w F A N : ℕ)
    (hb : m+1 ≤ N) (hd : D ≤ N) (hw : w ≤ N) (hf : F ≤ N) (ha : A ≤ N) :
    bounded (shell m D w F A) N := by
  have hm : m ≤ N := by omega
  have ho : 1 ≤ N := by omega
  have hq := (Nat.div_le_self D ((m+1)*w)).trans hd
  intro i; fin_cases i <;> first | assumption | exact Nat.zero_le _

theorem code_eval (code : List I) (v z : V) (N : ℕ) (r : Regs) (hv : bounded v N)
    (h : Valid code v ∧ run code v=z) :
    ∃ k rf, k ≤ 1000^(code.length+1)*(N.size+2)^2 ∧
      Eval (compile code) k ⟨r,frame v⟩ ⟨rf,frame z⟩ := by
  obtain ⟨k,rf,hk,he⟩ := run_eval code v r N.size (fun j => Nat.size_le_size (hv j)) h.1
  exact ⟨k,rf,hk,h.2 ▸ he⟩

theorem terminal_bound (m w p D u z N : ℕ) (hm : m+1 ≤ N) (hw : w ≤ N) (hp : p ≤ N)
    (hd : D ≤ N) (hu : u ≤ N) (hz : z ≤ N) : bounded (BitMatrixPass.state m w p 0 D 1 u z) N := by
  have h0 : m ≤ N := by omega
  have h1 : 1 ≤ N := by omega
  have hq := (Nat.div_le_self 1 D).trans h1
  intro i; fin_cases i <;> first | assumption | exact Nat.zero_le _

theorem table_end (D : ℕ) (xs : List ℕ) : table D xs=Nat.ofDigits D xs+D^xs.length := by
  simp [table,Nat.ofDigits_append]
theorem table_snoc (D : ℕ) (xs : List ℕ) (p : ℕ) :
    table D (xs++[p])=Nat.ofDigits D xs+(p+D)*D^xs.length := by
  rw [table_end,Nat.ofDigits_append]
  simp [pow_succ]; ring

def overhead := 1000^(prepare.length+1)+1000^(switchPass.length+1)+1000^(finish.length+1)+6

theorem stage_eval {m w D N p bp bf : ℕ} {as fs ys zs : List ℕ}
    (hD : 1 < D) (hb : m+1 ≤ N) (hd : D ≤ N) (hw : 0 < w) (hwN : w ≤ N)
    (hp : p < D) (hpA : Pass BitPackedPivot.program m w D bp (m*w) as p ys)
    (hpF : Pass fixedProgram m w D bf p fs p zs) (ha : table D as ≤ N) (hf : table D fs ≤ N)
    (hy : table D ys ≤ N) (hz : table D zs ≤ N) (ely : ys.length=as.length) (elz : zs.length=fs.length) (r : Regs) :
    ∃ k rf, k ≤ (as.length+fs.length)*(bp+bf+BitMatrixPass.passOverhead*(N.size+2)^2)+overhead*(N.size+2)^2 ∧
      Eval command k ⟨r,frame (initial m D w (table D fs) (table D as))⟩
        ⟨rf,frame (initial m D (w*(m+1)) (table D (zs++[p])) (table D ys))⟩ := by
  have H (xs : List ℕ) (h : table D xs ≤ N) :
      Nat.ofDigits D xs ≤ N ∧ D^xs.length ≤ N := by rw [table_end] at h; omega
  have hsh := shell_bound m D w _ _ N hb hd hwN hf ha
  obtain ⟨a,ra,ha',ea⟩ := code_eval prepare _ _ N r
    (merged_bound _ _ _ (fun _ => Nat.zero_le _) hsh) (pre_ok _ _ _ _ _ (by omega))
  obtain ⟨b,rb,hb',eb⟩ := pass_eval _ _ _ _ _ N hD hb hwN hd hpA (H _ ha).2 ha ra
  have eb' := call_left (n:=38) (u:=9) (passProg BitPackedPivot.program) _ _ (shell m D w (table D fs) (table D as))
    ra rb (b+1) (compiled_halt_trace eb _ _)
  have hu := H _ hy
  have hz' := H _ hz
  rw [← ely] at eb'
  obtain ⟨c,rc,hc',ec⟩ := code_eval switchPass _ _ N rb
    (merged_bound _ _ _ (terminal_bound _ _ _ _ _ _ _ hb hwN (hp.le.trans hd) hd hu.1 hu.2) hsh)
    (switch_ok _ _ _ _ _ _ _ _ (by omega))
  rw [← table_end D ys] at ec
  have hsh' := shell_bound m D w _ _ N hb hd hwN hf hy
  obtain ⟨d,rd,hd',ed⟩ := pass_eval _ _ _ _ _ N hD hb hwN hd hpF (H _ hf).2 hf rc
  have ed' := call_left (n:=38) (u:=9) (passProg fixedProgram) _ _ (shell m D w (table D fs) (table D ys))
    rc rd (d+1) (compiled_halt_trace ed _ _)
  rw [← elz] at ed'
  obtain ⟨e,rf,he',ee⟩ := code_eval finish _ _ N rd
    (merged_bound _ _ _ (terminal_bound _ _ _ _ _ _ _ hb hwN (hp.le.trans hd) hd hz'.1 hz'.2) hsh')
    (finish_ok _ _ _ _ _ _ _ _ hw)
  rw [← table_snoc D zs p] at ee
  refine ⟨_,rf,?_,.seq ea (.seq eb' (.seq ec (.seq ed' ee)))⟩
  unfold overhead
  have hs : 1 ≤ (N.size+2)^2 := Nat.one_le_pow _ _ (by omega)
  nlinarith only [ha',hb',hc',hd',he',hs,Nat.zero_le (as.length*bf),Nat.zero_le (fs.length*bp)]

end DetDLP.HermiteStageMachine
end

section

namespace DetDLP.HermiteRowTrace
open BorderedHermite PackedColumnWords HermiteWordPass HermiteStageMachine
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open BitMatrixPass (table)

def matrixWord {n} (m : ℕ) (a : Array (Column n)) := table ((m+1)^n) (a.toList.map (word (m+1)))
def ceiling (m n c : ℕ) := (m+1)^((n+2)*(n+c+3))
def invariant {n} (m c k : ℕ) (s : Array (Column n) × Array (Column n)) :=
  s.1.size=k ∧ s.2.size=c ∧ (∀ v∈s.1,digitsBounded m v) ∧ (∀ v∈s.2,Active m k v)

theorem table_bound (D : ℕ) (hD : 1 < D) (xs : List ℕ) (hx : ∀ x∈xs,x<D) :
    table D xs < D^(xs.length+1) := by
  unfold table
  apply lt_of_lt_of_eq (Nat.ofDigits_lt_base_pow_length hD ?_) (by simp)
  intro x h; rcases List.mem_append.mp h with h|h
  · exact hx _ h
  · simpa only [List.mem_singleton.mp h] using hD

theorem capacity {n c m : ℕ} (hm : 2 ≤ m) (hn : 0 < n) :
    let b := m+1
    let D := b^n
    let N := ceiling m n c
    1 < D ∧ b ≤ N ∧ D ≤ N ∧ b^2 ≤ N ∧ ∀ t ≤ n+c+2, D^t ≤ N := by
  intro b D N
  have h0 : 0 < b := by dsimp [b]; omega
  have h1 : 1 < b := by dsimp [b]; omega
  have hD : 1 < D := by exact (h1.trans_le (Nat.le_self_pow hn.ne' b)) 
  have cap (t : ℕ) (ht : t ≤ n+c+2) : D^t ≤ N := by
    change (b^n)^t ≤ b^((n+2)*(n+c+3))
    rw [← pow_mul]; exact Nat.pow_le_pow_right h0 (Nat.mul_le_mul (by omega) (by omega))
  have hdn : D ≤ N := by simpa using cap 1 (by omega)
  have hbn : b ≤ N := (Nat.le_self_pow hn.ne' b).trans hdn
  have hs : b^2 ≤ N := Nat.pow_le_pow_right h0 (by change 2 ≤ (n+2)*(n+c+3); nlinarith only [Nat.zero_le (n*(n+c+3))])
  exact ⟨hD,hbn,hdn,hs,cap⟩

theorem matrix_bound {n c m : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (a : Array (Column n))
    (ha : ∀ v∈a,digitsBounded m v) (hs : a.size ≤ n+c+1) : matrixWord m a ≤ ceiling m n c := by
  obtain ⟨hd,_,_,_,cap⟩:=capacity (c:=c) hm hn
  refine (table_bound _ hd _ ?_).le.trans (cap _ ?_)
  · intro x hx; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact word_lt (by omega) _ (ha _ (by simpa using hv))
  · simp; omega

def seed {n} (m : ℕ) (j : Fin n) : Column n := Vector.ofFn fun i => if i=j then (m:ℤ) else 0

theorem seed_properties {n m : ℕ} (hm : 2 ≤ m) (j : Fin n) :
    digitsBounded m (seed m j) ∧ zeroBefore j (seed m j) ∧ reducedAfter m j (seed m j) ∧
      0 < (seed m j).get j ∧ word (m+1) (seed m j)=m*(m+1)^j.val := by
  have hzero (i : Fin n) (hi : i≠j) : (seed m j).get i=0 := by simp [seed,hi]
  have hz : zeroBefore j (seed m j) := fun i hi => hzero i hi.ne
  have head : (seed m j).get j=(m:ℤ) := by simp [seed]
  refine ⟨?_,hz,fun i hi => by rw [hzero i hi.ne']; exact_mod_cast (by omega : 0 < m),by rw [head]; exact_mod_cast (by omega : 0 < m),?_⟩
  · intro i; by_cases he : i=j
    · subst i; simp [head]
    · simp [hzero i he]
  · rw [word_split _ j _,zero_low _ _ _ hz,zero_add]
    have hx (i : Fin (n-j.val-1)) : digit (seed m j) (high j i)=0 := by
      rw [digit,hzero]; rfl
      intro e; have := congrArg Fin.val e; dsimp [high] at this; omega
    have hd : digit (seed m j) j=m := by simp [digit,head]
    simp only [hx,hd]; simp [mul_comm]

def rowCost (m n c : ℕ) :=
  let N := ceiling m n c
  (n+c)*(pivotBudget m n N+fixedBudget n N+BitMatrixPass.passOverhead*(N.size+2)^2)+overhead*(N.size+2)^2

theorem row_eval {n c m : ℕ} [NeZero m] (hm : 2 ≤ m) (j : Fin n)
    (st : Array (Column n) × Array (Column n)) (hst : invariant m c j.val st) (r : Regs) :
    let b := m+1
    let D := b^n
    let z := pivotStage (m:ℤ) j st
    invariant m c (j.val+1) z ∧
    ∃ k rf, k ≤ rowCost m n c ∧ Eval command k
      ⟨r,frame (initial m D (b^j.val) (matrixWord m st.1) (matrixWord m st.2))⟩
      ⟨rf,frame (initial m D (b^(j.val+1)) (matrixWord m z.1) (matrixWord m z.2))⟩ := by
  intro b D z
  obtain ⟨hsf,hsa,hf,ha⟩ := hst
  let N := ceiling m n c
  let v := seed m j
  let y := sweep (m:ℤ) j v st.2.toList
  let zs := st.1.map (reduceFixed (m:ℤ) j y.1)
  have ij := j.isLt
  have hn : 0 < n := by omega
  obtain ⟨hD,hbN,hDN,hsq,cap⟩ := capacity (c:=c) hm hn
  obtain ⟨vb,vz,vr,vp,vw⟩ := seed_properties hm j
  obtain ⟨⟨yb,yz,yr,yp⟩,hy,hpass⟩ := sweep_pass hm j N hDN hsq st.2.toList
    (fun c' h => ha _ (by simpa using h)) v vb vz vr vp
  obtain ⟨hz,hfixed⟩ := fixed_pass hm j N hDN hsq y.1 yb yz yp st.1.toList (fun _ h => hf _ (by simpa using h))
  have yeq : z=(zs.push y.1,y.2.toArray) := by
    change pivotStage (m:ℤ) j st=_
    simp only [pivotStage]
    rw [sweep_eq]; simp [zs,y,v,seed]
  have len : y.2.length = st.2.size := by simpa [y] using sweep_length (m:ℤ) j v st.2.toList
  have hz' : ∀ u∈zs, digitsBounded m u := by intro u hu; exact hz u (by simpa [zs] using hu)
  have hy' : ∀ u∈y.2.toArray, Active m (j.val+1) u := by intro u hu; exact hy _ (by simpa using hu)
  have H : invariant m c (j.val+1) z := by
    rw [yeq]; refine ⟨by simp [zs,hsf],by simp [len,hsa],?_,hy'⟩
    intro u hu; rcases Array.mem_push.mp hu with h|h
    · exact hz' u h
    · simpa only [h] using yb
  have wN : b^j.val ≤ N := (Nat.pow_le_pow_right (by dsimp [b];omega) ij.le).trans hDN
  have hw : 0 < b^j.val := pow_pos (by dsimp [b];omega) _
  change BitMatrixPass.Pass _ _ _ _ _ (word b v) _ (word b y.1) _ at hpass
  rw [show word b v=m*b^j.val from vw] at hpass
  have F := matrix_bound (c:=c) hm hn st.1 hf (by omega)
  have A := matrix_bound (c:=c) hm hn st.2 (fun u hu => (ha u hu).1) (by omega)
  have Y := matrix_bound (c:=c) hm hn y.2.toArray (fun u hu => (hy' u hu).1) (by simp only [List.size_toArray,len,hsa]; omega)
  have Z := matrix_bound (c:=c) hm hn zs hz' (by simp [zs,hsf]; omega)
  obtain ⟨k,rf,hk,he⟩ := stage_eval hD hbN hDN hw wN (word_lt (by omega) y.1 yb) hpass hfixed A F
    (by simpa [matrixWord] using Y) (by simpa [matrixWord,zs] using Z)
    (by simpa only [List.length_map,Array.length_toList] using len) (by simp) r
  refine ⟨H,k,rf,hk.trans ?_,?_⟩
  · unfold rowCost
    simp only [List.length_map,Array.length_toList,hsf,hsa]
    apply Nat.add_le_add_right; apply Nat.mul_le_mul_right; omega
  · rw [yeq,pow_succ]; simpa [matrixWord,zs] using he

end DetDLP.HermiteRowTrace
end

section

namespace DetDLP.BitBorderColumn
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open BitMatrixPass (table table_cons table_pos)
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

theorem step_ok (m Q addr a x A X c w s : ℕ) (hm : 0 < m) (hQ : 0 < Q) (hw : 0 < addr)
    (ha : a < m+1) (hx : x < Q) :
    let b := m+1
    let d := coord b addr x
    let v := state m Q addr (a+b*A) (x+Q*X) c w s
    Valid stepCode v ∧ run stepCode v=state m Q addr A X (c+w*d) (b*w) ((s+a*d)%m) := by
  intro b d v
  have hb : 0 < b := Nat.succ_pos _
  have a1 : (a+b*A)/(m+1)=A := by rw [Nat.add_mul_div_left _ _ hb,Nat.div_eq_of_lt ha,zero_add]
  have a2 : (a+b*A)%(m+1)=a := by rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt ha]
  have x1 : (x+Q*X)/Q=X := by rw [Nat.add_mul_div_left _ _ hQ,Nat.div_eq_of_lt hx,zero_add]
  have x2 : (x+Q*X)%Q=x := by rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hx]
  constructor
  · simp [stepCode,Valid,Op.Valid,BitRegisterCode.Instr.step,state,v,hm,hQ,hw]
  · funext i; fin_cases i <;> first | rfl | simp [stepCode,run,BitRegisterCode.Instr.step,state,v,Op.eval,a1,a2,x1,x2,d,coord,b]

def cost := 1000^(stepCode.length+1)
private theorem exec_step (m Q addr A X c w s N : ℕ) (v : Vars 16) (r : Regs)
    (hc : ∀ q ∈ [m+1,Q,addr,A,X,c,w,s],q ≤ N) (H : Valid stepCode (state m Q addr A X c w s) ∧ run stepCode (state m Q addr A X c w s)=v) :
    ∃ t rf,t ≤ cost*(N.size+2)^2 ∧ Eval (compile stepCode) t ⟨r,frame (state m Q addr A X c w s)⟩ ⟨rf,frame v⟩ := by
  have hb := hc (m+1) (by simp)
  have hA := hc A (by simp)
  have hq := (Nat.div_le_self A (m+1)).trans hA
  have hm : m ≤ N := by omega
  have ho : 1 ≤ N := by omega
  have h (i : Fin 16) : state m Q addr A X c w s i ≤ N := by
    fin_cases i <;> first | assumption | exact Nat.zero_le _ | apply hc; simp [state]
  obtain ⟨t,rf,ht,he⟩ := run_eval _ _ r N.size (fun j => Nat.size_le_size (h j)) H.1
  exact ⟨t,rf,ht,H.2 ▸ he⟩

theorem scan (m Q addr : ℕ) (hm : 2 ≤ m) (hQ : 0 < Q) (hw : 0 < addr)
    (xs : List (ℕ × ℕ)) (hx : ∀ s∈xs,s.1 < m+1 ∧ s.2 < Q)
    (c w s N : ℕ) (hc : c < w) (hs : s < m) (h0 : s%m=s)
    (hbase : ∀ z ∈ [m+1,Q,addr],z ≤ N) (hA : packA (m+1) xs ≤ N) (hX : packX Q xs ≤ N)
    (hpow : w*(m+1)^xs.length ≤ N)
    (r : Regs) (hg : r 1=decide (packA (m+1) xs/(m+1)≠0)) :
    let b := m+1
    ∃ k rf,k ≤ xs.length*(cost*(N.size+2)^2+2)+1 ∧ Eval (.while 1 body) k
      ⟨r,frame (state m Q addr (packA b xs) (packX Q xs) c w s)⟩
      ⟨rf,frame (state m Q addr 1 0 (c+w*column b addr xs) (w*b^xs.length) ((s+dot b addr xs)%m))⟩ := by
  induction xs generalizing c w s r with
  | nil =>
    have hh : r 1=false := by simpa [packA,Nat.div_eq_of_lt (by omega : 1 < m+1)] using hg
    refine ⟨1,r,by simp,?_⟩
    simpa [packA,packX,column,dot,h0] using (Eval.while_false (body:=body)
      (a:=⟨r,frame (state m Q addr 1 0 c w s)⟩) hh)
  | cons z xs ih =>
    let b := m+1
    let d := coord b addr z.2
    have hb : 0 < b := Nat.succ_pos _
    have H := hx z (by simp)
    have ea : packA b (z::xs)=z.1+b*packA b xs := rfl
    have ex : packX Q (z::xs)=z.2+Q*packX Q xs := rfl
    have qa : packA b (z::xs)/b=packA b xs := by rw [ea,Nat.add_mul_div_left _ _ hb,Nat.div_eq_of_lt H.1,zero_add]
    have qx : packX Q (z::xs)/Q=packX Q xs := by rw [ex,Nat.add_mul_div_left _ _ hQ,Nat.div_eq_of_lt H.2,zero_add]
    have hwN : w ≤ N := (Nat.le_mul_of_pos_right w (pow_pos hb _)).trans hpow
    have hsN := hbase (m+1) (by simp)
    have hargs (u : ℕ) (hu : u∈[m+1,Q,addr,packA b (z::xs),packX Q (z::xs),c,w,s]) : u ≤ N := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
      rcases hu with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> first | assumption | omega | apply hbase; simp
    obtain ⟨t,rt,ht,et⟩ := exec_step _ _ _ _ _ _ _ _ N _ r hargs (step_ok m Q addr z.1 z.2 _ _ _ _ _ (by omega) hQ hw H.1 H.2)
    obtain ⟨rq,eq,hq⟩ := peek_eval (9:Fin 16) (state m Q addr (packA b xs) (packX Q xs) (c+w*d) (b*w) ((s+z.1*d)%m)) rt
    have hd := Nat.mod_lt (z.2/addr) hb
    have hacc : c+w*d < b*w := by simpa [Nat.mul_comm] using BitPackedPivot.digit_bound w c d b hc hd
    have hpow' : (b*w)*b^xs.length ≤ N := by simpa only [List.length_cons,pow_succ',mul_left_comm,mul_assoc] using hpow
    have sm := Nat.mod_lt (s+z.1*d) (by omega : 0 < m)
    have ap := (Nat.div_le_self (packA b (z::xs)) b).trans hA
    have xp := (Nat.div_le_self (packX Q (z::xs)) Q).trans hX
    rw [qa] at ap; rw [qx] at xp
    obtain ⟨k,rf,hk,ek⟩ := ih (fun u h => hx u (by simp [h])) _ _ _ hacc sm (Nat.mod_eq_of_lt sm) ap xp hpow' rq hq
    have hy : r 1=true := by change r 1=decide (packA b (z::xs)/b≠0) at hg; rw [hg,qa]; exact decide_eq_true (table_pos b hb _).ne'
    refine ⟨(t+1)+k+1,rf,?_,?_⟩
    · rw [List.length_cons,Nat.succ_mul]; omega
    · have ec : c+w*column b addr (z::xs)=(c+w*d)+(b*w)*column b addr xs := by
        change c+w*(d+b*column b addr xs)=_; ring
      have es : (s+dot b addr (z::xs))%m=(((s+z.1*d)%m)+dot b addr xs)%m := by
        change (s+(z.1*d+dot b addr xs))%m=_
        rw [Nat.mod_add_mod,Nat.add_assoc]
      rw [ec,es,List.length_cons,pow_succ',show w*(b*b^xs.length)=b*w*b^xs.length by ring]
      exact .while_true hy (.seq et eq) ek

end DetDLP.BitBorderColumn
end

section

namespace DetDLP.BorderedWords
open BorderedHermite PackedColumnWords
open OAI.Algorithms.SubexponentialSAT SqrtLogSpace

def remDigit (m : ℕ) (z : ℤ) := (z%(m:ℤ)).toNat

theorem remDigit_eq (m : ℕ) [NeZero m] (z : ℤ) : remDigit m z=((z:ZMod m).val) := by
  unfold remDigit; rw [← ZMod.val_intCast,Int.toNat_natCast]

theorem sign_value (z : ℤ) : BitWordFrames.value (encodeIntBin z)=
    (decide (z < 0)).toNat+2*z.natAbs := by
  simp [encodeIntBin,BitWordFrames.value,BitWordFrames.value_count]

theorem signed_rem (m : ℕ) [NeZero m] (z : ℤ) :
    let raw := BitWordFrames.value (encodeIntBin z)
    ((if raw%2=0 then raw/2 else (m-1)*(raw/2))%m)=remDigit m z := by
  intro raw
  have pos := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm : ((m-1:ℕ):ZMod m) = -1 := by rw [Nat.cast_sub (by omega),ZMod.natCast_self,Nat.cast_one,zero_sub]
  rw [remDigit_eq,← ZMod.val_natCast]
  apply congrArg ZMod.val
  rw [show raw= _ from sign_value z]
  by_cases hz : z < 0
  · simp only [hz,decide_true,Bool.toNat_true,Nat.add_mul_mod_self_left,Nat.reduceMod,Nat.reduceEqDiff,if_false,
      Nat.add_mul_div_left _ _ (by decide : 0 < 2),Nat.reduceDiv,zero_add,Nat.cast_mul,hm,neg_one_mul]
    rw [← Int.cast_natCast (R:=ZMod m) z.natAbs,Int.natCast_natAbs,abs_of_neg hz,Int.cast_neg,neg_neg]
  · simp only [hz,decide_false,Bool.toNat_false,zero_add,Nat.mul_mod_right,ite_true,Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    rw [← Int.cast_natCast (R:=ZMod m) z.natAbs,Int.natCast_natAbs,abs_of_nonneg (le_of_not_gt hz)]

theorem get_digit {n b : ℕ} (hb : 1 < b) (f : Fin n → ℕ) (hf : ∀ i,f i < b) (i : Fin n) :
    Nat.ofDigits b (List.ofFn f)/b^i.val%b=f i := by
  have hi : i.val < (List.ofFn f).length := by simpa using i.isLt
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i.val (by omega) _ (by intro a ha; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha; exact hf j),
    List.drop_eq_getElem_cons hi,Nat.ofDigits_cons,Nat.add_mul_mod_self_left,List.getElem_ofFn,Nat.mod_eq_of_lt (hf _)]

def row {n : ℕ} (m : ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :=
  Nat.ofDigits (m+1) (List.ofFn fun j => remDigit m (B i j))
def rows {n : ℕ} (m : ℕ) (a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) :=
  List.ofFn fun i => (a i,row m B i)

theorem small {m : ℕ} [NeZero m] (z : ℤ) : remDigit m z < m := by rw [remDigit_eq]; exact ZMod.val_lt _
theorem read_row {n m : ℕ} [NeZero m] (B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    BitBorderColumn.coord (m+1) ((m+1)^j.val) (row m B i)=remDigit m (B i j) :=
  get_digit (by have := Nat.pos_of_ne_zero (NeZero.ne m); omega) _ (fun t => (small _).trans_le (Nat.le_succ _)) j

theorem flatten {α : Type*} {k : ℕ} (f : α → List ℕ) (xs : List α) (h : ∀ i∈xs,(f i).length=k) (b : ℕ) :
    Nat.ofDigits b (xs.flatMap f)=Nat.ofDigits (b^k) (xs.map (fun i => Nat.ofDigits b (f i))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons,Nat.ofDigits_append,h x (by simp),ih (fun i hi => h _ (by simp [hi])),List.map_cons,Nat.ofDigits_cons]

theorem packed_input {n m : ℕ} (a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) :
    BitBorderColumn.packX ((m+1)^n) (rows m a B) =
      Nat.ofDigits (m+1) ((List.finRange n).flatMap fun i => (List.finRange n).map fun j => remDigit m (B i j)) := by
  rw [flatten (k:=n) _ _ (by simp)]
  simp [BitBorderColumn.packX,rows,row,List.map_ofFn,Function.comp_def,List.finRange]

def dotZ {n : ℕ} (a : Fin n → ℕ) (v : Fin n → ℤ) :=
  (List.finRange n).foldl (fun s i => s+(a i:ℤ)*v i) 0
def bordered {n : ℕ} (a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) : Array (Column (n+1)) :=
  Array.ofFn fun j => Vector.ofFn (Fin.cases (dotZ a (fun i => B i j)) (fun i => B i j))

theorem fold_sum {α : Type*} {A : Type*} [AddMonoid A] (f : α → A) (xs : List α) (s : A) :
    xs.foldl (fun v i => v+f i) s=s+(xs.map f).sum := by
  induction xs generalizing s with
  | nil => simp
  | cons i xs ih => simp [ih,add_assoc]

theorem dot_correct {n m : ℕ} [NeZero m] (a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    BitBorderColumn.dot (m+1) ((m+1)^j.val) (rows m a B)%m = remDigit m (dotZ a (fun i => B i j)) := by
  rw [remDigit_eq,← ZMod.val_natCast]
  apply congrArg ZMod.val
  have eq (i : Fin n) : ((remDigit m (B i j):ℕ):ZMod m)=(B i j:ZMod m) := by simp [remDigit_eq]
  simp [BitBorderColumn.dot,rows,List.map_ofFn,Function.comp_def,read_row,dotZ,fold_sum,
    List.sum_ofFn,List.finRange,eq]

theorem column_correct {n m : ℕ} [NeZero m] (a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    let b := m+1
    let raw := (bordered a B)[j.val]'(by simp [bordered])
    word b (raw.map (·%(m:ℤ))) = BitBorderColumn.dot b (b^j.val) (rows m a B)%m+
      b*BitBorderColumn.column b (b^j.val) (rows m a B) := by
  intro b raw
  rw [dot_correct,word,List.ofFn_succ,Nat.ofDigits_cons]
  have hd (i : Fin (n+1)) : digit (raw.map (·%(m:ℤ))) i =
      remDigit m (Fin.cases (dotZ a (fun k => B k j)) (fun k => B k j) i) := by
    simp [raw,bordered,digit,remDigit,Vector.get,Vector.getElem_map]
    rfl
  simp [hd,BitBorderColumn.column,rows,List.map_ofFn,Function.comp_def,read_row,b]

end DetDLP.BorderedWords
end

section

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

theorem signed_correct {m : ℕ} [NeZero m] (hm : 2 ≤ m) (z : ℤ) :
    digit true m (value (encodeIntBin z))=BorderedWords.remDigit m z := by
  let v := value (encodeIntBin z)
  rw [← BorderedWords.signed_rem]; change ((1+(m-2)*(v%2))*(v/2))%m=(if v%2=0 then v/2 else (m-1)*(v/2))%m
  rcases Nat.mod_two_eq_zero_or_one v with h|h
  · simp [h]
  · simp [h,show 1+(m-2)=m-1 by omega]

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

section

namespace DetDLP.BorderedColumnProgram
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open BitBorderColumn (state packA packX column dot command)
open BorderedWords

def out (m Q addr v power : ℕ) := state m Q addr 1 0 v power 0

theorem finish_ok (m Q addr c w s : ℕ) :
    Valid BitBorderColumn.finish (state m Q addr 1 0 c w s) ∧
    run BitBorderColumn.finish (state m Q addr 1 0 c w s) = out m Q addr (s+(m+1)*c) w := by
  constructor
  · simp [BitBorderColumn.finish,Valid,Op.Valid]
  · funext j; fin_cases j <;> rfl

theorem eval (m Q addr N : ℕ) (hm : 2 ≤ m) (hQ : 0 < Q) (haddr : 0 < addr)
    (xs : List (ℕ × ℕ)) (hh : ∀ z ∈ xs,z.1 < m+1 ∧ z.2 < Q)
    (hbase : ∀ z ∈ [m+1,Q,addr],z ≤ N)
    (hA : packA (m+1) xs ≤ N) (hX : packX Q xs ≤ N) (hpow : (m+1)^xs.length ≤ N) (r : Regs) :
    let b := m+1
    ∃ t rf,t ≤ xs.length*(BitBorderColumn.cost*(N.size+2)^2+2)+1000^4*(N.size+2)^2+2 ∧
      Eval command t ⟨r,frame (state m Q addr (packA b xs) (packX Q xs) 0 1 0)⟩
       ⟨rf,frame (out m Q addr (dot b addr xs%m+b*column b addr xs) (b^xs.length))⟩ := by
  intro b
  obtain ⟨rq,eq,hq⟩ := peek_eval (9:Fin 16) (state m Q addr (packA b xs) (packX Q xs) 0 1 0) r
  obtain ⟨t,rt,ht,et⟩ := BitBorderColumn.scan m Q addr hm hQ haddr xs hh 0 1 0 N
    (by decide) (by omega) (Nat.zero_mod _) hbase hA hX (by simpa using hpow) rq hq
  simp only [one_mul,zero_add] at et
  have hcol : column b addr xs < b^xs.length := by
    unfold column
    have hlen := List.length_map (f:=fun s : ℕ × ℕ => BitBorderColumn.coord b addr s.2) (as:=xs)
    rw [← hlen]
    apply Nat.ofDigits_lt_base_pow_length (by dsimp [b]; omega)
    intro z hz
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hz
    exact Nat.mod_lt _ (Nat.succ_pos _)
  have hmN := hbase (m+1) (by simp)
  have hQN := hbase Q (by simp)
  have haN := hbase addr (by simp)
  have hdot := Nat.mod_lt (dot b addr xs) (by omega : 0 < m)
  have pw : b^xs.length ≤ N := hpow
  have hreg (j : Fin 16) : state m Q addr 1 0 (column b addr xs) (b^xs.length) (dot b addr xs%m) j ≤ N := by
    fin_cases j <;> simp [state,Nat.div_eq_of_lt (by omega : 1 < m+1)] <;> omega
  obtain ⟨hf,rf,hf',ef⟩ := run_eval _ _ rt N.size (fun j => Nat.size_le_size (hreg j)) (finish_ok m Q addr _ _ _).1
  rw [(finish_ok m Q addr _ _ _).2] at ef
  change hf ≤ 1000^4*(N.size+2)^2 at hf'
  exact ⟨_,rf,by omega,.seq eq (.seq et ef)⟩

theorem actual {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ)
    (ha : ∀ i,a i < m) (j : Fin n) (N : ℕ) (r : Regs)
    (hN : ∀ z ∈ [m+1,(m+1)^n,packA (m+1) (rows m a B),packX ((m+1)^n) (rows m a B)],z ≤ N) :
    let b := m+1
    let Q := b^n
    let addr := b^j.val
    let xs := rows m a B
    let col := (bordered a B)[j.val]'(by simp [bordered])
    ∃ t rf,t ≤ n*(BitBorderColumn.cost*(N.size+2)^2+2)+1000^4*(N.size+2)^2+2 ∧
      Eval command t ⟨r,frame (state m Q addr (packA b xs) (packX Q xs) 0 1 0)⟩
       ⟨rf,frame (out m Q addr (PackedColumnWords.word b (col.map (·%(m:ℤ)))) Q)⟩ := by
  intro b Q addr xs col
  have L : xs.length=n := by simp [xs,rows]
  have bb : 1 < b := by dsimp [b]; omega
  have hQ : Q ≤ N := hN _ (by simp [Q,b])
  have had : addr ≤ Q := Nat.pow_le_pow_right (by omega : 0 < b) j.isLt.le
  have base : ∀ z ∈ [m+1,Q,addr],z ≤ N := by
    intro z hz; simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl
    · apply hN; simp
    · exact hQ
    · exact had.trans hQ
  have hh (z : ℕ × ℕ) (hz : z ∈ xs) : z.1 < m+1 ∧ z.2 < Q := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    refine ⟨(ha i).trans_le (Nat.le_succ _),?_⟩
    change Nat.ofDigits b (List.ofFn fun j => remDigit m (B i j)) < b^n
    have hh : ∀ x ∈ List.ofFn (fun j => remDigit m (B i j)), x < b := by
      intro x hx; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
      exact (small _).trans_le (Nat.le_succ _)
    simpa using Nat.ofDigits_lt_base_pow_length bb hh
  have H := eval m Q addr N hm (pow_pos (Nat.succ_pos _) _) (pow_pos (Nat.succ_pos _) _) xs hh base
    (hN _ (by simp [xs,b])) (hN _ (by simp [Q,b,xs])) (by rw [L]; exact hQ) r
  rw [L] at H
  rw [column_correct]
  exact H

end DetDLP.BorderedColumnProgram
end

section

namespace DetDLP.BorderTableMachine
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode BitRegisterCall
open BitBorderColumn (state packA packX)
open BorderedColumnProgram (out)
open BorderedWords

abbrev I := BitRegisterCode.Instr 24
def halves (v : Vars 16) (w : Vars 8) : Vars 24 := fun j => Fin.addCases (m:=16) (n:=8) (motive:=fun _ => ℕ) v w j
def keep (m Q addr A X acc place : ℕ) : Vars 8 :=
  ![A,X,acc,place,Q*(m+1),Q/(addr*(m+1)),0,1]
def start (m Q addr A X acc place : ℕ) := halves (state m Q addr A X 0 1 0) (keep m Q addr A X acc place)
def post : List I :=
  [⟨.mul,19,6,22⟩,⟨.add,18,22,18⟩,⟨.mul,19,20,19⟩,⟨.mul,3,1,3⟩,⟨.mul,3,1,22⟩,
   ⟨.quot,22,2,21⟩,⟨.add,16,15,4⟩,⟨.add,17,15,5⟩,⟨.add,15,15,6⟩,⟨.add,23,15,7⟩,
   ⟨.quot,1,4,9⟩,⟨.add,15,15,22⟩]
def sub := compiled BitBorderColumn.command (port (0:Fin 16)) (port (6:Fin 16))
def body : Code 24 := (subroutine sub (@left 16 8)).seq ((compile post).seq (peek (21:Fin 24)))
def command : Code 24 := (peek (21:Fin 24)).seq (.while 1 body)

theorem post_ok (m Q addr A X acc w z : ℕ) (ha : 0 < addr) :
    let old := halves (out m Q addr z Q) (keep m Q addr A X acc w)
    Valid post old ∧ run post old=start m Q (addr*(m+1)) A X (acc+w*z) (w*(Q*(m+1))) := by
  intro old
  have hp : 0 < addr*(m+1)*(m+1) := by positivity
  constructor
  · simp [post,Valid,Op.Valid,BitRegisterCode.Instr.step]
    exact ⟨hp,Nat.succ_pos _⟩
  · funext j; fin_cases j <;> rfl

def entry {m n : ℕ} (a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :=
  let v := (bordered a B)[j.val]'(by simp [bordered])
  PackedColumnWords.word (m+1) (v.map (·%(m:ℤ)))

def stepCost (n N : ℕ) := n*(BitBorderColumn.cost*(N.size+2)^2+2)+1000^4*(N.size+2)^2+1000^13*(N.size+2)^2+4

theorem one {n m : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ)
    (ha : ∀ i,a i < m) (j : Fin n) (N acc w : ℕ) (r : Regs) :
    let b := m+1
    let Q := b^n
    let addr := b^j.val
    let A := packA b (rows m a B)
    let X := packX Q (rows m a B)
    let z := entry (m:=m) a B j
    (∀ x∈[b,Q,A,X,z,Q*b,acc,w],x ≤ N) →
    ∃ t rf,t ≤ stepCost n N ∧ Eval body t
      ⟨r,frame (start m Q addr A X acc w)⟩
      ⟨rf,frame (start m Q (addr*b) A X (acc+w*z) (w*(Q*b)))⟩ ∧
      rf 1=decide (Q/(addr*b*b)≠0) := by
  intro b Q addr A X z sizes
  obtain ⟨t,rt,ht,et⟩ := BorderedColumnProgram.actual hm a B ha j N r (by
    intro x hx
    apply sizes; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    rcases hx with h|h|h|h <;> tauto)
  have call := call_left sub _ _ (keep m Q addr A X acc w) r rt (t+1) (compiled_halt_trace et _ _)
  have ad : 0<addr := pow_pos (Nat.succ_pos _) _
  have adQ : addr ≤ Q := Nat.pow_le_pow_right (Nat.succ_pos _) j.isLt.le
  let old := halves (out m Q addr z Q) (keep m Q addr A X acc w)
  have bN := sizes b (by simp)
  have QN := sizes Q (by simp)
  have A_N := sizes A (by simp)
  have X_N := sizes X (by simp)
  have zN := sizes z (by simp)
  have DN := sizes (Q*b) (by simp)
  have cN := sizes acc (by simp)
  have wN := sizes w (by simp)
  have gN := (Nat.div_le_self Q (addr*b)).trans QN
  have hbb : 1<b := by dsimp [b]; omega
  have le (j : Fin 24) : old j ≤ N := by
    fin_cases j <;> first | exact QN | exact bN | exact A_N | exact X_N | exact gN | exact zN | exact DN | exact cN | exact wN | exact adQ.trans QN | exact Nat.zero_le _ | change 1 ≤ N; omega | change m ≤ N; dsimp [b] at bN; omega | change 1/(m+1) ≤ N; exact (Nat.div_le_self ..).trans (by omega)
  obtain ⟨u,ru,hu,eu⟩ := run_eval post old rt N.size (fun j => Nat.size_le_size (le j)) (post_ok _ _ _ _ _ _ _ _ ad).1
  rw [(post_ok _ _ _ _ _ _ _ _ ad).2] at eu
  obtain ⟨rf,ef,hf⟩ := peek_eval (21:Fin 24) (start m Q (addr*b) A X (acc+w*z) (w*(Q*b))) ru
  refine ⟨_,rf,?_,.seq call (.seq eu ef),hf⟩
  change u ≤ 1000^13*(N.size+2)^2 at hu
  unfold stepCost; omega

end DetDLP.BorderTableMachine
end

section

namespace DetDLP.BorderTableTrace
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open BitBorderColumn (packA packX)
open BorderedWords BorderTableMachine

def prefixWord (D : ℕ) (xs : List ℕ) (k : ℕ) := Nat.ofDigits D (xs.take k)
theorem next {D : ℕ} (xs : List ℕ) {k : ℕ} (h : k<xs.length) :
    prefixWord D xs (k+1)=prefixWord D xs k+D^k*xs[k] := by
  unfold prefixWord
  rw [List.take_succ_eq_append_getElem h,Nat.ofDigits_append,List.length_take,Nat.min_eq_left h.le]
  simp

theorem entry_lt {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    BorderTableMachine.entry (m:=m) a B j < ((m+1)^n)*(m+1) := by
  rw [← pow_succ]
  apply PackedColumnWords.word_lt (by omega)
  intro i
  have M : 0 < (m:ℤ) := by exact_mod_cast (by omega : 0 < m)
  let v := (bordered a B)[j.val]'(by simp [bordered])
  change 0 ≤ (v.map (·%(m:ℤ)))[i.val] ∧ (v.map (·%(m:ℤ)))[i.val] ≤ (m:ℤ)
  simp only [Vector.getElem_map]
  exact ⟨Int.emod_nonneg _ M.ne',(Int.emod_lt_of_pos _ M).le⟩

def list {n} (m : ℕ) (a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) :=
  List.ofFn (BorderTableMachine.entry (m:=m) a B)

theorem list_eq {n} (m : ℕ) (a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) :
    list m a B=((BorderedBitIO.columns a B).map fun v => v.map (·%(m:ℤ))).toList.map (PackedColumnWords.word (m+1)) := by
  apply List.ext_getElem (by simp [list,BorderedBitIO.columns])
  intro i l h
  simp [list,BorderTableMachine.entry,BorderedBitIO.columns,bordered,dotZ,Vector.get]

theorem output {n} (m : ℕ) (a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) :
    prefixWord ((m+1)^(n+1)) (list m a B) n+((m+1)^(n+1))^n=
      BorderedBitIO.serialize m ((BorderedBitIO.columns a B).map fun v => v.map (·%(m:ℤ))) := by
  let xs := list m a B
  have L : xs.length=n := by simp [xs,list]
  change Nat.ofDigits _ (xs.take n)+_ = Nat.ofDigits _ (_++[1])
  rw [Nat.ofDigits_append]
  change _=Nat.ofDigits _ (((BorderedBitIO.columns a B).map _).toList.map (PackedColumnWords.word (m+1)))+_
  rw [← list_eq]
  have take : xs.take n=xs := by rw [← L,List.take_length]
  rw [take]
  simp [BorderedBitIO.columns,xs]

theorem trace {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ)
    (ha : ∀ i,a i < m) (N k d : ℕ) (hk : k+d=n) (r : Regs) :
    let b := m+1
    let Q := b^n
    let D := Q*b
    let xs := list m a B
    let A := packA b (rows m a B)
    let X := packX Q (rows m a B)
    let st (j : ℕ) := start m Q (b^j) A X (prefixWord D xs j) (D^j)
    (∀ z∈[b,Q,D,A,X,D^n],z ≤ N) → r 1=decide (Q/(b^k*b)≠0) →
    ∃ t rf,t ≤ d*(stepCost n N+1)+1 ∧ Eval (.while 1 body) t ⟨r,frame (st k)⟩ ⟨rf,frame (st n)⟩ := by
  intro b Q D xs A X st sizes hg
  have hb : 1 < b := by dsimp [b]; omega
  have hD : 1 < D := by dsimp [D]; have := Nat.one_le_pow n b (by omega); dsimp [Q]; nlinarith only [this,hb,Nat.mul_le_mul_right b this]
  have L : xs.length=n := by simp [xs,list]
  have guard (k : ℕ) : (Q/(b^k*b)≠0) ↔ k<n := by
    rw [←pow_succ,←Nat.pos_iff_ne_zero,Nat.div_pos_iff,and_iff_right (pow_pos (by omega) _)]
    exact Nat.pow_le_pow_iff_right hb
  induction d generalizing k r with
  | zero =>
    have e : k=n := by omega
    subst k
    have h : r 1=false := by simpa [guard] using hg
    exact ⟨1,r,by simp,.while_false h⟩
  | succ d ih =>
    have kl : k<n := by omega
    let j : Fin n := ⟨k,kl⟩
    have hlist (z : ℕ) (hz : z∈xs) : z<D := by
      obtain ⟨f,rfl⟩ := List.mem_ofFn.mp hz
      exact entry_lt hm a B f
    have use := Nat.ofDigits_lt_base_pow_length hD (fun z (hz : z∈xs.take k) => hlist z (List.mem_of_mem_take hz))
    have plen : (xs.take k).length=k := by simp [L,Nat.min_eq_left kl.le]
    rw [plen] at use
    have endN : D^n ≤ N := sizes _ (by simp)
    have pN := (Nat.pow_le_pow_right (by omega : 0<D) kl.le).trans endN
    have eN := (entry_lt hm a B j).le.trans (sizes D (by simp))
    have kN : prefixWord D xs k ≤ N := use.le.trans pN
    obtain ⟨t,rt,ht,et,hg'⟩ := one hm a B ha j N (prefixWord D xs k) (D^k) r (by
      intro z hz; simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with h|h|h|h|h|h|h|h <;> subst z <;> first | exact pN | exact kN | exact eN | apply sizes; simp [b,Q,D,A,X])
    have e : xs[k]'(by omega)=BorderTableMachine.entry (m:=m) a B j := by simp [xs,list,j]
    have agree : start m Q (b^j.val*b) A X (prefixWord D xs k+D^k*BorderTableMachine.entry (m:=m) a B j) (D^k*D)=st (k+1) := by
      dsimp only [st]; rw [next xs (by omega),e,pow_succ,pow_succ]
    rw [agree] at et
    obtain ⟨v,rv,hv,ev⟩ := ih (k+1) (by omega) rt (by simpa only [pow_succ] using hg')
    have hh : r 1=true := by rw [hg]; exact decide_eq_true ((guard k).mpr kl)
    refine ⟨t+v+1,rv,?_,.while_true hh et ev⟩
    rw [Nat.succ_mul]; omega

end DetDLP.BorderTableTrace
end

section

namespace DetDLP.UpdateInputs
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls SqrtLogSpace
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open UpdateCosts
instance (z : Input) : NeZero z.m := ⟨by have := z.valid.1; omega⟩
def raw (z : Input) := encodeCosetUpdateInput z.m z.x z.B z.a z.c
def radix (z : Input) := z.m+1
def Q (z : Input) := (radix z)^z.n
def D (z : Input) := Q z*radix z
def expCap (z : Input) := (raw z).length+1+(radix z).size*(z.n+1)^2
def cap (z : Input) := 2^(expCap z)

theorem n_bnd : Bnd (fun z => z.n) := bnd_mono base_bnd (by intro z; dsimp [U]; omega)
theorem raw_bnd : Bnd (fun z => (raw z).length) := by
  apply bnd_mono (bnd_mul (const_bnd 100) (bnd_pow base_bnd 3))
  intro z
  obtain ⟨_,_,hx,ha,hc,hB⟩ := z.valid
  exact CosetTapeBounds.input_bound z.x z.a z.B z.c (fun i => (hx i).le) (fun i => (ha i).le) hc.le hB

theorem radix_bnd : Bnd (fun z => (radix z).size) := by
  apply bnd_mono base_bnd
  intro z
  have h := Nat.le_pow_clog (by decide : 1<2) z.m
  have pos := Nat.two_pow_pos (bitLen z.m)
  have b : (radix z).size ≤ bitLen z.m+2 := by
    apply Nat.size_le.mpr; change z.m+1 < 2^(bitLen z.m+2)
    change z.m ≤ 2^(bitLen z.m) at h; rw [pow_add]; norm_num; omega
  dsimp [U]; omega

theorem cap_bnd : Bnd (fun z => (cap z).size) := by
  have he : Bnd expCap := bnd_add (bnd_add raw_bnd (const_bnd 1))
    (bnd_mul radix_bnd (bnd_pow (bnd_add n_bnd (const_bnd 1)) 2))
  simpa only [cap,Nat.size_pow] using bnd_add he (const_bnd 1)

theorem rawCap (z : Input) : 2^((raw z).length+1) ≤ cap z :=
  Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..)
theorem radixCap (z : Input) {t : ℕ} (h : t ≤ (z.n+1)^2) : (radix z)^t ≤ cap z := by
  apply (Nat.pow_le_pow_left (Nat.lt_size_self (radix z)).le t).trans
  rw [←pow_mul]
  apply Nat.pow_le_pow_right (by decide)
  exact (Nat.mul_le_mul_left _ h).trans (Nat.le_add_left ..)

def unsignedWords {n} (f : Fin n → ℕ) := (List.ofFn f).map countWord
def matrixList (z : Input) := (List.finRange z.n).flatMap fun i => (List.finRange z.n).map (fun j => z.B i j)
def matrixWords (z : Input) := (matrixList z).map encodeIntBin
def A (z : Input) := BitBorderColumn.packA (radix z) (BorderedWords.rows z.m z.a z.B)
def X (z : Input) := BitBorderColumn.packX (Q z) (BorderedWords.rows z.m z.a z.B)
def unsignedPacked {n} (m : ℕ) (f : Fin n → ℕ) := Nat.ofDigits (m+1) (List.ofFn f)
theorem unsigned_eq {n m} (f : Fin n → ℕ) : FramedDigitScan.packed false m (unsignedWords f)=unsignedPacked m f := by
  simp [FramedDigitScan.packed,unsignedWords,FramedDigitScan.digit,Function.comp_def,BitWordFrames.value_count,unsignedPacked]
theorem matrix_eq (z : Input) : FramedDigitScan.packed true z.m (matrixWords z)=X z := by
  rw [X,Q,radix,BorderedWords.packed_input]
  simp [FramedDigitScan.packed,matrixWords,matrixList,List.map_map,Function.comp_def,
    FramedDigitScan.signed_correct z.valid.1,List.map_flatMap]
theorem A_eq (z : Input) : A z=unsignedPacked z.m z.a+Q z := by
  simp [A,BitBorderColumn.packA,BitMatrixPass.table,BorderedWords.rows,Nat.ofDigits_append,List.map_ofFn,
    unsignedPacked,Q,radix,Function.comp_def]

theorem encode_id_map {α} (f : α → List Bool) (xs : List α) :
    Encoding.encodeList id (xs.map f)=Encoding.encodeList f xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList,ih]
theorem word_length {xs : List (List Bool)} {w : List Bool} (h : w∈xs) :
    w.length ≤ (Encoding.encodeList id xs).length := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl|h
    · exact BinaryUpdateFields.head_length _ _
    · exact (ih h).trans (BinaryUpdateFields.tail_length _ _)

theorem word_lengths (z : Input) :
    (Encoding.encodeList id (unsignedWords z.x)).length ≤ (raw z).length ∧
    (Encoding.encodeList id (unsignedWords z.a)).length ≤ (raw z).length ∧
    (Encoding.encodeList id (matrixWords z)).length ≤ (raw z).length := by
  simp only [unsignedWords,matrixWords,encode_id_map]
  let R := encodeCosetRep z.x z.B
  let Ux := encodeNatListBin (List.ofFn z.x)
  let Ua := encodeNatListBin (List.ofFn z.a)
  let Bx := Encoding.encodeList encodeIntBin (matrixList z)
  let outer := [countWord z.m,countWord z.n,R,Ua,countWord z.c]
  have H : R.length ≤ (raw z).length := word_length (xs:=outer) (by simp [outer])
  change Ux.length ≤ (raw z).length ∧ Ua.length ≤ (raw z).length ∧ Bx.length ≤ (raw z).length
  exact ⟨(word_length (xs:=[Ux,Bx]) (by simp)).trans H,word_length (xs:=outer) (by simp [outer]),
    (word_length (xs:=[Ux,Bx]) (by simp)).trans H⟩

theorem matrix_len (z : Input) : (matrixWords z).length=z.n*z.n := by
  simp [matrixWords,matrixList,List.length_flatMap,Finset.sum_const]

theorem scan_exec (sgn : Bool) (ws : Input → List (List Bool)) (len : Input → ℕ)
    (hl : ∀ z,(ws z).length=len z) (hlen : Bnd len)
    (hb : ∀ z,(Encoding.encodeList id (ws z)).length ≤ (raw z).length)
    (hd : ∀ z x,x∈ws z → FramedDigitScan.digit sgn z.m (BitWordFrames.value x) < z.m+1)
    (hpow : ∀ z,len z ≤ (z.n+1)^2) :
    let S (z : Input) := SerializedFieldCall.merge SerializedFieldCall.clean
      (FramedDigitScan.data z.m (BitWordFrames.word (Encoding.encodeList id (ws z))) 0 1)
    let T (z : Input) := SerializedFieldCall.merge SerializedFieldCall.clean
      (FramedDigitScan.data z.m (BitWordFrames.word [false]) (FramedDigitScan.packed sgn z.m (ws z)) ((radix z)^len z))
    Executes (FramedDigitScan.command sgn) (bank S) (bank T) := by
  intro S T
  let C := FramedDigitScan.C
  apply of_bound (bnd_add (bnd_mul hlen (bnd_add (bnd_mul (bnd_mul (const_bnd C) (bnd_add raw_bnd (const_bnd 4)))
      (bnd_pow (bnd_add cap_bnd (const_bnd 2)) 2)) (const_bnd 1))) (const_bnd 2))
  intro z r
  obtain ⟨rq,eq,hq⟩ := peek_eval (SerializedFieldCall.high (9:Fin 13)) (S z) r
  obtain ⟨t,rt,ht,et⟩ := FramedDigitScan.scan sgn z.m (cap z) (raw z).length z.valid.1 (ws z)
    (hd z) (by simpa only [pow_one,radix] using radixCap z (t:=1) (Nat.one_le_pow _ _ (by omega))) (rawCap z) (hb z) 0 1 (by decide) (by simpa only [one_mul,hl,radix] using radixCap z (hpow z)) rq hq
  simp only [zero_add,one_mul,hl] at et ht
  exact ⟨1+t,rt,by dsimp only [C]; omega,.seq eq et⟩

end DetDLP.UpdateInputs
end

section

namespace DetDLP.BorderPhaseRuns
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls SqrtLogSpace
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open UpdateCosts UpdateInputs
open SerializedFieldCall (merge clean)
open BitWordFrames (word)

def parseStart (z : Input) : Vars 21 := merge clean ![word (raw z),0,0,0,0,0,0,0,0,0,0]
def parsed (z : Input) : Vars 21 := merge clean (BinaryUpdateFields.fields z.m z.x z.a z.B z.c)
theorem parse : Executes (BinaryUpdateFields.sequence BinaryUpdateFields.pops) (bank parseStart) (bank parsed) := by
  let expense := (BinaryUpdateFields.pops.length*SerializedFieldCall.cost)
  apply of_bound (bnd_mul (bnd_mul (const_bnd expense) (bnd_add raw_bnd (const_bnd 4)))
    (bnd_pow (bnd_add (bnd_add (bnd_add raw_bnd (const_bnd 1)) (const_bnd 1)) (const_bnd 2)) 2))
  intro z r
  obtain ⟨t,rf,ht,et⟩ := BinaryUpdateFields.parses_eval (BinaryUpdateFields.decode z.m z.x z.a z.B z.c) (by
    intro j; have H := (BinaryUpdateFields.word_bound (raw z)).le
    fin_cases j <;> first | exact H | exact Nat.zero_le _) r
  refine ⟨t,rf,?_,et⟩
  simpa only [raw,expense,Nat.size_pow,Nat.mul_assoc] using ht

def scanStart (z : Input) (xs : List (List Bool)) : Vars 23 :=
  merge clean (FramedDigitScan.data z.m (word (Encoding.encodeList id xs)) 0 1)
def scanEnd (z : Input) (v power : ℕ) : Vars 23 :=
  merge clean (FramedDigitScan.data z.m (word [false]) v power)

theorem unsigned_run (f : (z : Input) → Fin z.n → ℕ) (small : ∀ z i, f z i < z.m)
    (len : ∀ z,(Encoding.encodeList id (unsignedWords (f z))).length ≤ (raw z).length) :
    Executes (FramedDigitScan.command false) (bank fun z => scanStart z (unsignedWords (f z)))
      (bank fun z => scanEnd z (unsignedPacked z.m (f z)) (Q z)) := by
  have e := scan_exec false (fun z => unsignedWords (f z)) (fun z => z.n)
    (by simp [unsignedWords]) n_bnd len (by
      intro z x hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hy
      simpa [FramedDigitScan.digit,BitWordFrames.value_count] using (small z i).trans (Nat.lt_succ_self _))
    (by intro z; nlinarith only [Nat.zero_le (z.n^2)])
  simpa only [scanStart,scanEnd,unsigned_eq,Q] using e
theorem signed_run : Executes (FramedDigitScan.command true) (bank fun z => scanStart z (matrixWords z))
      (bank fun z => scanEnd z (X z) ((radix z)^(z.n*z.n))) := by
  have e := scan_exec true matrixWords (fun z => z.n*z.n) matrix_len (bnd_mul n_bnd n_bnd)
    (fun z => (word_lengths z).2.2) (by
      intro z x hx
      obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
      rw [FramedDigitScan.signed_correct z.valid.1]
      exact (BorderedWords.small _).trans (Nat.lt_succ_self _))
    (by intro z; nlinarith)
  simpa only [scanStart,scanEnd,matrix_eq] using e

def tableState (z : Input) (j : ℕ) : Vars 24 :=
  BorderTableMachine.start z.m (Q z) ((radix z)^j) (A z) (X z)
    (BorderTableTrace.prefixWord (D z) (BorderTableTrace.list z.m z.a z.B) j) ((D z)^j)

theorem fullTable : Executes BorderTableMachine.command (bank fun z => tableState z 0) (bank fun z => tableState z z.n) := by
  let S (z : Input) := ((cap z).size+2)^2
  have sB : Bnd S := bnd_pow (bnd_add cap_bnd (const_bnd 2)) 2
  have stB : Bnd (fun z => BorderTableMachine.stepCost z.n (cap z)) :=
    bnd_add (bnd_add (bnd_add (bnd_mul n_bnd (bnd_add (bnd_mul (const_bnd BitBorderColumn.cost) sB) (const_bnd 2)))
      (bnd_mul (const_bnd (1000^4)) sB)) (bnd_mul (const_bnd (1000^13)) sB)) (const_bnd 4)
  apply of_bound (bnd_add (bnd_mul n_bnd (bnd_add stB (const_bnd 1))) (const_bnd 2))
  intro z r
  have hm := z.valid.1
  have hn := z.valid.2.1
  have hQ := radixCap z (t:=z.n) (by nlinarith only [Nat.zero_le (z.n^2)])
  have hD := radixCap z (t:=z.n+1) (by nlinarith only [Nat.zero_le (z.n^2),Nat.zero_le z.n])
  have hDN := radixCap z (t:=(z.n+1)*z.n) (by nlinarith)
  have b : 1 < radix z := by dsimp [radix]; omega
  have ha : unsignedPacked z.m z.a < Q z := by
    have H := Nat.ofDigits_lt_base_pow_length b (l:=List.ofFn z.a) (by
      intro v hv; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
      exact (z.valid.2.2.2.1 i).trans (Nat.lt_succ_self _))
    simpa [Q,unsignedPacked,radix] using H
  have hA : A z ≤ cap z := by
    rw [A_eq]; apply le_trans _ hD; rw [pow_succ]
    have H := Nat.mul_le_mul_left (Q z) b
    change _ ≤ Q z*radix z; omega
  have hX : X z ≤ cap z := by
    rw [←matrix_eq]
    have H := Nat.ofDigits_lt_base_pow_length b (l:=(matrixWords z).map (fun x => FramedDigitScan.digit true z.m (BitWordFrames.value x))) (by
      intro d hd; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hd
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
      exact (FramedDigitScan.signed_correct z.valid.1 v) ▸ (BorderedWords.small v).trans (Nat.lt_succ_self _))
    rw [List.length_map,matrix_len] at H
    exact H.le.trans (radixCap z (by nlinarith))
  have hb : radix z ≤ cap z := by simpa using radixCap z (t:=1) (Nat.one_le_pow _ _ (by omega))
  have hD' : D z ≤ cap z := by simpa [D,Q,pow_succ] using hD
  have hDN' : D z^z.n ≤ cap z := by rwa [pow_mul,pow_succ] at hDN
  obtain ⟨rq,eq,hg⟩ := peek_eval (21:Fin 24) (tableState z 0) r
  obtain ⟨t,rt,ht,et⟩ := BorderTableTrace.trace hm z.a z.B z.valid.2.2.2.1 (cap z) 0 z.n (by omega) rq
    (by intro v hv; simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with q|q|q|q|q|q <;> subst v <;> first | exact hb | exact hQ | exact hD' | exact hA | exact hX | exact hDN') hg
  exact ⟨1+t,rt,by omega,.seq eq et⟩

end DetDLP.BorderPhaseRuns
end

section

namespace DetDLP.BorderMoves
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls SqrtLogSpace
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open UpdateCosts UpdateInputs BorderPhaseRuns
open BitWordFrames (word)
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
abbrev V := Vars 47
abbrev I := BitRegisterCode.Instr 47
def av (z : Input) := word (encodeNatListBin (List.ofFn z.a))
def xv (z : Input) := word (encodeNatListBin (List.ofFn z.x))
def bv (z : Input) := word (Encoding.encodeList encodeIntBin (matrixList z))
def allcols (z : Input) := BorderedBitIO.serialize z.m ((BorderedBitIO.columns z.a z.B).map fun v => v.map (·%(z.m:ℤ)))
def tableValue (z : Input) := BorderTableTrace.prefixWord (D z) (BorderTableTrace.list z.m z.a z.B) z.n

def seed (z : Input) (F : ℕ) : Vars 47 :=
  ![0,0,0,0,0,0,0,0,0,0,word (raw z),0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,F]
def parserTail (z : Input) (F : ℕ) : Vars 26 :=
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,F]
def aTail (z : Input) (F : ℕ) : Vars 24 :=
  ![0,z.m,av z,bv z,xv z,z.c,z.m-2,2,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,F]
def xTail (z : Input) (F : ℕ) : Vars 24 :=
  ![0,z.m,av z,bv z,xv z,z.c,z.m-2,2,0,A z,Q z,0,0,0,1,0,0,0,0,0,0,0,0,F]
def bTail (z : Input) (F : ℕ) : Vars 24 :=
  ![0,z.m,av z,bv z,xv z,z.c,z.m-2,2,0,A z,Q z,unsignedPacked z.m z.x,0,0,1,0,0,0,0,0,0,0,0,F]
def tableTail (z : Input) (F : ℕ) : Vars 23 :=
  ![z.m,av z,bv z,xv z,z.c,z.m-2,2,0,A z,Q z,unsignedPacked z.m z.x,X z,0,1,0,0,0,0,0,0,0,0,F]
def ready (z : Input) (F : ℕ) : Vars 47 :=
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,z.m,radix z,D z,1,1,allcols z,Q z,1,0]

def startParse (z : Input) (F : ℕ) : V := join (parseStart z) (parserTail z F)
def endParse (z : Input) (F : ℕ) : V := join (parsed z) (parserTail z F)
def startA (z : Input) (F : ℕ) : V := join (scanStart z (unsignedWords z.a)) (aTail z F)
def endA (z : Input) (F : ℕ) : V := join (scanEnd z (unsignedPacked z.m z.a) (Q z)) (aTail z F)
def startX (z : Input) (F : ℕ) : V := join (scanStart z (unsignedWords z.x)) (xTail z F)
def endX (z : Input) (F : ℕ) : V := join (scanEnd z (unsignedPacked z.m z.x) (Q z)) (xTail z F)
def startB (z : Input) (F : ℕ) : V := join (scanStart z (matrixWords z)) (bTail z F)
def endB (z : Input) (F : ℕ) : V := join (scanEnd z (X z) ((radix z)^(z.n*z.n))) (bTail z F)
def startTable (z : Input) (F : ℕ) : V := join (tableState z 0) (tableTail z F)
def endTable (z : Input) (F : ℕ) : V := join (tableState z z.n) (tableTail z F)

def cp (src dst : Fin 47) : I := ⟨.add,src,36,dst⟩

def initParser : List I :=
  [cp 37 2,cp 37 8,⟨.add,37,37,9⟩]
def toA : List I :=
  [cp 11 24,cp 14 25,cp 17 26,cp 16 27,cp 15 28,cp 9 30,
   ⟨.add,24,37,11⟩,⟨.mul,24,24,29⟩,⟨.quot,11,29,29⟩,⟨.mul,29,29,29⟩,⟨.quot,24,29,29⟩,cp 24 10,
   cp 29 12,cp 25 13,cp 36 14,cp 37 15,cp 36 16,cp 36 17,
   cp 36 18,cp 36 20,cp 37 21,cp 30 22,⟨.rem,30,13,19⟩]
def toX : List I :=
  [⟨.add,14,15,32⟩,cp 15 33,cp 27 13,cp 36 14,cp 37 15,⟨.rem,30,13,19⟩]
def toB : List I :=
  [cp 14 34,cp 26 13,cp 36 14,cp 37 15,⟨.rem,30,13,19⟩]
def toTable : List I :=
  [cp 14 35,cp 24 0,cp 11 1,cp 33 2,cp 37 3,cp 32 4,
   cp 35 5,cp 36 6,cp 37 7,cp 36 8,⟨.quot,1,4,9⟩,cp 36 10,
   cp 36 11,cp 36 12,cp 36 13,cp 37 14,cp 36 15,cp 32 16,
   cp 35 17,cp 36 18,cp 37 19,⟨.mul,2,1,20⟩,⟨.quot,1,2,21⟩,cp 36 22,
   cp 37 23]
def finish : List I :=
  [cp 24 38,cp 1 39,cp 20 40,cp 37 41,cp 37 42,⟨.add,18,19,43⟩,
   cp 33 44,cp 37 45,cp 36 46,cp 36 0,cp 36 1,cp 36 2,
   cp 36 3,cp 36 4,cp 36 5,cp 36 6,cp 36 7,cp 36 8,
   cp 36 9,cp 36 10,cp 36 11,cp 36 12,cp 36 13,cp 36 14,
   cp 36 15,cp 36 16,cp 36 17,cp 36 18,cp 36 19,cp 36 20,
   cp 36 21,cp 36 22,cp 36 23,cp 36 24,cp 36 25,cp 36 26,
   cp 36 27,cp 36 28,cp 36 29,cp 36 30,cp 36 31,cp 36 32,
   cp 36 33,cp 36 34,cp 36 35,cp 36 37]

theorem start_ok (z : Input) (F : ℕ) : run initParser (seed z F)=startParse z F := by
  funext j; fin_cases j <;> rfl

theorem unsigned_word {n : ℕ} (f : Fin n → ℕ) : word (Encoding.encodeList id (unsignedWords f))=word (encodeNatListBin (List.ofFn f)) := by
  unfold unsignedWords encodeNatListBin; rw [encode_id_map]
theorem matrix_word (z : Input) : word (Encoding.encodeList id (matrixWords z))=bv z := by simp [bv,matrixWords,encode_id_map]
theorem minus_two (m : ℕ) (hm : 2 ≤ m) :
    (m*m/(m+1))*(m*m/(m+1))/m=m-2 := by
  rw [BitPackedPivot.square_quot m (by omega)]
  simpa [show m-1+1=m by omega,show m-1-1=m-2 by omega] using BitPackedPivot.square_quot (m-1) (by omega)

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
theorem A_ok (z : Input) (F : ℕ) : run toA (endParse z F)=startA z F := by
  funext j; fin_cases j <;> first | rfl | exact minus_two _ z.valid.1 | exact (unsigned_word _).symm |
    exact congrArg (fun v : ℕ => v%2) (unsigned_word _).symm

theorem X_ok (z : Input) (F : ℕ) : run toX (endA z F)=startX z F := by
  funext j; fin_cases j <;> first | rfl | exact (A_eq z).symm | exact (unsigned_word _).symm |
    exact congrArg (fun v : ℕ => v%2) (unsigned_word _).symm
theorem B_ok (z : Input) (F : ℕ) : run toB (endX z F)=startB z F := by
  funext j; fin_cases j <;> first | rfl | exact (matrix_word z).symm |
    exact congrArg (fun v : ℕ => v%2) (matrix_word z).symm
theorem table_ok (z : Input) (F : ℕ) : run toTable (endB z F)=startTable z F := by
  funext j; fin_cases j <;> first | rfl | change _= Q z/(1*radix z); rw [one_mul]; rfl

theorem ready_ok (z : Input) (F : ℕ) : run finish (endTable z F)=ready z F := by
  have e := BorderTableTrace.output z.m z.a z.B
  rw [pow_succ (z.m+1) z.n] at e
  funext j; fin_cases j <;> first | rfl | exact e

theorem validated (z : Input) (F : ℕ) :
    BitRegisterCode.Valid initParser (seed z F) ∧ BitRegisterCode.Valid toA (endParse z F) ∧
    BitRegisterCode.Valid toX (endA z F) ∧ BitRegisterCode.Valid toB (endX z F) ∧
    BitRegisterCode.Valid toTable (endB z F) ∧ BitRegisterCode.Valid finish (endTable z F) := by
  have m := z.valid.1
  have pos : 0 < z.m := by omega
  have b : 0 < z.m+1 := Nat.succ_pos _
  have two : 0 < (2:ℕ) := by decide
  constructor
  · simp [initParser,cp,BitRegisterCode.Valid,Op.Valid]
  constructor
  · simp [toA,cp,BitRegisterCode.Valid,Op.Valid,BitRegisterCode.Instr.step]
    exact ⟨b,pos,two⟩
  constructor
  · simp [toX,cp,BitRegisterCode.Valid,Op.Valid,BitRegisterCode.Instr.step]
    exact two
  constructor
  · simp [toB,cp,BitRegisterCode.Valid,Op.Valid,BitRegisterCode.Instr.step]
    exact two
  constructor
  · simp [toTable,cp,BitRegisterCode.Valid,Op.Valid,BitRegisterCode.Instr.step]
    exact b
  · simp [finish,cp,BitRegisterCode.Valid,Op.Valid]
end DetDLP.BorderMoves
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

namespace DetDLP.BorderInputProgram
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls SqrtLogSpace
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open UpdateCosts UpdateInputs BorderPhaseRuns BorderMoves
open BitWordFrames (word)

def Path {s} (A B : Input → St s) := ∃ q : Cmd 8 s,Executes q A B

theorem append {s} {a b d : Input → St s} (p : Path a b) {q : Cmd 8 s} (e : Executes q b d) : Path a d := by
  obtain ⟨c,h⟩ := p; exact ⟨c.seq q,compose h e⟩
theorem width {s} [NeZero s] {a b : Input → St s} (h : Path a b) (w : Width a) : Width b := by
  obtain ⟨_,e⟩ := h; exact output_width e w
theorem advance {a : Input → St 55} {b d : Input → V} (p : Path a (bank b)) (w : Width a)
    (c : List BorderMoves.I) (hv : ∀ z,BitRegisterCode.Valid c (b z)) (eq : ∀ z,run c (b z)=d z) : Path a (bank d) :=
  append p (straight c b d (width p w) hv eq)

theorem common (F : Input → ℕ) (w : Width (bank fun z => seed z (F z))) :
    Path (bank fun z => seed z (F z)) (bank fun z => endX z (F z)) := by
  let src := bank (fun z => seed z (F z))
  have a : Path src (bank fun z => startParse z (F z)) :=
    ⟨_,straight initParser _ _ w (fun z => (validated z (F z)).1) (fun z => start_ok z (F z))⟩
  have b := append a (push_left (fun z => parserTail z (F z)) parse)
  have c := advance b w toA (fun z => (validated z (F z)).2.1) (fun z => A_ok z (F z))
  have d := append c (push_left (fun z => aTail z (F z)) (unsigned_run (fun z => z.a)
    (fun z => z.valid.2.2.2.1) (fun z => (word_lengths z).2.1)))
  have e := advance d w toX (fun z => (validated z (F z)).2.2.1) (fun z => X_ok z (F z))
  exact append e (push_left (fun z => xTail z (F z)) (unsigned_run (fun z => z.x)
    (fun z => z.valid.2.2.1) (fun z => (word_lengths z).1)))

theorem prepare (w : Width (bank fun z => seed z 0)) :
    Path (bank fun z => seed z 0) (bank fun z => ready z 0) := by
  have a := common (fun _ => 0) w
  have b := advance a w toB (fun z => (validated z 0).2.2.2.1) (fun z => B_ok z 0)
  have c := append b (push_left (fun z => bTail z 0) signed_run)
  have d := advance c w toTable (fun z => (validated z 0).2.2.2.2.1) (fun z => table_ok z 0)
  have e := append d (push_left (fun z => tableTail z 0) fullTable)
  exact advance e w finish (fun z => (validated z 0).2.2.2.2.2) (fun z => ready_ok z 0)

set_option maxRecDepth 10000
theorem seed_stacks (z : Input) :
    frame (seed z 0)=Function.update (Function.update (fun _ : Fin 55 => []) 18 (word (raw z)).bits) 45 [true] := by
  funext j; fin_cases j <;> first | rfl | exact (by decide : (1:ℕ).bits=[true])
theorem seed_width : Width (bank fun z => seed z 0) := by
  obtain ⟨k,hk⟩ := bnd_add raw_bnd (const_bnd 1)
  refine ⟨k,fun z j => ?_⟩
  change (frame (seed z 0) j).length ≤ _
  rw [seed_stacks]; simp only [Function.update_apply,BitWordFrames.bits]
  have h : (raw z).length+1 ≤ (U z)^k := hk z
  split_ifs <;> simp <;> omega
theorem final_stacks (z : Input) : frame (ready z 0)=BorderedBitIO.staged z.m (BorderedBitIO.columns z.a z.B) := by
  have hD : (z.m+1)^(z.n+1)=D z := pow_succ .. 
  have hQ : D z/(z.m+1)=Q z := Nat.mul_div_cancel _ (Nat.succ_pos _)
  funext j; fin_cases j <;> first | rfl |
    exact congrArg Nat.bits hD.symm | exact congrArg Nat.bits (hD ▸ hQ).symm
end DetDLP.BorderInputProgram
end

section

namespace DetDLP.BinaryPreparation
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode
open UpdateCosts UpdateInputs BorderMoves BorderInputProgram
open BitWordFrames (word)
open BorderedBitIO (backup initialStacks withBackup)

abbrev lowPort (s : ℕ) (j : Fin 55) := j.castAdd (s+2)
theorem off (s : ℕ) (j : Fin 55) (i : Fin (s+2)) : lowPort s j ≠ Fin.natAdd 55 i := by
  intro e; have h := congrArg Fin.val e; change j.val=55+i.val at h; omega
theorem twoLow (s : ℕ) (j k : Fin 55) (h : j ≠ k) : lowPort s j ≠ lowPort s k :=
  fun e => h (Fin.castAdd_injective _ _ e)
theorem at_start (s : ℕ) (z : Input) :
    initialStacks s (raw z)=withBackup s (fun _ => []) (raw z) := by
  funext j; refine Fin.addCases (m:=55) (n:=s+2)
    (motive:=fun j => initialStacks s (raw z) j=withBackup s (fun _ => []) (raw z) j) (fun i => ?_) (fun i => ?_) j
  · simp [initialStacks,withBackup,backup,off]
  · simp [initialStacks,withBackup,backup,Fin.natAdd_inj]
theorem update_low (s : ℕ) (q : St 55) (xs w : List Bool) (j : Fin 55) :
    Function.update (withBackup s q xs) (lowPort s j) w=withBackup s (Function.update q j w) xs := by
  funext i; refine Fin.addCases (m:=55) (n:=s+2)
    (motive:=fun i => Function.update (withBackup s q xs) (lowPort s j) w i=withBackup s (Function.update q j w) xs i) (fun k => ?_) (fun k => ?_) i
  · simp [withBackup,Function.update_apply,lowPort,Fin.castAdd_inj]
  · simp [withBackup,Function.update_of_ne (off s j k).symm]

def boot (s : ℕ) : BorderedBitIO.Code s :=
  (ArithmeticCalls.copyAt (backup s) (lowPort s 18) (lowPort s 0)).seq
    ((BitWordBridge.encode (lowPort s 18) (lowPort s 0)).seq (BitWordBridge.mark (lowPort s 45)))

theorem boot_exec (s : ℕ) : Executes (boot s) (fun z => initialStacks s (raw z))
    (fun z => withBackup s (frame (seed z 0)) (raw z)) := by
  apply of_bound (bnd_add (bnd_mul (const_bnd 13) raw_bnd) (const_bnd 15))
  intro z r
  let xs := raw z
  let empty := fun _ : Fin 55 => ([] : List Bool)
  let S := withBackup s empty xs
  let a := lowPort s 18
  let b := lowPort s 0
  let c := lowPort s 45
  have ne : a≠b := twoLow s _ _ (by decide)
  have ac : a≠c := twoLow s _ _ (by decide)
  have far (j : Fin 55) : lowPort s j≠backup s := off s j 0
  have low (k : Fin 55) : S (lowPort s k)=[] := by simp [S,withBackup,lowPort,empty]
  have high : S (backup s)=xs := by simp [S,backup,withBackup]
  have eq := ArithmeticCalls.copyAt_eval (backup s) a b (⟨r,S⟩ : StructuredProgram.State 8 _)
    (far _).symm (far _).symm ne.symm (low 18) (low 0)
  let r₁ := readRegs r 0 1 none
  let s₁ := Function.update S a xs
  change Eval _ (7*(S (backup s)).length+5) ⟨r,S⟩ ⟨r₁,Function.update S a (S (backup s))⟩ at eq
  rw [high] at eq
  have at_a : s₁ a=xs := Function.update_self ..
  have at_b : s₁ b=[] := by rw [show s₁=Function.update S a xs from rfl,Function.update_of_ne ne.symm]; exact low 0
  obtain ⟨r₂,e₂⟩ := BitWordBridge.encode_eval a b ne r₁ s₁ at_b
  rw [at_a] at e₂
  let s₂ := Function.update s₁ a (word xs).bits
  have e₃ := BitWordBridge.mark_eval c r₂ s₂
  have at_c : s₂ c=[] := by simp only [s₂,s₁,Function.update_of_ne ac.symm]; exact low 45
  rw [at_c] at e₃
  have final : Function.update s₂ c [true]=withBackup s (frame (seed z 0)) xs := by
    rw [seed_stacks]; dsimp only [s₂,s₁,S,a,c]
    rw [Function.update_idem,update_low,update_low]
  rw [final] at e₃
  rw [at_start] 
  exact ⟨_,_,by dsimp only [xs]; omega,.seq eq (.seq e₂ e₃)⟩

private theorem emb {s : ℕ} (xs : List Bool) (r q : Regs) (a b : St 55) :
    embedState id (Fin.castAdd (s+2)) ⟨r,withBackup s a xs⟩ ⟨q,b⟩ =
      ⟨q,withBackup s b xs⟩ := by
  apply embedState_eq_of_ports id (Fin.castAdd (s+2)) _ _ _ Function.injective_id (Fin.castAdd_injective ..)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i; simp [withBackup]
  · intro j
    refine Fin.addCases (m:=55) (n:=s+2) (motive:=fun j => (¬ ∃ i : Fin 55, i.castAdd (s+2)=j) →
      withBackup s b xs j=withBackup s a xs j) (fun i hi => (hi ⟨i,rfl⟩).elim) (fun i _ => ?_) j
    simp [withBackup]

theorem full : BorderedBitIO.InputPreparation := by
  obtain ⟨q,H⟩ := prepare seed_width
  let P := compiled q (0:Fin 55) 0
  refine ⟨0,fun s _ => ?_⟩
  let call : BorderedBitIO.Code s := .call (ProgramLinking.liftProgram P id (Fin.castAdd (s+2)))
  have hcall : Executes call (fun z => withBackup s (frame (seed z 0)) (raw z))
      (fun z => withBackup s (BorderedBitIO.staged z.m (BorderedBitIO.columns z.a z.B)) (raw z)) := by
    obtain ⟨k,hk⟩ := H
    apply of_bound (bnd_add (bnd_pow base_bnd k) (const_bnd 1))
    intro z r
    obtain ⟨t,rf,ht,e⟩ := hk z r
    have h := eval_call_lifted P id (Fin.castAdd (s+2)) ⟨r,withBackup s (frame (seed z 0)) (raw z)⟩
      Function.injective_id (Fin.castAdd_injective ..)
      (a:=⟨r,frame (seed z 0)⟩) (b:=⟨rf,frame (ready z 0)⟩) (compiled_halt_trace e 0 0)
    rw [emb,emb,final_stacks] at h
    exact ⟨_,rf,Nat.add_le_add_right ht 1,h⟩
  obtain ⟨k,hk⟩ := compose (boot_exec s) hcall
  refine ⟨(boot s).seq call,k,?_⟩
  intro n m x a B c hv
  exact hk ⟨m,n,x,a,B,c,hv⟩ (fun _ => false)

end DetDLP.BinaryPreparation
end

open DetDLP

theorem solution : BorderedBitIO.InputPreparation := by
  exact BinaryPreparation.full
