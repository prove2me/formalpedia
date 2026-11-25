-- Prove2me | solution 1 for DetDLP.packed_hermite_normal_form_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T14:02:21.550516+00:00
-- url     : https://prove2.me/submissions/b10bae70-67aa-4457-a630-1efc98f71f2d

import Definitions.Def_DetDLP_BorderedHermite
import Definitions.Def_OAIQ081S067

set_option autoImplicit false
open OAI.Algorithms.SubexponentialSAT



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

namespace DetDLP.BitEuclidLoop
open OAI.Algorithms.SubexponentialSAT
theorem nat_bits (n : ℕ) : BinaryArithmetic.toNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih =>
    rw [Nat.bits_append_bit _ _ h,BinaryArithmetic.toNat_cons,ih]
    cases b <;> simp [Nat.bit] <;> omega

end DetDLP.BitEuclidLoop


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

end DetDLP.BorderedHermite


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

end DetDLP.UnsignedHermitePivot


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

private theorem row_eq {m : ℕ} [NeZero m] (hm : 2 ≤ m) (p t : ℕ) (hp : 0 < p)
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


namespace DetDLP.HermiteNormalMachine
open BorderedHermite PackedColumnWords HermiteWordPass HermiteStageMachine HermiteRowTrace
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls
open BitArithmeticUnit BitRegisterBank BitRegisterCode

def body : Code 47 := HermiteStageMachine.command.seq (peek (44:Fin 47))
def command : Code 47 := (peek (44:Fin 47)).seq (.while 1 body)
def program := compiled command (port (43:Fin 47)) (port (42:Fin 47))

def state {n} (m : ℕ) (cs : Array (Column n)) (k : ℕ) :=
  let s := runRows (m:ℤ) cs k
  initial m ((m+1)^n) ((m+1)^k) (matrixWord m s.1) (matrixWord m s.2)

theorem guard {m n : ℕ} (hm : 2 ≤ m) (cs : Array (Column n)) (k : ℕ) :
    (state m cs k (44:Fin 47) ≠ 0) ↔ k<n := by
  change ((m+1)^n/((m+1)*(m+1)^k) ≠ 0) ↔ _
  rw [← pow_succ']
  have hb : 1 < m+1 := by omega
  have hpos : 0 < (m+1)^(k+1) := pow_pos (Nat.succ_pos _) _
  rw [← Nat.pos_iff_ne_zero,Nat.div_pos_iff,and_iff_right hpos,Nat.pow_le_pow_iff_right hb]
  omega

theorem while_eval {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (cs : Array (Column n)) (k d : ℕ)
    (hk : k+d=n) (H : invariant m cs.size k (runRows (m:ℤ) cs k)) (r : Regs)
    (hg : r 1=decide (state m cs k 44 ≠ 0)) :
    ∃ t rf,t ≤ d*(rowCost m n cs.size+2)+1 ∧
      Eval (.while 1 body) t ⟨r,frame (state m cs k)⟩ ⟨rf,frame (state m cs n)⟩ := by
  induction d generalizing k r with
  | zero =>
    have e : k=n := by omega
    subst k
    have hh : r 1=false := by simpa [guard hm] using hg
    exact ⟨1,r,by simp,.while_false hh⟩
  | succ d ih =>
    have hkn : k<n := by omega
    let j : Fin n := ⟨k,hkn⟩
    have eq : runRows (m:ℤ) cs (k+1)=pivotStage (m:ℤ) j (runRows (m:ℤ) cs k) := by simp [runRows,hkn,j]
    obtain ⟨H',t,rt,ht,et⟩ := row_eval hm j _ H r
    rw [← eq] at H' et
    obtain ⟨rq,eq',hq⟩ := peek_eval (44:Fin 47) (state m cs (k+1)) rt
    obtain ⟨u,rf,hu,eu⟩ := ih (k+1) (by omega) H' rq hq
    have hh : r 1=true := by rw [hg]; exact decide_eq_true ((guard hm cs k).mpr hkn)
    refine ⟨(t+1)+u+1,rf,?_,.while_true hh (.seq et eq') eu⟩
    rw [Nat.succ_mul]; omega

theorem normal_eval {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (cs : Array (Column n)) (r : Regs) :
    ∃ t rf,t ≤ n*(rowCost m n cs.size+2)+2 ∧
      Eval command t ⟨r,frame (state m cs 0)⟩ ⟨rf,frame (state m cs n)⟩ := by
  have M : 0 < (m:ℤ) := by exact_mod_cast (by omega : 0 < m)
  have H : invariant m cs.size 0 (runRows (m:ℤ) cs 0) := by
    refine ⟨rfl,by simp [runRows],by simp [runRows],?_⟩
    intro v hv
    obtain ⟨c,_,rfl⟩ := Array.mem_map.mp hv
    have B (i : Fin n) : 0 ≤ (c.map (·%(m:ℤ))).get i ∧ (c.map (·%(m:ℤ))).get i < (m:ℤ) := by
      change 0 ≤ (c.map (·%(m:ℤ)))[i.val] ∧ (c.map (·%(m:ℤ)))[i.val] < (m:ℤ)
      simp only [Vector.getElem_map]; exact ⟨Int.emod_nonneg _ M.ne',Int.emod_lt_of_pos _ M⟩
    exact ⟨fun i => ⟨(B i).1,(B i).2.le⟩,fun _ h => (Nat.not_lt_zero _ h).elim,fun i _ => (B i).2⟩
  obtain ⟨rq,eq,hq⟩ := peek_eval (44:Fin 47) (state m cs 0) r
  obtain ⟨t,rf,ht,et⟩ := while_eval hm cs 0 n (by omega) H rq hq
  exact ⟨1+t,rf,by omega,.seq eq et⟩

theorem normal_trace {m n : ℕ} [NeZero m] (hm : 2 ≤ m) (cs : Array (Column n)) (r : Regs) :
    ∃ t rf,t ≤ n*(rowCost m n cs.size+2)+3 ∧
      Trace program t ⟨some program.entry,r,frame (state m cs 0)⟩
        ⟨none,rf,frame (state m cs n)⟩ ∧
      frame (state m cs n) (port (42:Fin 47))=(matrixWord m (normalForm (m:ℤ) cs)).bits := by
  obtain ⟨k,rf,hk,he⟩ := normal_eval hm cs r
  exact ⟨k+1,rf,by omega,compiled_halt_trace he _ _,by rw [frame,store_port]; rfl⟩

end DetDLP.HermiteNormalMachine


namespace DetDLP.HermiteNormalBound
open HermiteRowTrace HermiteWordPass
open OAI.Algorithms.SubexponentialSAT

def factor := 4*BitPackedPivot.overhead+BitFixedColumn.overhead+BitMatrixPass.passOverhead+HermiteStageMachine.overhead+10

theorem work (m n c : ℕ) :
    let A := n+c+bitLen m+4
    n*(rowCost m n c+2)+3 ≤ factor*16*A^9 := by
  intro A
  let b := m+1
  let e := (n+2)*(n+c+3)
  let N := ceiling m n c
  have ub : b.size ≤ bitLen m+2 := by
    apply Nat.size_le.mpr
    have h := Nat.le_pow_clog (by decide : 1<2) m
    change m+1 < 2^(Nat.clog 2 m+2)
    have pos : 0 < 2^(Nat.clog 2 m) := pow_pos (by decide) _
    rw [pow_add]; norm_num; omega
  have hn : n ≤ A := by dsimp [A]; omega
  have hc : n+c ≤ A := by dsimp [A]; omega
  have hpun : bitLen m+n+3 ≤ A := by dsimp [A]; omega
  have hfun : n+3 ≤ A := by dsimp [A]; omega
  have hb : b.size ≤ A := by dsimp [A]; omega
  have he : e ≤ A^2 := by dsimp only [e]; rw [pow_two]; exact Nat.mul_le_mul (by dsimp [A]; omega) (by dsimp [A]; omega)
  have ne : N ≤ 2^(e*b.size) := by
    change b^e ≤ 2^(e*b.size)
    rw [Nat.mul_comm e b.size,pow_mul 2 b.size e]; exact Nat.pow_le_pow_left (Nat.lt_size_self b).le _
  have hn2 := Nat.size_le_size (Nat.mul_le_mul_left 2 ne)
  rw [← pow_succ',Nat.size_pow] at hn2
  have hsN := Nat.size_le_size (show N ≤ 2*N by omega)
  have h3 : e*b.size ≤ A^3 := by rw [pow_succ]; exact Nat.mul_le_mul he hb
  have hA : 4 ≤ A := by dsimp [A]; omega
  have H (t : ℕ) (ht : 0 < t) : A ≤ A^t := Nat.le_self_pow ht.ne' A
  have hSq : ((2*N).size+2)^2 ≤ 4*A^6 := by
    have hbase : (2*N).size+2 ≤ 2*A^3 := by have := H 3 (by decide); omega
    calc _ ≤ (2*A^3)^2 := Nat.pow_le_pow_left hbase _
         _ = _ := by ring
  have hS : (N.size+2)^2 ≤ 4*A^6 := (Nat.pow_le_pow_left (Nat.add_le_add_right hsN 2) _).trans hSq
  have h1 : 1 ≤ A^6 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ A^7 := Nat.one_le_pow _ _ (by omega)
  have h3' : 1 ≤ A^8 := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ A^9 := Nat.one_le_pow _ _ (by omega)
  have h67 : A^6 ≤ A^7 := Nat.pow_le_pow_right (by omega) (by decide)
  have h78 : A^7 ≤ A^8 := Nat.pow_le_pow_right (by omega) (by decide)
  let P := 4*BitPackedPivot.overhead
  let F := BitFixedColumn.overhead
  let M := BitMatrixPass.passOverhead
  let R := HermiteStageMachine.overhead
  have p : pivotBudget m n N ≤ 4*P*A^7+1 := by
    unfold pivotBudget; apply Nat.add_le_add_right
    calc _ ≤ (P*A)*(4*A^6) := Nat.mul_le_mul (Nat.mul_le_mul_left P hpun) hSq
         _ = _ := by ring
  have f : fixedBudget n N ≤ 4*F*A^7+1 := by
    unfold fixedBudget; apply Nat.add_le_add_right
    calc _ ≤ (F*A)*(4*A^6) := Nat.mul_le_mul (Nat.mul_le_mul_left F hfun) hSq
         _ = _ := by ring
  have row : rowCost m n c ≤ 4*(P+F+M+R+2)*A^8 := by
    have hrow : pivotBudget m n N+fixedBudget n N+M*(N.size+2)^2 ≤ 4*(P+F+M+1)*A^7 := by
      nlinarith only [p,f,Nat.mul_le_mul_left M hS,Nat.mul_le_mul_left M h67,h2]
    change (n+c)*_ + R*_ ≤ _
    have hrow' := Nat.mul_le_mul hc hrow
    nlinarith only [hrow',Nat.mul_le_mul_left R hS,Nat.mul_le_mul_left R (h67.trans h78),h3']
  have hh := Nat.mul_le_mul hn (Nat.add_le_add_right row 2)
  change _ ≤ (P+F+M+R+10)*16*A^9
  nlinarith only [hh,H 9 (by decide),h4]

theorem polynomial : ∃ k : ℕ,∀ m n c, n*(rowCost m n c+2)+3 ≤ (n+c+bitLen m+4)^k := by
  refine ⟨(factor*16).size+9,?_⟩
  intro m n c
  let A := n+c+bitLen m+4
  have C : factor*16 ≤ A^(factor*16).size :=
    (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_left (by dsimp [A]; omega) _)
  exact (work m n c).trans (by rw [pow_add]; exact Nat.mul_le_mul_right _ C)

end DetDLP.HermiteNormalBound

open DetDLP

theorem solution :
    ∃ (l k : ℕ) (P : BitProgram.Program 8 55 l),
      ∀ (m n : ℕ) [NeZero m], 2 ≤ m →
      ∀ (cols : Array (BorderedHermite.Column n)) (r : Fin 8 → Bool),
        let b := m+1
        let D := b^n
        let serialize (a : Array (BorderedHermite.Column n)) :=
          Nat.ofDigits D ((a.toList.map fun v => Nat.ofDigits b
            (List.ofFn fun i => (v.get i).toNat))++[1])
        let reduced := cols.map (fun c => c.map (·%(m:ℤ)))
        let ports : Fin 9 → ℕ := ![m,b,D,1,1,serialize reduced,D/b,1,0]
        let start : Fin 55 → List Bool := fun i => Fin.addCases (m:=46) (n:=9)
          (fun _ => []) (fun j => (ports j).bits) i
        ∃ (t : ℕ) (f : BitProgram.Cfg 8 55 l),
          BitProgram.Trace P t ⟨some P.entry,r,start⟩ f ∧ f.pc=none ∧
          f.stacks P.outputStack=(serialize (BorderedHermite.normalForm (m:ℤ) cols)).bits ∧
          t ≤ (n+cols.size+bitLen m+4)^k := by
  obtain ⟨k,hk⟩ := HermiteNormalBound.polynomial
  refine ⟨_,k,HermiteNormalMachine.program,?_⟩
  intro m n inst hm cs r b D serialize reduced ports start
  obtain ⟨t,rf,ht,tr,out⟩ := HermiteNormalMachine.normal_trace hm cs r
  have init : BitRegisterCode.frame (HermiteNormalMachine.state m cs 0)=start := by
    funext i
    have e : D/(b*1)=D/b := by simp
    fin_cases i <;> first | rfl | exact congrArg Nat.bits e
  rw [init] at tr
  exact ⟨t,_,tr,rfl,out,ht.trans (hk m n cs.size)⟩
