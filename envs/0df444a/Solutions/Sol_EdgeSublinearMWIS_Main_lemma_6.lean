-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.lemma_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T22:41:06.326201+00:00
-- url     : https://prove2.me/submissions/0990f944-a5fe-4b55-9db0-d17883693495
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Nat.Bits
import Mathlib.Tactic
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_OAIThreeMachineSched02
import Theorems.Thm_EdgeSublinearMWIS_Main_realizer_native_program
import Definitions.Def_EdgeSublinearMWIS_Main_Graphs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Theorems.Thm_EdgeSublinearMWIS_Main_lemma_11
import Theorems.Thm_EdgeSublinearMWIS_Main_lemma_8
import Definitions.Def_EdgeSublinearMWIS_Main_WeightedReduction
import Theorems.Thm_TreewidthApprox_Partition_comp_subset_part
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.Convex.Jensen
import Definitions.Def_EdgeSublinearMWIS_Main_Relaxation
import Definitions.Def_EdgeSublinearMWIS_Main_WeightedExecution
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.List.Sublists
import Definitions.Def_EdgeSublinearMWIS_Main_RoundOrCut
import Mathlib
import Theorems.Thm_EdgeSublinearMWIS_Main_polynomial_context_program
import Definitions.Def_EdgeSublinearMWIS_Main_AlgorithmContracts

-- Solutions.RawBinary
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def value : List Bool → ℕ
   | [] => 0
   | b::L => b.toNat+2*value L
 def increment : List Bool → List Bool
   | [] => [true]
   | false::L => true::L
   | true::L => false::increment L

 theorem increment_value (L : List Bool) : value (increment L)=value L+1 := by
  induction L with
  | nil => rfl
  | cons b L ih => cases b <;> simp [increment,value,ih] <;> omega

 theorem increment_length (L : List Bool) : (increment L).length≤ L.length+1 := by
  induction L with
  | nil => simp [increment]
  | cons b L ih => cases b <;> simp [increment] <;> omega

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryAdder
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open RawStack
abbrev State := List Bool × (List Bool × (Bool × List Bool))
 def step (s : State) : State :=
   let a := s.1.headD false
   let b := s.2.1.headD false
   let c := s.2.2.1
   (s.1.tail,(s.2.1.tail,((a && b)||(a && c)||(b && c),(xor (xor a b) c)::s.2.2.2)))
 def word (A B : List Bool) : List Bool :=
   ((step^[A.length+B.length+1]) (A,(B,(false,[])))).2.2.2.reverse

 theorem value_head_tail (A : List Bool) : value A=(A.headD false).toNat+2*value A.tail := by
   cases A <;> rfl

 theorem value_append (A B : List Bool) : value (A++B)=value A+2^A.length*value B := by
   induction A with
   | nil => simp [value]
   | cons a A ih => simp [value,ih,pow_succ]; ring

 theorem full_adder (a b c : Bool) :
    (xor (xor a b) c).toNat+2*((a && b)||(a && c)||(b && c)).toNat=a.toNat+b.toNat+c.toNat := by
   cases a <;> cases b <;> cases c <;> decide

 theorem step_value (s : State) :
    value (step s).2.2.2.reverse+2^(step s).2.2.2.length*(value (step s).1+value (step s).2.1+(step s).2.2.1.toNat)=
      value s.2.2.2.reverse+2^s.2.2.2.length*(value s.1+value s.2.1+s.2.2.1.toNat) := by
   rcases s with ⟨A,B,c,R⟩
   have ha := value_head_tail A
   have hb := value_head_tail B
   have hf := full_adder (A.headD false) (B.headD false) c
   simp only [step,List.reverse_cons,value_append,List.length_reverse,List.length_cons,pow_succ,value,List.length_nil,Nat.mul_zero,Nat.add_zero]
   rw [ha,hb]
   have hfm := congrArg (fun z : ℕ => 2^R.length*z) hf
   nlinarith only [hfm]

 theorem iter_value (s : State) (t : ℕ) :
    value ((step^[t]) s).2.2.2.reverse+2^((step^[t]) s).2.2.2.length*(value ((step^[t]) s).1+value ((step^[t]) s).2.1+((step^[t]) s).2.2.1.toNat)=
      value s.2.2.2.reverse+2^s.2.2.2.length*(value s.1+value s.2.1+s.2.2.1.toNat) := by
   induction t with
   | zero => rfl
   | succ t ih => rw [Function.iterate_succ_apply']; exact (step_value ((step^[t]) s)).trans ih

 theorem iter_lists (s : State) (t : ℕ) :
    ((step^[t]) s).1=s.1.drop t ∧ ((step^[t]) s).2.1=s.2.1.drop t ∧
      ((step^[t]) s).2.2.2.length=s.2.2.2.length+t := by
   induction t with
   | zero => simp
   | succ t ih =>
     rw [Function.iterate_succ_apply']
     simp only [step,ih.1,ih.2.1,ih.2.2,List.length_cons]
     constructor
     · exact List.tail_drop
     · constructor
       · exact List.tail_drop
       · omega

 theorem word_value (A B : List Bool) : value (word A B)=value A+value B := by
   let t := A.length+B.length
   let s : State := (A,(B,(false,[])))
   have hlist := iter_lists s t
   have hA : ((step^[t]) s).1=[] := by rw [hlist.1]; exact List.drop_eq_nil_of_le (by dsimp [s,t]; omega)
   have hB : ((step^[t]) s).2.1=[] := by rw [hlist.2.1]; exact List.drop_eq_nil_of_le (by dsimp [s,t]; omega)
   have hzero : ((step^[t+1]) s).1=[] ∧ ((step^[t+1]) s).2.1=[] ∧ ((step^[t+1]) s).2.2.1=false := by
     rw [Function.iterate_succ_apply']
     simp [step,hA,hB]
   have hi := iter_value s (t+1)
   rw [hzero.1,hzero.2.1,hzero.2.2] at hi
   simpa only [word,s,t,value,List.reverse_nil,Bool.toNat_false,Nat.add_zero,Nat.mul_zero,List.length_nil,pow_zero,Nat.one_mul,Nat.zero_add] using hi

 theorem word_length (A B : List Bool) : (word A B).length=A.length+B.length+1 := by
   have hh := (iter_lists (A,(B,(false,[]))) (A.length+B.length+1)).2.2
   simpa only [word,List.length_reverse,List.length_nil,Nat.zero_add] using hh

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.BinaryTrim
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def trim : List Bool → List Bool
   | [] => []
   | b::L => let T := trim L
             if T=[] then if b then [true] else [] else b::T

 theorem trim_value (L : List Bool) : value (trim L)=value L := by
   induction L with
   | nil => rfl
   | cons b L ih =>
     by_cases hT : trim L=[]
     · have hv : value L=0 := by rw [← ih,hT]; rfl
       cases b <;> simp [trim,hT,value,hv]
     · simp only [trim,hT,if_false,value,ih]

 theorem trim_length (L : List Bool) : (trim L).length≤ L.length := by
   induction L with
   | nil => simp [trim]
   | cons b L ih =>
     by_cases hT : trim L=[]
     · cases b <;> simp [trim,hT]
     · simp [trim,hT]; omega

 theorem value_lt (L : List Bool) : value L<2^L.length := by
   induction L with
   | nil => simp [value]
   | cons b L ih => cases b <;> simp [value,pow_succ] <;> omega

 theorem trim_lower (L : List Bool) (hL : trim L≠[]) : 2^((trim L).length-1)≤ value (trim L) := by
   induction L with
   | nil => exact False.elim (hL rfl)
   | cons b L ih =>
     by_cases hT : trim L=[]
     · cases b <;> simp_all [trim,value]
     · have hh := ih hT
       have hlen : 0<(trim L).length := by
         cases he : trim L with
         | nil => exact False.elim (hT he)
         | cons a T => simp
       have hp : 2^((trim L).length)=2*2^((trim L).length-1) := by
         rw [← Nat.pow_succ']
         congr 1
         omega
       simp only [trim,hT,if_false,List.length_cons,Nat.add_sub_cancel,value]
       rw [hp]
       omega

 theorem trim_length_of_lt (L : List Bool) (B : ℕ) (hB : value L<2^B) : (trim L).length≤ B := by
   by_cases hL : trim L=[]
   · simp [hL]
   · have hp := trim_lower L hL
     rw [trim_value] at hp
     have hh : (trim L).length-1< B := by
       by_contra hn
       have hpow := Nat.pow_le_pow_right (by omega : 1≤2) (by omega : B≤(trim L).length-1)
       omega
     omega

 def trimStep (x : Bool×List Bool) : List Bool :=
   if x.2=[] then if x.1 then [true] else [] else x.1::x.2

 theorem trim_fold (L : List Bool) : L.reverse.foldl (fun T b => trimStep (b,T)) []=trim L := by
   induction L with
   | nil => rfl
   | cons b L ih =>
     rw [List.reverse_cons,List.foldl_append]
     change trimStep (b,L.reverse.foldl (fun T b => trimStep (b,T)) [])=trim (b::L)
     rw [ih]
     rfl

 theorem trim_idem (L : List Bool) : trim (trim L)=trim L := by
   induction L with
   | nil => rfl
   | cons b L ih =>
     by_cases hT : trim L=[]
     · cases b <;> simp [trim,hT]
     · simp only [trim,hT,if_false,ih]


end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinarySubtract
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinarySubtract
open RawStack
abbrev State := BinaryAdder.State
 def step (s : State) : State :=
   let a := s.1.headD false
   let b := s.2.1.headD false
   let c := s.2.2.1
   (s.1.tail,(s.2.1.tail,((!a && (b || c)) || (b && c),(xor (xor a b) c)::s.2.2.2)))
 def raw (A B : List Bool) : Bool×List Bool :=
   let s := (step^[A.length+B.length+1]) (A,(B,(false,[])))
   (s.2.2.1,s.2.2.2.reverse)
 def difference (A B : List Bool) : List Bool := if (raw A B).1 then [] else trim (raw A B).2
 def less (A B : List Bool) : Bool := (raw A B).1

 theorem bit_balance (a b c : Bool) :
     a.toNat+2*((!a && (b || c)) || (b && c)).toNat=b.toNat+c.toNat+(xor (xor a b) c).toNat := by
   cases a <;> cases b <;> cases c <;> decide

 def potential (s : State) : ℤ :=
   (value s.2.2.2.reverse:ℤ)+(2:ℤ)^s.2.2.2.length*((value s.1:ℤ)-(value s.2.1:ℤ)-s.2.2.1.toNat)

 theorem step_potential (s : State) : potential (step s)=potential s := by
   rcases s with ⟨A,B,c,R⟩
   have ha := BinaryAdder.value_head_tail A
   have hb := BinaryAdder.value_head_tail B
   have hf := bit_balance (A.headD false) (B.headD false) c
   have haZ : (value A:ℤ)=(A.headD false).toNat+2*(value A.tail:ℤ) := by exact_mod_cast ha
   have hbZ : (value B:ℤ)=(B.headD false).toNat+2*(value B.tail:ℤ) := by exact_mod_cast hb
   have hfZ : ((A.headD false).toNat:ℤ)+2*((!A.headD false && (B.headD false || c)) || (B.headD false && c)).toNat=
       (B.headD false).toNat+c.toNat+(xor (xor (A.headD false) (B.headD false)) c).toNat := by exact_mod_cast hf
   simp only [potential,step,List.reverse_cons,BinaryAdder.value_append,List.length_reverse,List.length_cons,pow_succ,value,Nat.mul_zero,Nat.add_zero]
   push_cast
   rw [haZ,hbZ]
   have hh := congrArg (fun z : ℤ => (2:ℤ)^R.length*z) hfZ
   nlinarith only [hh]

 theorem iter_potential (s : State) (t : ℕ) : potential (step^[t] s)=potential s := by
   induction t with
   | zero => rfl
   | succ t ih => rw [Function.iterate_succ_apply']; exact (step_potential _).trans ih

 theorem iter_lists (s : State) (t : ℕ) :
     (step^[t] s).1=s.1.drop t ∧ (step^[t] s).2.1=s.2.1.drop t ∧
       (step^[t] s).2.2.2.length=s.2.2.2.length+t := by
   induction t with
   | zero => simp
   | succ t ih =>
     rw [Function.iterate_succ_apply']
     simp only [step,ih.1,ih.2.1,ih.2.2,List.length_cons]
     exact ⟨List.tail_drop,List.tail_drop,by omega⟩

 theorem raw_balance (A B : List Bool) : value A+2^(A.length+B.length+1)*(raw A B).1.toNat=value B+value (raw A B).2 := by
   let n := A.length+B.length+1
   let s : State := (A,(B,(false,[])))
   let t := step^[n] s
   have hh := iter_potential s n
   have hl := iter_lists s n
   have hA : t.1=[] := by rw [hl.1]; exact List.drop_eq_nil_of_le (by dsimp [n,s]; omega)
   have hB : t.2.1=[] := by rw [hl.2.1]; exact List.drop_eq_nil_of_le (by dsimp [n,s]; omega)
   have hlen : t.2.2.2.length=n := by simpa only [s,List.length_nil,Nat.zero_add] using hl.2.2
   change potential t=potential s at hh
   dsimp only [potential] at hh
   rw [hA,hB,hlen] at hh
   dsimp only [s] at hh
   simp only [value,List.reverse_nil,List.length_nil,pow_zero,Bool.toNat_false,Int.ofNat_zero,zero_sub,mul_one] at hh
   have heq : (value A:ℤ)+(2:ℤ)^n*(t.2.2.1.toNat:ℤ)=(value B:ℤ)+(value t.2.2.2.reverse:ℤ) := by linarith only [hh]
   exact_mod_cast heq

 theorem raw_length (A B : List Bool) : (raw A B).2.length=A.length+B.length+1 := by
   have hh := (iter_lists (A,(B,(false,[]))) (A.length+B.length+1)).2.2
   simpa only [raw,List.length_reverse,List.length_nil,Nat.zero_add] using hh

 theorem less_iff (A B : List Bool) : less A B=true ↔ value A< value B := by
   have hb := raw_balance A B
   have hl := value_lt (raw A B).2
   rw [raw_length] at hl
   unfold less
   cases h : (raw A B).1 <;> simp only [h,Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,Nat.mul_one,Nat.add_zero] at hb ⊢ <;> simp only [Bool.false_eq_true,false_iff,true_iff] <;> omega

 theorem difference_value (A B : List Bool) : value (difference A B)=value A-value B := by
   unfold difference
   by_cases h : (raw A B).1=true
   · rw [if_pos h]
     have hh := (less_iff A B).mp h
     simp [value,Nat.sub_eq_zero_of_le hh.le]
   · have hb := raw_balance A B
     have hf : (raw A B).1=false := Bool.eq_false_iff.mpr h
     rw [hf,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at hb
     rw [if_neg h,trim_value]
     omega

 theorem difference_canonical (A B : List Bool) : trim (difference A B)=difference A B := by
   unfold difference
   split_ifs
   · rfl
   · exact trim_idem _

 theorem difference_length (A B : List Bool) : (difference A B).length≤ A.length := by
   rw [← difference_canonical A B]
   apply trim_length_of_lt
   rw [difference_value]
   exact (Nat.sub_le _ _).trans_lt (value_lt A)

end EdgeSublinearMWIS.Main.BinarySubtract
end

-- Solutions.BinaryMultiply
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def multiplyStep (x : Bool×(List Bool×List Bool)) : List Bool×List Bool :=
   (false::x.2.1,if x.1 then trim (BinaryAdder.word x.2.2 x.2.1) else x.2.2)
 def multiply (A B : List Bool) : List Bool :=
   trim (B.foldl (fun s b => multiplyStep (b,s)) (A,[])).2

 theorem multiply_fold_value (A B S : List Bool) :
     value (B.foldl (fun s b => multiplyStep (b,s)) (A,S)).2=value S+value A*value B := by
   induction B generalizing A S with
   | nil => simp [value]
   | cons b B ih =>
     rw [List.foldl_cons]
     change value (B.foldl _ (false::A,if b then trim (BinaryAdder.word S A) else S)).2=_
     rw [ih]
     cases b <;> simp only [Bool.false_eq_true,if_false,if_true,trim_value,BinaryAdder.word_value,value,Bool.toNat_false,Bool.toNat_true] <;> ring

 theorem multiply_value (A B : List Bool) : value (multiply A B)=value A*value B := by
   rw [multiply,trim_value,multiply_fold_value]
   simp [value]

 theorem product_lt (A B : List Bool) : value A*value B<2^(A.length+B.length) := by
   calc
     _ ≤ value A*2^B.length := Nat.mul_le_mul_left _ (value_lt B).le
     _ < 2^A.length*2^B.length := Nat.mul_lt_mul_of_pos_right (value_lt A) (by positivity)
     _ = _ := (pow_add _ _ _).symm

 theorem multiply_length (A B : List Bool) : (multiply A B).length≤ A.length+B.length := by
   apply trim_length_of_lt
   rw [multiply_fold_value]
   simpa only [value,Nat.zero_add] using product_lt A B

 theorem multiply_first_length (A B S : List Bool) :
     (B.foldl (fun s b => multiplyStep (b,s)) (A,S)).1.length=A.length+B.length := by
   induction B generalizing A S with
   | nil => simp
   | cons b B ih =>
     rw [List.foldl_cons]
     change (B.foldl _ (false::A,if b then trim (BinaryAdder.word S A) else S)).1.length=_
     rw [ih]
     simp [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

 theorem multiply_canonical (A B S : List Bool) (hS : trim S=S) :
     trim (B.foldl (fun s b => multiplyStep (b,s)) (A,S)).2=(B.foldl (fun s b => multiplyStep (b,s)) (A,S)).2 := by
   induction B generalizing A S with
   | nil => exact hS
   | cons b B ih =>
     rw [List.foldl_cons]
     apply ih
     cases b
     · exact hS
     · exact trim_idem _

 theorem multiply_prefix_length (A B : List Bool) (j : ℕ) :
     ((B.take j).foldl (fun s b => multiplyStep (b,s)) (A,[])).2.length≤ A.length+B.length := by
   let P := (B.take j).foldl (fun s b => multiplyStep (b,s)) (A,[])
   have hc : trim P.2=P.2 := multiply_canonical A (B.take j) [] rfl
   rw [← hc]
   apply trim_length_of_lt
   have hfull := multiply_fold_value A B []
   rw [← List.take_append_drop j B,List.foldl_append] at hfull
   have hpartial := multiply_fold_value P.1 (B.drop j) P.2
   change value ((B.drop j).foldl _ P).2=_ at hfull
   rw [hpartial,List.take_append_drop] at hfull
   have hle : value P.2≤ value A*value B := by simpa only [value,Nat.zero_add] using (show value P.2≤ value []+value A*value B by omega)
   exact hle.trans_lt (product_lt A B)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryDivision
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def divideStep (x : Bool×(List Bool×(List Bool×List Bool))) : List Bool×(List Bool×List Bool) :=
   let B := x.2.1
   let R := x.1::x.2.2.1
   if BinarySubtract.less R B then (B,(trim R,false::x.2.2.2))
   else (B,(BinarySubtract.difference R B,true::x.2.2.2))
 def divide (A B : List Bool) : List Bool×List Bool :=
   let s := A.reverse.foldl (fun s b => divideStep (b,s)) (B,([],[]))
   (trim s.2.2,trim s.2.1)

 theorem divideStep_base (b : Bool) (B R Q : List Bool) : (divideStep (b,(B,(R,Q)))).1=B := by
   dsimp only [divideStep]
   split_ifs <;> rfl

 theorem divideStep_balance (b : Bool) (B R Q : List Bool) :
     value (divideStep (b,(B,(R,Q)))).2.1+value B*value (divideStep (b,(B,(R,Q)))).2.2=
       b.toNat+2*(value R+value B*value Q) := by
   unfold divideStep
   by_cases h : BinarySubtract.less (b::R) B=true
   · rw [if_pos h]
     rw [trim_value]
     have hb := (BinarySubtract.less_iff _ _).mp h
     simp only [value,Bool.toNat_false]
     ring
   · rw [if_neg h]
     rw [BinarySubtract.difference_value]
     have hb : value B≤ value (b::R) := by
       exact Nat.le_of_not_gt (fun hh => h ((BinarySubtract.less_iff _ _).mpr hh))
     have he := Nat.sub_add_cancel hb
     simp only [value,Bool.toNat_true] at he ⊢
     nlinarith only [he]

 theorem divideStep_remainder (b : Bool) (B R Q : List Bool) (hB : 0< value B) (hR : value R< value B) :
     value (divideStep (b,(B,(R,Q)))).2.1< value B := by
   unfold divideStep
   by_cases h : BinarySubtract.less (b::R) B=true
   · rw [if_pos h]
     rw [trim_value]
     exact (BinarySubtract.less_iff _ _).mp h
   · rw [if_neg h,BinarySubtract.difference_value]
     have hb : value B≤ value (b::R) := Nat.le_of_not_gt (fun hh => h ((BinarySubtract.less_iff _ _).mpr hh))
     have hbit : b.toNat≤1 := by cases b <;> decide
     simp only [value] at hb ⊢
     omega

 theorem divide_fold_base (L B R Q : List Bool) :
     (L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))).1=B := by
   induction L generalizing R Q with
   | nil => rfl
   | cons b L ih =>
     rw [List.foldl_cons]
     have hs := divideStep_base b B R Q
     generalize he : divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hs
     subst B'
     exact ih R' Q'

 theorem divide_fold_balance (L B R Q : List Bool) :
     let s := L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))
     value s.2.1+value B*value s.2.2=value L.reverse+2^L.length*(value R+value B*value Q) := by
   induction L generalizing R Q with
   | nil => simp [value]
   | cons b L ih =>
     dsimp only
     rw [List.foldl_cons]
     have hbase := divideStep_base b B R Q
     have hstep := divideStep_balance b B R Q
     generalize he : divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hbase hstep
     subst B'
     have hh := ih R' Q'
     dsimp only at hh
     rw [hh,List.reverse_cons,BinaryAdder.value_append]
     simp only [value,List.length_reverse,List.length_cons,pow_succ,Nat.mul_zero,Nat.add_zero]
     rw [hstep]
     ring

 theorem divide_fold_remainder (L B R Q : List Bool) (hB : 0< value B) (hR : value R< value B) :
     value (L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))).2.1< value B := by
   induction L generalizing R Q with
   | nil => exact hR
   | cons b L ih =>
     rw [List.foldl_cons]
     have hbase := divideStep_base b B R Q
     have hstep := divideStep_remainder b B R Q hB hR
     generalize he : divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hbase hstep
     subst B'
     exact ih R' Q' hstep

 theorem divide_value (A B : List Bool) (hB : 0< value B) :
     value (divide A B).1=value A/value B ∧ value (divide A B).2=value A%value B := by
   have hb := divide_fold_balance A.reverse B [] []
   have hr := divide_fold_remainder A.reverse B [] [] hB (by simpa only [value] using hB)
   dsimp only at hb
   simp only [List.reverse_reverse,value,Nat.mul_zero,Nat.add_zero] at hb
   have he := (Nat.div_mod_unique hB).mpr ⟨hb,hr⟩
   dsimp only [divide]
   simp only [trim_value]
   exact ⟨he.1.symm,he.2.symm⟩

 theorem divideStep_qlength (b : Bool) (B R Q : List Bool) :
     (divideStep (b,(B,(R,Q)))).2.2.length=Q.length+1 := by
   dsimp only [divideStep]
   split_ifs <;> simp

 theorem divideStep_canonical (b : Bool) (B R Q : List Bool) :
     trim (divideStep (b,(B,(R,Q)))).2.1=(divideStep (b,(B,(R,Q)))).2.1 := by
   dsimp only [divideStep]
   split_ifs
   · exact trim_idem _
   · dsimp only [BinarySubtract.difference]
     split_ifs
     · rfl
     · exact trim_idem _

 theorem divide_fold_qlength (L B R Q : List Bool) :
     (L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))).2.2.length=Q.length+L.length := by
   induction L generalizing R Q with
   | nil => simp
   | cons b L ih =>
     rw [List.foldl_cons]
     have hbase := divideStep_base b B R Q
     have hlen := divideStep_qlength b B R Q
     generalize he : divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hbase hlen
     subst B'
     rw [ih,hlen]
     simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

 theorem divide_fold_canonical (L B R Q : List Bool) (hR : trim R=R) :
     trim (L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))).2.1=(L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))).2.1 := by
   induction L generalizing R Q with
   | nil => exact hR
   | cons b L ih =>
     rw [List.foldl_cons]
     have hbase := divideStep_base b B R Q
     have hcanon := divideStep_canonical b B R Q
     generalize he : divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hbase hcanon
     subst B'
     exact ih R' Q' hcanon

 theorem divide_prefix_lengths (A B : List Bool) (hB : 0< value B) (j : ℕ) (hj : j≤ A.length) :
     let s := (A.reverse.take j).foldl (fun s b => divideStep (b,s)) (B,([],[]))
     s.1=B ∧ s.2.1.length≤ B.length ∧ s.2.2.length≤ A.length := by
   let L := A.reverse.take j
   have hbase := divide_fold_base L B [] []
   have hr := divide_fold_remainder L B [] [] hB (by simpa only [value] using hB)
   have hc := divide_fold_canonical L B [] [] rfl
   have hq := divide_fold_qlength L B [] []
   have hlen : L.length≤ A.length := by dsimp [L]; simp only [List.length_take,List.length_reverse]; omega
   refine ⟨hbase,?_,?_⟩
   · rw [← hc]
     exact trim_length_of_lt _ B.length (hr.trans (value_lt B))
   · simp only [List.length_nil,Nat.zero_add] at hq
     exact hq.le.trans hlen

 theorem divideStep_rlength (b : Bool) (B R Q : List Bool) :
     (divideStep (b,(B,(R,Q)))).2.1.length≤ R.length+1 := by
   dsimp only [divideStep]
   split_ifs
   · exact (trim_length _).trans (by simp)
   · exact (BinarySubtract.difference_length _ _).trans (by simp)

 theorem divide_fold_rlength (L B R Q : List Bool) :
     (L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))).2.1.length≤ R.length+L.length := by
   induction L generalizing R Q with
   | nil => simp
   | cons b L ih =>
     rw [List.foldl_cons]
     have hbase := divideStep_base b B R Q
     have hlen := divideStep_rlength b B R Q
     generalize he : divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hbase hlen
     subst B'
     have hh := ih R' Q'
     simp only [List.length_cons]
     omega

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EuclidBound
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryEuclid

 def step (s : ℕ×ℕ) : ℕ×ℕ := if s.2=0 then s else (s.2,s.1%s.2)

 theorem mod_mod_half (b r : ℕ) (hr : 0< r) (hrb : r< b) : 2*(b%r)< b := by
   by_cases h : 2*r≤ b
   · have hm := Nat.mod_lt b hr
     omega
   · have hb : r≤ b := by omega
     have hsmall : b-r< r := by omega
     have he : b%r=b-r := by rw [Nat.mod_eq_sub_mod hb,Nat.mod_eq_of_lt hsmall]
     rw [he]
     omega

 theorem two_step (a b L : ℕ) (hb : b<2^(L+1)) : (step^[2] (a,b)).2<2^L := by
   by_cases hb0 : b=0
   · simp [step,hb0]
   · have hbpos : 0< b := by omega
     by_cases hr0 : a%b=0
     · simp [Function.iterate_succ_apply,step,hb0,hr0]
     · have hr : 0< a%b := by omega
       have hrb := Nat.mod_lt a hbpos
       have hh := mod_mod_half b (a%b) hr hrb
       simp only [Function.iterate_succ_apply,Function.iterate_zero_apply,step,hb0,if_false,hr0]
       rw [pow_succ] at hb
       omega

 theorem terminates (a b L : ℕ) (hb : b<2^L) : (step^[2*L] (a,b)).2=0 := by
   induction L generalizing a b with
   | zero =>
     simp only [pow_zero] at hb
     have hb0 : b=0 := by omega
     simpa using hb0
   | succ L ih =>
     have hh := two_step a b L hb
     have ht := ih (step^[2] (a,b)).1 (step^[2] (a,b)).2 hh
     rw [Nat.mul_succ,Function.iterate_add_apply]
     exact ht

 theorem gcd_step (s : ℕ×ℕ) : (step s).1.gcd (step s).2=s.1.gcd s.2 := by
   rcases s with ⟨a,b⟩
   by_cases hb : b=0
   · simp [step,hb]
   · simp only [step,hb,if_false]
     rw [Nat.gcd_comm b (a%b),← Nat.gcd_rec b a,Nat.gcd_comm]

 theorem gcd_iter (s : ℕ×ℕ) (t : ℕ) : (step^[t] s).1.gcd (step^[t] s).2=s.1.gcd s.2 := by
   induction t with
   | zero => rfl
   | succ t ih => rw [Function.iterate_succ_apply']; exact (gcd_step _).trans ih

end EdgeSublinearMWIS.Main.BinaryEuclid
end

-- Solutions.BinaryGcd
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
namespace BinaryGcd

 def step (s : List Bool×List Bool) : List Bool×List Bool :=
   if s.2=[] then s else (s.2,(divide s.1 s.2).2)
 def run (A B : List Bool) : List Bool×List Bool := step^[2*B.length] (trim A,trim B)
 def gcd (A B : List Bool) : List Bool := (run A B).1

 theorem divide_lengths (A B : List Bool) :
     (divide A B).1.length≤ A.length ∧ (divide A B).2.length≤ A.length := by
   have hr := divide_fold_rlength A.reverse B [] []
   have hq := divide_fold_qlength A.reverse B [] []
   simp only [List.length_nil,Nat.zero_add,List.length_reverse] at hr hq
   constructor
   · exact (trim_length _).trans hq.le
   · exact (trim_length _).trans hr

 theorem divide_canonical (A B : List Bool) : trim (divide A B).1=(divide A B).1 ∧
     trim (divide A B).2=(divide A B).2 := ⟨trim_idem _,trim_idem _⟩

 theorem canonical_step (s : List Bool×List Bool) (hA : trim s.1=s.1) (hB : trim s.2=s.2) :
     trim (step s).1=(step s).1 ∧ trim (step s).2=(step s).2 := by
   unfold step
   split_ifs
   · exact ⟨hA,hB⟩
   · exact ⟨hB,(divide_canonical _ _).2⟩

 theorem canonical_iter (s : List Bool×List Bool) (hA : trim s.1=s.1) (hB : trim s.2=s.2) (t : ℕ) :
     trim (step^[t] s).1=(step^[t] s).1 ∧ trim (step^[t] s).2=(step^[t] s).2 := by
   induction t with
   | zero => exact ⟨hA,hB⟩
   | succ t ih => rw [Function.iterate_succ_apply']; exact canonical_step _ ih.1 ih.2

 theorem value_positive (A : List Bool) (hA : trim A=A) (hn : A≠[]) : 0< value A := by
   have h := trim_lower A (by simpa only [hA] using hn)
   rw [hA] at h
   exact lt_of_lt_of_le (by positivity : 0<2^(A.length-1)) h

 theorem values_step (s : List Bool×List Bool) (hB : trim s.2=s.2) :
     (value (step s).1,value (step s).2)=BinaryEuclid.step (value s.1,value s.2) := by
   by_cases hb : s.2=[]
   · simp [step,hb,value,BinaryEuclid.step]
   · have hp := value_positive s.2 hB hb
     have he := (divide_value s.1 s.2 hp).2
     simp only [step,hb,if_false,BinaryEuclid.step,ne_of_gt hp,he]

 theorem values_iter (s : List Bool×List Bool) (hA : trim s.1=s.1) (hB : trim s.2=s.2) (t : ℕ) :
     (value (step^[t] s).1,value (step^[t] s).2)=BinaryEuclid.step^[t] (value s.1,value s.2) := by
   induction t with
   | zero => rfl
   | succ t ih =>
     rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
     rw [values_step _ (canonical_iter s hA hB t).2,ih]

 theorem run_second (A B : List Bool) : (run A B).2=[] := by
   have hc := (canonical_iter (trim A,trim B) (trim_idem A) (trim_idem B) (2*B.length)).2
   have hv := values_iter (trim A,trim B) (trim_idem A) (trim_idem B) (2*B.length)
   have ht := BinaryEuclid.terminates (value (trim A)) (value (trim B)) B.length (by rw [trim_value]; exact value_lt B)
   have hz : value (run A B).2=0 := by
     exact (congrArg Prod.snd hv).trans ht
   by_contra hn
   exact (ne_of_gt (value_positive _ hc hn)) hz

 theorem gcd_value (A B : List Bool) : value (gcd A B)=(value A).gcd (value B) := by
   have hv := values_iter (trim A,trim B) (trim_idem A) (trim_idem B) (2*B.length)
   have hg := BinaryEuclid.gcd_iter (value (trim A),value (trim B)) (2*B.length)
   have hv1 := congrArg Prod.fst hv
   have hv2 := congrArg Prod.snd hv
   change value (run A B).1=_ at hv1
   change value (run A B).2=_ at hv2
   rw [← hv1,← hv2,run_second,value,Nat.gcd_zero_right,trim_value,trim_value] at hg
   exact hg

 theorem length_step (s : List Bool×List Bool) : (step s).1.length+(step s).2.length≤ s.1.length+s.2.length := by
   unfold step
   split_ifs
   · rfl
   · have hh := (divide_lengths s.1 s.2).2
     dsimp only
     omega

 theorem length_iter (s : List Bool×List Bool) (t : ℕ) :
     (step^[t] s).1.length+(step^[t] s).2.length≤ s.1.length+s.2.length := by
   induction t with
   | zero => rfl
   | succ t ih => rw [Function.iterate_succ_apply']; exact (length_step _).trans ih

end BinaryGcd
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryCanonical
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 theorem natBits_eq_bits (n : ℕ) : natBits n=n.bits := by
   simp only [natBits,Nat.digits_two_eq_bits,List.map_map]
   have he : ((fun b : ℕ => b==1) ∘ (fun b : Bool => cond b 1 0))=id := by funext b; cases b <;> rfl
   rw [he,List.map_id]

 theorem trim_eq_bits_value (A : List Bool) : trim A=(value A).bits := by
   induction A with
   | nil => exact Nat.zero_bits.symm
   | cons b A ih =>
     by_cases hA : trim A=[]
     · have hv : value A=0 := by rw [← trim_value A,hA]; rfl
       cases b <;> simp [trim,hA,value,hv,Nat.zero_bits,Nat.one_bits]
     · have hp := BinaryGcd.value_positive (trim A) (trim_idem A) hA
       rw [trim_value] at hp
       have hb : Nat.bit b (value A)=b.toNat+2*value A := by cases b <;> simp [Nat.bit]; omega
       simp only [trim,hA,if_false]
       rw [ih,value,← hb,Nat.bits_append_bit (value A) b (by omega)]

 theorem trim_eq_natBits (A : List Bool) : trim A=natBits (value A) := by
   rw [natBits_eq_bits]
   exact trim_eq_bits_value A

 theorem canonical_eq_natBits (A : List Bool) (hA : trim A=A) : A=natBits (value A) := by
   exact hA.symm.trans (trim_eq_natBits A)

 theorem canonical_value_injective (A B : List Bool) (hA : trim A=A) (hB : trim B=B) (h : value A=value B) : A=B := by
   rw [canonical_eq_natBits A hA,canonical_eq_natBits B hB,h]

 theorem value_natBits (n : ℕ) : value (natBits n)=n := by
   rw [natBits_eq_bits]
   induction n using Nat.binaryRecFromOne with
   | zero => simp [Nat.zero_bits,value]
   | one => simp [Nat.one_bits,value]
   | bit b n hn ih =>
     rw [Nat.bits_append_bit n b (fun h => False.elim (hn h))]
     cases b <;> simp [value,ih,Nat.bit] <;> omega

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryAdderRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler

 def headBit : Realizer (fun A : List Bool => A.headD false) where
   transform := Data.head
   charge := fun x => x.size+2
   routine := Routine.select true
   correct A := by cases A <;> rfl

 def tailBits : Realizer (fun A : List Bool => A.tail) where
   transform := Data.tail
   charge := fun x => x.size+2
   routine := Routine.select false
   correct A := by cases A <;> rfl

 def xorBits : Realizer (fun x : Bool×Bool => xor x.1 x.2) :=
   (Realizer.not.choose Realizer.id).congr (fun x => by rcases x with ⟨a,b⟩; cases a <;> cases b <;> rfl)

 def bitA : Realizer (fun s : State => s.1.headD false) := Realizer.fst.comp headBit
 def bitB : Realizer (fun s : State => s.2.1.headD false) := (Realizer.snd.comp Realizer.fst).comp headBit
 def bitC : Realizer (fun s : State => s.2.2.1) := (Realizer.snd.comp Realizer.snd).comp Realizer.fst
 def revOutput : Realizer (fun s : State => s.2.2.2) := (Realizer.snd.comp Realizer.snd).comp Realizer.snd
 def sumBit : Realizer (fun s : State => xor (xor (s.1.headD false) (s.2.1.headD false)) s.2.2.1) :=
   (((bitA.pair bitB).comp xorBits).pair bitC).comp xorBits
 def carryBit : Realizer (fun s : State =>
     (s.1.headD false && s.2.1.headD false)||(s.1.headD false && s.2.2.1)||(s.2.1.headD false && s.2.2.1)) :=
   ((((bitA.pair bitB).comp Realizer.and).pair ((bitA.pair bitC).comp Realizer.and)).comp Realizer.or).pair
     ((bitB.pair bitC).comp Realizer.and) |>.comp Realizer.or

 def stepRealizer : Realizer step :=
   ((Realizer.fst.comp tailBits).pair
     (((Realizer.snd.comp Realizer.fst).comp tailBits).pair
       (carryBit.pair ((sumBit.pair revOutput).comp Realizer.cons)))).congr (fun _ => rfl)

 def wordLength : Realizer (fun A : List Bool => A.length) :=
   (Uniform.length (I := Unit) (α := fun _ => Bool)).specialize ()
 def lengthBound : Realizer (fun x : List Bool×List Bool => x.1.length+x.2.length+1) :=
   (((Realizer.fst.comp wordLength).pair (Realizer.snd.comp wordLength)).comp Realizer.add).comp Realizer.succ
 def initialState : Realizer (fun x : List Bool×List Bool => (x.1,(x.2,(false,([] : List Bool))))) :=
   Realizer.fst.pair (Realizer.snd.pair (Realizer.false.pair Realizer.nil))
 def wordRealizer : Realizer (fun x : List Bool×List Bool => word x.1 x.2) :=
   (((lengthBound.pair initialState).comp stepRealizer.iterate).comp revOutput).comp Realizer.reverse

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.NativeCompilerInterface
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.NativeCompiler
 theorem runs_mono (P : Program) (input output : List Bool) {t u : ℕ}
    (ht : Runs P input output t) (htu : t≤ u) : Runs P input output u := by
  obtain ⟨h⟩ := ht
  exact ⟨{h with steps_le_m := h.steps_le_m.trans htu}⟩
end EdgeSublinearMWIS.Main.NativeCompiler
end

-- Solutions.RealizerLinear
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 def Linear {f : α → β} (R : Realizer f) : Prop :=
   ∃ C : ℕ,0< C ∧ ∀ x,R.time x ≤ C*(volume x+1) ∧ volume (f x) ≤ C*(volume x+1)

 theorem linear_of {f : α → β} (R : Realizer f) (C : ℕ) (hC : 0< C)
    (ht : ∀x,R.time x≤ C*(volume x+1)) (hv : ∀x,volume (f x)≤ C*(volume x+1)) : Linear R :=
   ⟨C,hC,fun x => ⟨ht x,hv x⟩⟩

 theorem linear_comp {f : α → β} {g : β → γ} {R : Realizer f} {S : Realizer g}
    (hR : Linear R) (hS : Linear S) : Linear (R.comp S) := by
   obtain ⟨C,hC,hR⟩ := hR
   obtain ⟨D,hD,hS⟩ := hS
   refine ⟨C+(D+10)*(C+1),by positivity,?_⟩
   intro x
   have h1 := hR x
   have h2 := hS (f x)
   have hV : volume (f x)+1 ≤ (C+1)*(volume x+1) := by nlinarith
   have htime := (h2.1).trans (Nat.mul_le_mul_left D hV)
   have hout := (h2.2).trans (Nat.mul_le_mul_left D hV)
   have hcopy := Nat.mul_le_mul_left 10 hV
   constructor
   · rw [Realizer.time_comp]
     nlinarith
   · change volume (g (f x))≤ _
     nlinarith

 theorem linear_pair {f : α → β} {g : α → γ} {R : Realizer f} {S : Realizer g}
    (hR : Linear R) (hS : Linear S) : Linear (R.pair S) := by
   obtain ⟨C,hC,hR⟩ := hR
   obtain ⟨D,hD,hS⟩ := hS
   refine ⟨100*(C+D+1),by positivity,?_⟩
   intro x
   have h1 := hR x
   have h2 := hS x
   constructor
   · rw [Realizer.time_pair]
     nlinarith
   · simp only [volume_pair]
     nlinarith

 theorem linear_fst : Linear (Realizer.fst : Realizer (Prod.fst : α×β → α)) := by
   refine linear_of _ 3 (by omega) (fun x => by simp; omega) ?_
   rintro ⟨a,b⟩
   simp only [volume_pair]
   omega

 theorem linear_snd : Linear (Realizer.snd : Realizer (Prod.snd : α×β → β)) := by
   refine linear_of _ 3 (by omega) (fun x => by simp; omega) ?_
   rintro ⟨a,b⟩
   simp only [volume_pair]
   omega

 theorem linear_bool {f : α → Bool} (R : Realizer f) (C : ℕ) (ht : ∀x,R.time x≤ C*(volume x+1)) : Linear R := by
   refine linear_of R (C+3) (by omega) ?_ ?_
   · intro x; have hh := ht x; nlinarith
   · intro x; have hh := volume_bool (f x); nlinarith

 theorem linear_and : Linear Realizer.and := linear_bool _ 10000 (fun x =>
   (Realizer.time_and_le x).trans (by nlinarith))
 theorem linear_or : Linear Realizer.or := linear_bool _ 10000 (fun x =>
   (Realizer.time_or_le x).trans (by nlinarith))
 theorem linear_not : Linear Realizer.not := linear_bool _ 10000 (fun x =>
   (Realizer.time_not_le x).trans (by nlinarith))

theorem linear_finite [Fintype α] {f : α → β} (R : Realizer f) : Linear R := by
   let C := (∑ x : α, (R.time x+volume (f x)))+1
   refine ⟨C,by dsimp [C]; omega,?_⟩
   intro x
   have hx := Finset.single_le_sum (fun z (_ : z∈(Finset.univ : Finset α)) => Nat.zero_le (R.time z+volume (f z))) (Finset.mem_univ x)
   have hC : C≤ C*(volume x+1) := by nlinarith
   constructor <;> dsimp [C] at * <;> omega

 theorem linear_cons : Linear (Realizer.cons : Realizer (fun x : α×List α => x.1::x.2)) := by
   refine linear_of _ 3 (by omega) ?_ ?_
   · intro x
     change volume x+2≤3*(volume x+1)
     omega
   · rintro ⟨a,L⟩
     simp only [volume_cons,volume_pair]
     omega

 theorem linear_id : Linear (Realizer.id : Realizer (id : α → α)) :=
   linear_of _ 3 (by omega) (fun x => by change volume x+2≤ _; omega) (fun x => by change volume x≤3*(volume x+1); omega)

 theorem linear_choose {f g : α → β} {R : Realizer f} {S : Realizer g}
    (hR : Linear R) (hS : Linear S) : Linear (R.choose S) := by
   obtain ⟨C,hC,hR⟩ := hR
   obtain ⟨D,hD,hS⟩ := hS
   refine ⟨200*(C+D+1),by positivity,?_⟩
   rintro ⟨b,x⟩
   have hp : volume x+1≤ volume (b,x)+1 := by simp only [volume_pair]; omega
   have h1 := hR x
   have h2 := hS x
   have hc := Nat.mul_le_mul_left C hp
   have hd := Nat.mul_le_mul_left D hp
   constructor
   · simp only [Realizer.time_choose,Realizer.time_comp,Realizer.time_snd,Function.comp_apply]
     nlinarith
   · change volume (if b then f x else g x)≤ _
     split_ifs <;> nlinarith

 theorem linear_congr {f f' : α → β} (R : Realizer f) (hf : ∀x,f x=f' x) (hR : Linear R) : Linear (R.congr hf) := by
   obtain ⟨C,hC,hR⟩ := hR
   refine ⟨C,hC,?_⟩
   intro x
   have hh := hR x
   refine ⟨?_,?_⟩
   · simpa only [Realizer.time_congr] using hh.1
   · rw [← hf x]
     exact hh.2

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.AdderStepBound
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem headBit_linear : Linear headBit := by
   apply linear_bool headBit 3
   intro A
   change volume A+2≤3*(volume A+1)
   omega

 theorem tailBits_linear : Linear tailBits := by
   refine linear_of tailBits 3 (by omega) ?_ ?_
   · intro A
     change volume A+2≤3*(volume A+1)
     omega
   · intro A
     cases A with
     | nil => simp
     | cons a A => simp only [List.tail_cons,volume_cons]; omega

 theorem bitA_linear : Linear bitA := linear_comp linear_fst headBit_linear
 theorem bitB_linear : Linear bitB := linear_comp (linear_comp linear_snd linear_fst) headBit_linear
 theorem bitC_linear : Linear bitC := linear_comp (linear_comp linear_snd linear_snd) linear_fst
 theorem revOutput_linear : Linear revOutput := linear_comp (linear_comp linear_snd linear_snd) linear_snd
 theorem sumBit_linear : Linear sumBit :=
   linear_comp (linear_pair (linear_comp (linear_pair bitA_linear bitB_linear) (linear_finite xorBits)) bitC_linear) (linear_finite xorBits)
 theorem carryBit_linear : Linear carryBit :=
   linear_comp (linear_pair (linear_comp (linear_pair (linear_comp (linear_pair bitA_linear bitB_linear) linear_and)
     (linear_comp (linear_pair bitA_linear bitC_linear) linear_and)) linear_or)
     (linear_comp (linear_pair bitB_linear bitC_linear) linear_and)) linear_or
 theorem step_linear : Linear stepRealizer := by
   have hh := linear_pair (linear_comp (linear_fst : Linear (Realizer.fst : Realizer (Prod.fst : State → List Bool))) tailBits_linear)
     (linear_pair (linear_comp (linear_comp linear_snd linear_fst) tailBits_linear)
       (linear_pair carryBit_linear (linear_comp (linear_pair sumBit_linear revOutput_linear) linear_cons)))
   exact hh

 theorem step_volume (s : State) : volume (step s)≤ volume s+6 := by
   rcases s with ⟨A,B,c,R⟩
   have hA : volume A.tail≤ volume A := by cases A <;> simp [volume_cons] <;> omega
   have hB : volume B.tail≤ volume B := by cases B <;> simp [volume_cons] <;> omega
   have hsum := volume_bool (xor (xor (A.headD false) (B.headD false)) c)
   have hcarry := volume_bool ((A.headD false && B.headD false)||(A.headD false && c)||(B.headD false && c))
   have hc : 1≤ volume c := volume_pos c
   simp only [step,volume_pair,volume_cons]
   omega

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.WordLengthBound
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler

 theorem volume_bits (A : List Bool) : volume A≤4*A.length+1 :=
   (volume_list_le A 3 (fun b _ => volume_bool b)).trans (by omega)

 theorem length_step_time (a : Bool) (b : ℕ) :
     ((Realizer.snd : Realizer (Prod.snd : Bool×ℕ → ℕ)).comp Realizer.succ).time (a,b)≤1000*(b+1) := by
   rw [Realizer.time_comp,Realizer.time_snd]
   have ht := Realizer.time_succ_le b
   simp only [volume_pair,volume_nat]
   have hb := volume_bool a
   nlinarith

 theorem length_fold_time (A : List Bool) (b : ℕ) :
     Realizer.foldTime ((Realizer.snd : Realizer (Prod.snd : Bool×ℕ → ℕ)).comp Realizer.succ) b A ≤
       10000*(A.length+1)*(volume A+2*b+2*A.length+1) := by
   induction A generalizing b with
   | nil => simp [Realizer.foldTime,volume_nil]; omega
   | cons a A ih =>
     have hh := ih (b+1)
     have ht := length_step_time a b
     have ha := volume_bool a
     have hp := volume_pos A
     change _+Realizer.foldTime _ (b+1) A+20*(volume (a::A)+volume b+volume (b+1)+1) ≤ _
     simp only [volume_cons,volume_nat,List.length_cons] at hh ⊢
     nlinarith

 theorem wordLength_time (A : List Bool) : wordLength.time A≤1000000*(A.length+1)^2 := by
   have hf := length_fold_time A 0
   have hv := volume_bits A
   change (Uniform.length (I:=Unit) (α:=fun _ => Bool)).time () A≤ _
   rw [Uniform.length,Uniform.time_congr,Uniform.time_comp,Uniform.time_pair,Uniform.time_id,Uniform.time_zero,Uniform.time_fold]
   simp only [Uniform.time_uniform,Function.comp_apply,volume_pair,volume_nat,Nat.mul_zero,Nat.add_zero] at hf ⊢
   have hfold : Realizer.foldTime
       (((Uniform.snd (I:=Unit) (α:=fun _ => Bool) (β:=fun _ => ℕ)).comp (Realizer.succ.uniform Unit)).specialize ()) 0 A≤
       10000*(A.length+1)*(volume A+2*A.length+1) := hf
   have hf' : Realizer.foldTime
       (((Uniform.snd (I:=Unit) (α:=fun _ => Bool) (β:=fun _ => ℕ)).comp (Realizer.succ.uniform Unit)).specialize ()) 0 A≤100000*(A.length+1)^2 := by
     calc
       _ ≤ 10000*(A.length+1)*(volume A+2*A.length+1) := hfold
       _ ≤ 10000*(A.length+1)*(6*A.length+2) := Nat.mul_le_mul_left _ (by omega)
       _ ≤ _ := by nlinarith
   nlinarith

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.AdderRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem iter_volume (s : State) (t : ℕ) : volume ((step^[t]) s)≤ volume s+6*t := by
   induction t with
   | zero => simp
   | succ t ih => rw [Function.iterate_succ_apply']; have hh := step_volume ((step^[t]) s); omega

 theorem initial_volume (A B : List Bool) : volume (A,(B,(false,([] : List Bool))))≤4*(A.length+B.length)+7 := by
   have hA := volume_bits A
   have hB := volume_bits B
   simp only [volume_pair,volume_bool_false,volume_nil]
   omega

 theorem iterate_time : ∃ C : ℕ,0< C ∧ ∀ A B : List Bool,
     stepRealizer.iterate.time (A.length+B.length+1,(A,(B,(false,([] : List Bool)))))≤ C*(A.length+B.length+1)^2 := by
   obtain ⟨C,hC,hlinear⟩ := step_linear
   refine ⟨1000000*(C+1),by positivity,?_⟩
   intro A B
   let z := A.length+B.length+1
   let s : State := (A,(B,(false,[])))
   have hz : 1≤ z := by dsimp [z]; omega
   have hvol (j : ℕ) (hj : j≤ z) : volume ((step^[j]) s)≤14*z := by
     have hi := initial_volume A B
     have hv := iter_volume s j
     dsimp [s,z] at *
     omega
   have htime (j : ℕ) (hj : j< z) : stepRealizer.time ((step^[j]) s)≤ C*(14*z+1) :=
     ((hlinear _).1).trans (Nat.mul_le_mul_left C (by have hh := hvol j hj.le; omega))
   have hh := Realizer.time_iterate_le stepRealizer z s (C*(14*z+1)) (14*z) htime hvol
   calc
     _ ≤ 10000*(z+1)*(C*(14*z+1)+14*z+z+1) := hh
     _ ≤ 10000*(2*z)*((15*C+16)*z) := by
       apply Nat.mul_le_mul
       · exact Nat.mul_le_mul_left _ (by omega)
       · have hc := Nat.mul_le_mul_left C (show 14*z+1≤15*z by omega)
         nlinarith
     _ = (20000*(15*C+16))*z^2 := by ring
     _ ≤ (1000000*(C+1))*z^2 := Nat.mul_le_mul_right _ (by omega)

 theorem lengthBound_time (A B : List Bool) :
     lengthBound.time (A,B)≤1000000000*(A.length+B.length+1)^2 := by
   have hA := wordLength_time A
   have hB := wordLength_time B
   have hvA := volume_bits A
   have hvB := volume_bits B
   have ha := Realizer.time_add_le A.length B.length
   have hs := Realizer.time_succ_le (A.length+B.length)
   simp only [lengthBound,Realizer.time_comp,Realizer.time_pair,Realizer.time_fst,Realizer.time_snd,Function.comp_apply,volume_pair,volume_nat]
   have hLA : (A.length+1)^2≤(A.length+B.length+1)^2 := Nat.pow_le_pow_left (by omega) 2
   have hLB : (B.length+1)^2≤(A.length+B.length+1)^2 := Nat.pow_le_pow_left (by omega) 2
   have hA' := hA.trans (Nat.mul_le_mul_left 1000000 hLA)
   have hB' := hB.trans (Nat.mul_le_mul_left 1000000 hLB)
   nlinarith

 theorem initial_linear : Linear initialState := by
   have hfalse : Linear (Realizer.false : Realizer (fun _ : List Bool×List Bool => false)) := by
     refine linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   have hnil : Linear (Realizer.nil : Realizer (fun _ : List Bool×List Bool => ([] : List Bool))) := by
     refine linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   exact linear_pair linear_fst (linear_pair linear_snd (linear_pair hfalse hnil))

 theorem reverse_time (A : List Bool) : (Realizer.reverse : Realizer (fun A : List Bool => A.reverse)).time A≤200*(A.length+1)*(volume A+1) :=
   Uniform.time_reverse (I:=Unit) (α:=fun _ => Bool) () A

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.AdderTotalRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem word_time : ∃ C : ℕ,0< C ∧ ∀ A B : List Bool,
     wordRealizer.time (A,B)≤ C*(A.length+B.length+1)^2 := by
   obtain ⟨C,hC,hiter⟩ := iterate_time
   obtain ⟨I,hI,hinit⟩ := initial_linear
   obtain ⟨O,hO,hout⟩ := revOutput_linear
   refine ⟨1000000000+C+5*I+15*O+20000,by positivity,?_⟩
   intro A B
   let z := A.length+B.length+1
   let s : State := (A,(B,(false,[])))
   let t : State := (step^[z]) s
   have hz : 1≤ z := by dsimp [z]; omega
   have hzsq : z≤ z^2 := by nlinarith
   have hvA := volume_bits A
   have hvB := volume_bits B
   have hvx : volume (A,B)≤4*z := by simp only [volume_pair]; dsimp [z]; omega
   have hvs : volume s≤7*z := by have hh := initial_volume A B; dsimp [s,z] at *; omega
   have hvt : volume t≤14*z := by have hh := iter_volume s z; dsimp [t]; omega
   have hvr : volume t.2.2.2≤ volume t := by
     rcases t with ⟨T,U,c,R⟩
     simp only [volume_pair]
     omega
   have hlen : t.2.2.2.length=z := by
     have hh := (iter_lists s z).2.2
     simpa [s] using hh
   have hinit0 := (hinit (A,B)).1
   have hinit1 : initialState.time (A,B)≤5*I*z^2 := by
     calc
       _ ≤ I*(volume (A,B)+1) := hinit0
       _ ≤ I*(5*z) := Nat.mul_le_mul_left _ (by omega)
       _ ≤ 5*I*z^2 := by nlinarith [Nat.mul_le_mul_left (5*I) hzsq]
   have hout0 := (hout t).1
   have hout1 : revOutput.time t≤15*O*z^2 := by
     calc
       _ ≤ O*(volume t+1) := hout0
       _ ≤ O*(15*z) := Nat.mul_le_mul_left _ (by omega)
       _ ≤ 15*O*z^2 := by nlinarith [Nat.mul_le_mul_left (15*O) hzsq]
   have hr := reverse_time t.2.2.2
   have hr1 : (Realizer.reverse : Realizer (fun A : List Bool => A.reverse)).time t.2.2.2≤6000*z^2 := by
     calc
       _ ≤ 200*(z+1)*(volume t.2.2.2+1) := by simpa only [hlen] using hr
       _ ≤ 200*(2*z)*(15*z) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
       _ = 6000*z^2 := by ring
   have hiter1 : stepRealizer.iterate.time (z,s)≤ C*z^2 := hiter A B
   have hlen1 : lengthBound.time (A,B)≤1000000000*z^2 := lengthBound_time A B
   have hvolZ : volume z=2*z+1 := volume_nat z
   have hcopy0 : 20*(volume (A,B)+volume z+volume s+1)+10*(volume (z,s)+1)+10*(volume t+1)+10*(volume t.2.2.2+1)≤10000*z^2 := by
     simp only [volume_pair,hvolZ]
     omega
   have hrealtime : wordRealizer.time (A,B)=lengthBound.time (A,B)+initialState.time (A,B)+
       20*(volume (A,B)+volume z+volume s+1)+stepRealizer.iterate.time (z,s)+10*(volume (z,s)+1)+
       revOutput.time t+10*(volume t+1)+
       (Realizer.reverse : Realizer (fun A : List Bool => A.reverse)).time t.2.2.2+10*(volume t.2.2.2+1) := by
     dsimp only [wordRealizer,word]
     simp only [Realizer.time_comp,Realizer.time_pair,Function.comp_apply,volume_reverse]
     rfl
   rw [hrealtime]
   change _≤(1000000000+C+5*I+15*O+20000)*z^2
   nlinarith only [hinit1,hout1,hr1,hiter1,hlen1,hcopy0]

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.BinaryTrimRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def nonemptyBits : Realizer (fun L : List Bool => !L.isEmpty) :=
   (Uniform.isCons (I:=Unit) (α:=fun _ => Bool)).specialize ()
 def keepBit : Realizer (fun x : Bool×List Bool => x.1 || !x.2.isEmpty) :=
   (Realizer.fst.pair (Realizer.snd.comp nonemptyBits)).comp Realizer.or
 def trimStepRealizer : Realizer trimStep :=
   ((keepBit.pair Realizer.id).comp (Realizer.cons.choose Realizer.nil)).congr (fun x => by
     rcases x with ⟨b,L⟩
     cases L with
     | nil => cases b <;> rfl
     | cons a L => cases b <;> rfl)
 def trimRealizer : Realizer trim :=
   (((Realizer.reverse : Realizer (fun L : List Bool => L.reverse)).pair Realizer.nil).comp trimStepRealizer.fold).congr (fun L => trim_fold L)

 theorem nonempty_linear : Linear nonemptyBits := by
   apply linear_bool nonemptyBits 10000
   intro L
   exact Realizer.time_test_le (fun L : List Bool => !L.isEmpty) (by intro L; cases L <;> rfl) L

 theorem trimStep_linear : Linear trimStepRealizer := by
   have hkeep : Linear keepBit := linear_comp (linear_pair linear_fst (linear_comp linear_snd nonempty_linear)) linear_or
   have hcons : Linear (Realizer.cons : Realizer (fun x : Bool×List Bool => x.1::x.2)) := linear_cons
   have hnil : Linear (Realizer.nil : Realizer (fun _ : Bool×List Bool => ([] : List Bool))) :=
     linear_of _ 3 (by omega) (fun x => by change 2≤ _; omega) (fun x => by simp; omega)
   unfold trimStepRealizer
   apply linear_congr
   exact linear_comp (linear_pair hkeep linear_id) (linear_choose hcons hnil)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.TrimRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem trimStep_volume (b : Bool) (T : List Bool) : volume (trimStep (b,T))≤ volume T+4 := by
   cases T with
   | nil => cases b <;> decide
   | cons a T => simp only [trimStep,List.cons_ne_nil,if_false,volume_cons]; have hb := volume_bool b; omega

 theorem trim_fold_time : ∃ C : ℕ,0< C ∧ ∀ (L T : List Bool),
     Realizer.foldTime trimStepRealizer T L≤ C*(L.length+1)*(volume L+volume T+4*L.length+1) := by
   obtain ⟨C,hC,hlin⟩ := trimStep_linear
   let K := 100*(C+1)
   refine ⟨K,by dsimp [K]; positivity,?_⟩
   intro L
   induction L with
   | nil =>
     intro T
     simp only [Realizer.foldTime,List.length_nil,volume_nil,Nat.zero_mul,Nat.zero_add,Nat.mul_one]
     dsimp [K]
     nlinarith
   | cons b L ih =>
     intro T
     let V := volume (b::L)+volume T+4*(b::L).length+1
     have hVpos : 1≤ V := by dsimp [V]; omega
     have hL := volume_pos L
     have hT := volume_pos T
     have hb := volume_bool b
     have hstep := trimStep_volume b T
     have hrec := ih (trimStep (b,T))
     have hsub : volume L+volume (trimStep (b,T))+4*L.length+1≤ V := by
       dsimp [V]
       simp only [volume_cons,List.length_cons]
       omega
     have hrec' : Realizer.foldTime trimStepRealizer (trimStep (b,T)) L≤ K*(L.length+1)*V :=
       hrec.trans (Nat.mul_le_mul_left _ hsub)
     have harg : volume (b,T)+1≤ V := by dsimp [V]; simp only [volume_cons,volume_pair,List.length_cons]; omega
     have htime : trimStepRealizer.time (b,T)≤ C*V :=
       ((hlin (b,T)).1).trans (Nat.mul_le_mul_left _ harg)
     have hcopy : 20*(volume (b::L)+volume T+volume (trimStep (b,T))+1)≤80*V := by
       have hh1 : volume (b::L)≤ V := by dsimp [V]; omega
       have hh2 : volume T≤ V := by dsimp [V]; omega
       have hh3 : volume (trimStep (b,T))≤ V := by dsimp [V]; omega
       omega
     have hcoeff : (C+80)*V≤ K*V := Nat.mul_le_mul_right _ (by dsimp [K]; omega)
     change trimStepRealizer.time (b,T)+Realizer.foldTime trimStepRealizer (trimStep (b,T)) L+
       20*(volume (b::L)+volume T+volume (trimStep (b,T))+1)≤ K*((b::L).length+1)*V
     simp only [List.length_cons]
     nlinarith only [htime,hrec',hcopy,hcoeff]

 theorem trim_time : ∃ C : ℕ,0< C ∧ ∀ L : List Bool,trimRealizer.time L≤ C*(L.length+1)^2 := by
   obtain ⟨C,hC,hfold⟩ := trim_fold_time
   refine ⟨10000*(C+1),by positivity,?_⟩
   intro L
   have hv := BinaryAdder.volume_bits L
   have hr := BinaryAdder.reverse_time L
   have hf := hfold L.reverse []
   simp only [List.length_reverse,volume_reverse,volume_nil] at hf
   have hf' : Realizer.foldTime trimStepRealizer [] L.reverse≤8*C*(L.length+1)^2 := by
     calc
       _ ≤ C*(L.length+1)*(volume L+1+4*L.length+1) := hf
       _ ≤ C*(L.length+1)*(8*(L.length+1)) := Nat.mul_le_mul_left _ (by omega)
       _ = _ := by ring
   have hr' : (Realizer.reverse : Realizer (fun L : List Bool => L.reverse)).time L≤1000*(L.length+1)^2 := by
     calc
       _ ≤ 200*(L.length+1)*(volume L+1) := hr
       _ ≤ 200*(L.length+1)*(5*(L.length+1)) := Nat.mul_le_mul_left _ (by omega)
       _ = _ := by ring
   have hnil : (Realizer.nil : Realizer (fun _ : List Bool => ([] : List Bool))).time L=2 := rfl
   have he : trimRealizer.time L=(Realizer.reverse : Realizer (fun L : List Bool => L.reverse)).time L+2+
       20*(volume L+volume L+1+1)+(2*volume (L.reverse,([] : List Bool))+6+Realizer.foldTime trimStepRealizer [] L.reverse)+
       10*(volume (L.reverse,([] : List Bool))+1) := by
     simp only [trimRealizer,Realizer.time_congr,Realizer.time_comp,Realizer.time_pair,hnil,volume_nil,Realizer.time_fold,Function.comp_apply,volume_reverse]
   rw [he]
   simp only [volume_pair,volume_reverse,volume_nil]
   nlinarith only [hr',hf',hv]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryMultiplyRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler

 def addThenTrim : Realizer (fun x : List Bool×List Bool => trim (BinaryAdder.word x.2 x.1)) :=
   ((Realizer.snd.pair Realizer.fst).comp BinaryAdder.wordRealizer).comp trimRealizer
 def selectedSum : Realizer (fun x : Bool×(List Bool×List Bool) =>
     if x.1 then trim (BinaryAdder.word x.2.2 x.2.1) else x.2.2) :=
   addThenTrim.choose Realizer.snd
 def shiftedWord : Realizer (fun x : Bool×(List Bool×List Bool) => false::x.2.1) :=
   (Realizer.false.pair (Realizer.snd.comp Realizer.fst)).comp Realizer.cons
 def multiplyStepRealizer : Realizer multiplyStep :=
   (shiftedWord.pair selectedSum).congr (fun _ => rfl)
 def multiplyInitial : Realizer (fun x : List Bool×List Bool => (x.2,(x.1,([] : List Bool)))) :=
   Realizer.snd.pair (Realizer.fst.pair Realizer.nil)
 def multiplyRealizer : Realizer (fun x : List Bool×List Bool => multiply x.1 x.2) :=
   (((multiplyInitial.comp multiplyStepRealizer.fold).comp Realizer.snd).comp trimRealizer).congr (fun _ => rfl)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RealizerPolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 def PolyBound {f : α → β} (R : Realizer f) : Prop :=
   ∃ C q : ℕ,0< C ∧ ∀ x,R.time x≤ C*(volume x+1)^q ∧ volume (f x)≤ C*(volume x+1)^q

 theorem linear_polynomial {f : α → β} {R : Realizer f} (hR : Linear R) : PolyBound R := by
   obtain ⟨C,hC,hR⟩ := hR
   exact ⟨C,1,hC,by simpa only [pow_one] using hR⟩

 theorem polynomial_comp {f : α → β} {g : β → γ} {R : Realizer f} {S : Realizer g}
    (hR : PolyBound R) (hS : PolyBound S) : PolyBound (R.comp S) := by
   obtain ⟨C,q,hC,hR⟩ := hR
   obtain ⟨D,r,hD,hS⟩ := hS
   refine ⟨C+D*(C+1)^r+10*(C+1),q+q*r,by positivity,?_⟩
   intro x
   let z := volume x+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hq : 1≤ z^q := one_le_pow₀ hz
   have h1 := hR x
   change R.time x≤ C*z^q ∧ volume (f x)≤ C*z^q at h1
   have h2 := hS (f x)
   have hV : volume (f x)+1≤(C+1)*z^q := by change volume (f x)+1≤ _; nlinarith
   have hVp := Nat.pow_le_pow_left hV r
   have hPow : ((C+1)*z^q)^r=(C+1)^r*z^(q*r) := by rw [mul_pow,pow_mul]
   rw [hPow] at hVp
   have hqr : z^q≤ z^(q+q*r) := Nat.pow_le_pow_right hz (by omega)
   have hrr : z^(q*r)≤ z^(q+q*r) := Nat.pow_le_pow_right hz (by omega)
   have htime1 := h1.1.trans (Nat.mul_le_mul_left C hqr)
   have htime2 := h2.1.trans (Nat.mul_le_mul_left D hVp)
   have htime2 := htime2.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+1)^r) hrr)
   have hcopy := (Nat.mul_le_mul_left 10 hV).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (10*(C+1)) hqr)
   have hout := h2.2.trans (Nat.mul_le_mul_left D hVp)
   have hout := hout.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+1)^r) hrr)
   constructor
   · rw [Realizer.time_comp]
     change _≤(C+D*(C+1)^r+10*(C+1))*z^(q+q*r)
     nlinarith only [htime1,htime2,hcopy]
   · change volume (g (f x))≤(C+D*(C+1)^r+10*(C+1))*z^(q+q*r)
     exact hout.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (z^(q+q*r)) (show D*(C+1)^r≤ C+D*(C+1)^r+10*(C+1) by omega))

 theorem polynomial_pair {f : α → β} {g : α → γ} {R : Realizer f} {S : Realizer g}
    (hR : PolyBound R) (hS : PolyBound S) : PolyBound (R.pair S) := by
   obtain ⟨C,q,hC,hR⟩ := hR
   obtain ⟨D,r,hD,hS⟩ := hS
   refine ⟨100*(C+D+1),q+r+1,by positivity,?_⟩
   intro x
   let z := volume x+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hp : z≤ z^(q+r+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+r+1)
   have hq : z^q≤ z^(q+r+1) := Nat.pow_le_pow_right hz (by omega)
   have hr : z^r≤ z^(q+r+1) := Nat.pow_le_pow_right hz (by omega)
   have h1 := hR x
   have h2 := hS x
   have ht1 := h1.1.trans (Nat.mul_le_mul_left C hq)
   have ht2 := h2.1.trans (Nat.mul_le_mul_left D hr)
   have hv1 := h1.2.trans (Nat.mul_le_mul_left C hq)
   have hv2 := h2.2.trans (Nat.mul_le_mul_left D hr)
   constructor
   · rw [Realizer.time_pair]
     change _≤100*(C+D+1)*z^(q+r+1)
     change z≤ z^(q+r+1) at hp
     have hsmall : R.time x+S.time x+20*(volume x+volume (f x)+volume (g x)+1)≤(21*C+21*D+20)*z^(q+r+1) := by
       have hp' : volume x+1≤ z^(q+r+1) := hp
       nlinarith only [ht1,ht2,hv1,hv2,hp']
     exact hsmall.trans (Nat.mul_le_mul_right _ (by omega))
   · simp only [volume_pair]
     change _≤100*(C+D+1)*z^(q+r+1)
     have hp1 : 1≤ z^(q+r+1) := one_le_pow₀ hz
     have hsmall : volume (f x)+volume (g x)+1≤(C+D+1)*z^(q+r+1) := by nlinarith only [hv1,hv2,hp1]
     exact hsmall.trans (Nat.mul_le_mul_right _ (by omega))

 theorem polynomial_congr {f f' : α → β} (R : Realizer f) (hf : ∀x,f x=f' x)
    (hR : PolyBound R) : PolyBound (R.congr hf) := by
   obtain ⟨C,q,hC,hR⟩ := hR
   refine ⟨C,q,hC,?_⟩
   intro x
   have hh := hR x
   refine ⟨?_,?_⟩
   · simpa only [Realizer.time_congr] using hh.1
   · rw [← hf x]
     exact hh.2

 theorem polynomial_choose {f g : α → β} {R : Realizer f} {S : Realizer g}
    (hR : PolyBound R) (hS : PolyBound S) : PolyBound (R.choose S) := by
   obtain ⟨C,q,hC,hR⟩ := hR
   obtain ⟨D,r,hD,hS⟩ := hS
   refine ⟨200*(C+D+1),q+r+1,by positivity,?_⟩
   rintro ⟨b,x⟩
   let z := volume (b,x)+1
   let p := z^(q+r+1)
   have hz : 1≤ z := by dsimp [z]; omega
   have hx : volume x+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hq : (volume x+1)^q≤ p := (Nat.pow_le_pow_left hx q).trans (Nat.pow_le_pow_right hz (by omega))
   have hr : (volume x+1)^r≤ p := (Nat.pow_le_pow_left hx r).trans (Nat.pow_le_pow_right hz (by omega))
   have hp : z≤ p := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+r+1)
   have h1 := hR x
   have h2 := hS x
   have ht1 := h1.1.trans (Nat.mul_le_mul_left C hq)
   have ht2 := h2.1.trans (Nat.mul_le_mul_left D hr)
   have hv1 := h1.2.trans (Nat.mul_le_mul_left C hq)
   have hv2 := h2.2.trans (Nat.mul_le_mul_left D hr)
   constructor
   · simp only [Realizer.time_choose,Realizer.time_comp,Realizer.time_snd]
     change _≤200*(C+D+1)*p
     have hsmall : volume (b,x)+2+R.time x+10*(volume x+1)+(volume (b,x)+2+S.time x+10*(volume x+1))+
         30*(volume (b,x)+volume (f x)+volume (g x)+1)≤(31*C+31*D+100)*p := by
       dsimp [z] at hx hp
       nlinarith only [ht1,ht2,hv1,hv2,hx,hp]
     exact hsmall.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (if b then f x else g x)≤200*(C+D+1)*p
     split_ifs
     · exact hv1.trans (Nat.mul_le_mul_right _ (by omega))
     · exact hv2.trans (Nat.mul_le_mul_right _ (by omega))

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.BinaryArithmeticPolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem bits_length_volume (L : List Bool) : L.length≤ volume L := by
   induction L with
   | nil => simp
   | cons b L ih => simp only [List.length_cons,volume_cons]; omega

 theorem word_polynomial : PolyBound BinaryAdder.wordRealizer := by
   obtain ⟨C,hC,hT⟩ := BinaryAdder.word_time
   refine ⟨C+5,2,by omega,?_⟩
   rintro ⟨A,B⟩
   have ha := bits_length_volume A
   have hb := bits_length_volume B
   have hV : A.length+B.length+1≤ volume (A,B)+1 := by simp only [volume_pair]; omega
   have hp := Nat.pow_le_pow_left hV 2
   have ht := (hT A B).trans (Nat.mul_le_mul_left C hp)
   have hv := BinaryAdder.volume_bits (BinaryAdder.word A B)
   rw [BinaryAdder.word_length] at hv
   have hz : 1≤ volume (A,B)+1 := by omega
   have hsq : volume (A,B)+1≤(volume (A,B)+1)^2 := by nlinarith
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (BinaryAdder.word A B)≤ _
     have hv' : volume (BinaryAdder.word A B)≤5*(volume (A,B)+1)^2 := by nlinarith
     exact hv'.trans (Nat.mul_le_mul_right _ (by omega))

 theorem trim_polynomial : PolyBound trimRealizer := by
   obtain ⟨C,hC,hT⟩ := trim_time
   refine ⟨C+5,2,by omega,?_⟩
   intro L
   have hlen := bits_length_volume L
   have hp := Nat.pow_le_pow_left (show L.length+1≤ volume L+1 by omega) 2
   have ht := (hT L).trans (Nat.mul_le_mul_left C hp)
   have hv := BinaryAdder.volume_bits (trim L)
   have htrim := trim_length L
   have hz : 1≤ volume L+1 := by omega
   have hsq : volume L+1≤(volume L+1)^2 := by nlinarith
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · have hv' : volume (trim L)≤5*(volume L+1)^2 := by nlinarith
     exact hv'.trans (Nat.mul_le_mul_right _ (by omega))

 theorem addThenTrim_polynomial : PolyBound addThenTrim :=
   polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_snd) (linear_polynomial linear_fst)) word_polynomial) trim_polynomial
 theorem selectedSum_polynomial : PolyBound selectedSum :=
   polynomial_choose addThenTrim_polynomial (linear_polynomial linear_snd)
 theorem shiftedWord_polynomial : PolyBound shiftedWord := by
   have hf : Linear (Realizer.false : Realizer (fun _ : Bool×(List Bool×List Bool) => false)) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   exact linear_polynomial (linear_comp (linear_pair hf (linear_comp linear_snd linear_fst)) linear_cons)
 theorem multiplyStep_polynomial : PolyBound multiplyStepRealizer := by
   unfold multiplyStepRealizer
   apply polynomial_congr
   exact polynomial_pair shiftedWord_polynomial selectedSum_polynomial

 theorem reverse_polynomial : PolyBound (Realizer.reverse : Realizer (fun L : List Bool => L.reverse)) := by
   refine ⟨201,2,by omega,?_⟩
   intro L
   have hlen := bits_length_volume L
   have hT := BinaryAdder.reverse_time L
   have hmul := Nat.mul_le_mul_right (200*(volume L+1)) (show L.length+1≤ volume L+1 by omega)
   have hv : volume L≤(volume L+1)^2 := by nlinarith
   constructor
   · have hh : 200*(L.length+1)*(volume L+1)≤200*(volume L+1)^2 := by nlinarith only [hmul]
     exact (hT.trans hh).trans (Nat.mul_le_mul_right _ (by omega))
   · rw [volume_reverse]
     exact hv.trans (Nat.le_mul_of_pos_left _ (by omega))

 theorem lengthBound_polynomial : PolyBound BinaryAdder.lengthBound := by
   refine ⟨1000000001,2,by omega,?_⟩
   rintro ⟨A,B⟩
   have hA := bits_length_volume A
   have hB := bits_length_volume B
   have hbase : A.length+B.length+1≤ volume (A,B)+1 := by simp only [volume_pair]; omega
   have hp := Nat.pow_le_pow_left hbase 2
   have ht := (BinaryAdder.lengthBound_time A B).trans (Nat.mul_le_mul_left 1000000000 hp)
   have hz : volume (A,B)+1≤(volume (A,B)+1)^2 := by nlinarith
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (A.length+B.length+1)≤ _
     rw [volume_nat]
     nlinarith

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialIterate
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

 theorem iterate_coefficient (F D : ℕ) : 10000*F+10000*(D+3)≤100000*(F+D+10) := by omega
 theorem iterate_output_coefficient (F D : ℕ) : D+1≤100000*(F+D+10) := by omega

 theorem polynomial_iterate {f : α → α} {R : Realizer f} (hR : PolyBound R) (D : ℕ)
    (hg : ∀x,volume (f x)≤ volume x+D) : PolyBound R.iterate := by
   obtain ⟨C,q,hC,hR⟩ := hR
   let F := C*(D+2)^q
   refine ⟨100000*(F+D+10),q+2,by dsimp [F]; positivity,?_⟩
   rintro ⟨n,a⟩
   let z := volume (n,a)+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hn : n+1≤ z := by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have ha : volume a≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hiter (j : ℕ) : volume (f^[j] a)≤ volume a+D*j := by
     induction j with
     | zero => simp
     | succ j ih => rw [Function.iterate_succ_apply']; have hh := hg (f^[j] a); nlinarith
   have hV (j : ℕ) (hj : j≤ n) : volume (f^[j] a)≤(D+1)*z := by
     have hh := hiter j
     have hd := Nat.mul_le_mul_left D (show j≤ z by omega)
     nlinarith
   have hT (j : ℕ) (hj : j< n) : R.time (f^[j] a)≤ F*z^q := by
     have hh := (hR (f^[j] a)).1
     have hv := hV j hj.le
     have hbase : volume (f^[j] a)+1≤(D+2)*z := by nlinarith
     have ht := hh.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
     simpa only [F,mul_pow,Nat.mul_assoc] using ht
   have ht := Realizer.time_iterate_le R n a (F*z^q) ((D+1)*z) hT hV
   have hq : z^(q+1)≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hq2 : z^2≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hze : z≤ z^(q+2) := by exact (show z≤ z^2 by nlinarith).trans hq2
   constructor
   · change _≤100000*(F+D+10)*z^(q+2)
     have hmul : (n+1)*(F*z^q+(D+1)*z+n+1)≤ z*(F*z^q+(D+3)*z) :=
       Nat.mul_le_mul hn (by nlinarith)
     have hmul' := Nat.mul_le_mul_left 10000 hmul
     have hp1 := Nat.mul_le_mul_left (10000*F) hq
     have hp2 := Nat.mul_le_mul_left (10000*(D+3)) hq2
     have hsmall : R.iterate.time (n,a)≤(10000*F+10000*(D+3))*z^(q+2) := by
       rw [pow_succ] at hp1
       nlinarith only [ht,hmul',hp1,hp2]
     have hcoef := iterate_coefficient F D
     exact hsmall.trans (Nat.mul_le_mul_right (z^(q+2)) hcoef)
   · change volume (f^[n] a)≤100000*(F+D+10)*z^(q+2)
     have hcoef := iterate_output_coefficient F D
     exact (hV n le_rfl).trans ((Nat.mul_le_mul_left (D+1) hze).trans (Nat.mul_le_mul_right (z^(q+2)) hcoef))

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.BinarySubtractRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.BinarySubtract
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def notA : Realizer (fun s : State => !s.1.headD false) := BinaryAdder.bitA.comp Realizer.not
 def borrowBit : Realizer (fun s : State =>
     (!s.1.headD false && (s.2.1.headD false || s.2.2.1))||(s.2.1.headD false && s.2.2.1)) :=
   ((notA.pair ((BinaryAdder.bitB.pair BinaryAdder.bitC).comp Realizer.or)).comp Realizer.and).pair
     ((BinaryAdder.bitB.pair BinaryAdder.bitC).comp Realizer.and) |>.comp Realizer.or
 def stepRealizer : Realizer step :=
   ((Realizer.fst.comp BinaryAdder.tailBits).pair
     (((Realizer.snd.comp Realizer.fst).comp BinaryAdder.tailBits).pair
       (borrowBit.pair ((BinaryAdder.sumBit.pair BinaryAdder.revOutput).comp Realizer.cons)))).congr (fun _ => rfl)
 def rawRealizer : Realizer (fun x : List Bool×List Bool => raw x.1 x.2) :=
   (((BinaryAdder.lengthBound.pair BinaryAdder.initialState).comp stepRealizer.iterate).comp
     (BinaryAdder.bitC.pair (BinaryAdder.revOutput.comp Realizer.reverse))).congr (fun _ => rfl)
 def lessRealizer : Realizer (fun x : List Bool×List Bool => less x.1 x.2) := rawRealizer.comp Realizer.fst
 def differenceRealizer : Realizer (fun x : List Bool×List Bool => difference x.1 x.2) :=
   (rawRealizer.comp (Realizer.nil.choose RawStack.trimRealizer)).congr (fun _ => rfl)

 theorem step_linear : Linear stepRealizer := by
   have hnot : Linear notA := linear_comp BinaryAdder.bitA_linear linear_not
   have hborrow : Linear borrowBit := linear_comp
     (linear_pair (linear_comp (linear_pair hnot (linear_comp (linear_pair BinaryAdder.bitB_linear BinaryAdder.bitC_linear) linear_or)) linear_and)
       (linear_comp (linear_pair BinaryAdder.bitB_linear BinaryAdder.bitC_linear) linear_and)) linear_or
   unfold stepRealizer
   apply linear_congr
   exact linear_pair (linear_comp linear_fst BinaryAdder.tailBits_linear)
     (linear_pair (linear_comp (linear_comp linear_snd linear_fst) BinaryAdder.tailBits_linear)
       (linear_pair hborrow (linear_comp (linear_pair BinaryAdder.sumBit_linear BinaryAdder.revOutput_linear) linear_cons)))

 theorem step_volume (s : State) : volume (step s)≤ volume s+6 := by
   rcases s with ⟨A,B,c,R⟩
   have hA : volume A.tail≤ volume A := by cases A <;> simp [volume_cons] <;> omega
   have hB : volume B.tail≤ volume B := by cases B <;> simp [volume_cons] <;> omega
   have hsum := volume_bool (xor (xor (A.headD false) (B.headD false)) c)
   have hcarry := volume_bool ((!A.headD false && (B.headD false || c))||(B.headD false && c))
   have hc : 1≤ volume c := volume_pos c
   simp only [step,volume_pair,volume_cons]
   omega

end EdgeSublinearMWIS.Main.BinarySubtract
end

-- Solutions.SubtractPolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.BinarySubtract
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem raw_polynomial : PolyBound rawRealizer := by
   have hpre := polynomial_pair RawStack.lengthBound_polynomial (linear_polynomial BinaryAdder.initial_linear)
   have hiter := polynomial_iterate (linear_polynomial step_linear) 6 step_volume
   have hpost := polynomial_pair (linear_polynomial BinaryAdder.bitC_linear)
     (polynomial_comp (linear_polynomial BinaryAdder.revOutput_linear) RawStack.reverse_polynomial)
   unfold rawRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp hpre hiter) hpost

 theorem less_polynomial : PolyBound lessRealizer :=
   polynomial_comp raw_polynomial (linear_polynomial linear_fst)

 theorem difference_polynomial : PolyBound differenceRealizer := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : List Bool => ([] : List Bool))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   unfold differenceRealizer
   apply polynomial_congr
   exact polynomial_comp raw_polynomial (polynomial_choose (linear_polynomial hn) RawStack.trim_polynomial)

end EdgeSublinearMWIS.Main.BinarySubtract
end

-- Solutions.BinaryDivisionRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
abbrev DivisionState := List Bool×(List Bool×List Bool)
abbrev DivisionInput := Bool×DivisionState

 def divisionDen : Realizer (fun x : DivisionInput => x.2.1) := Realizer.snd.comp Realizer.fst
 def divisionOldR : Realizer (fun x : DivisionInput => x.2.2.1) := (Realizer.snd.comp Realizer.snd).comp Realizer.fst
 def divisionOldQ : Realizer (fun x : DivisionInput => x.2.2.2) := (Realizer.snd.comp Realizer.snd).comp Realizer.snd
 def divisionNewR : Realizer (fun x : DivisionInput => x.1::x.2.2.1) :=
   (Realizer.fst.pair divisionOldR).comp Realizer.cons
 def divisionPair : Realizer (fun x : DivisionInput => (x.1::x.2.2.1,x.2.1)) := divisionNewR.pair divisionDen
 def divisionTest : Realizer (fun x : DivisionInput => BinarySubtract.less (x.1::x.2.2.1) x.2.1) :=
   divisionPair.comp BinarySubtract.lessRealizer
 def divisionRemainder : Realizer (fun x : DivisionInput =>
     if BinarySubtract.less (x.1::x.2.2.1) x.2.1 then trim (x.1::x.2.2.1) else BinarySubtract.difference (x.1::x.2.2.1) x.2.1) :=
   (divisionTest.pair divisionPair).comp ((Realizer.fst.comp trimRealizer).choose BinarySubtract.differenceRealizer)
 def divisionQ : Realizer (fun x : DivisionInput => (!BinarySubtract.less (x.1::x.2.2.1) x.2.1)::x.2.2.2) :=
   ((divisionTest.comp Realizer.not).pair divisionOldQ).comp Realizer.cons
 def divideStepRealizer : Realizer divideStep :=
   (divisionDen.pair (divisionRemainder.pair divisionQ)).congr (fun x => by
     rcases x with ⟨b,B,R,Q⟩
     cases h : BinarySubtract.less (b::R) B <;> simp [divideStep,h])
 def divideInitial : Realizer (fun x : List Bool×List Bool => (x.1.reverse,(x.2,(([] : List Bool),([] : List Bool))))) :=
   (Realizer.fst.comp Realizer.reverse).pair (Realizer.snd.pair (Realizer.nil.pair Realizer.nil))
 def divisionFinish : Realizer (fun x : DivisionState => (trim x.2.2,trim x.2.1)) :=
   ((Realizer.snd.comp Realizer.snd).comp trimRealizer).pair ((Realizer.snd.comp Realizer.fst).comp trimRealizer)
 def divideRealizer : Realizer (fun x : List Bool×List Bool => divide x.1 x.2) :=
   ((divideInitial.comp divideStepRealizer.fold).comp divisionFinish).congr (fun _ => rfl)

 theorem divideStep_polynomial : PolyBound divideStepRealizer := by
   have hden : PolyBound divisionDen := linear_polynomial (linear_comp linear_snd linear_fst)
   have hr : PolyBound divisionOldR := linear_polynomial (linear_comp (linear_comp linear_snd linear_snd) linear_fst)
   have hq : PolyBound divisionOldQ := linear_polynomial (linear_comp (linear_comp linear_snd linear_snd) linear_snd)
   have hnew : PolyBound divisionNewR := polynomial_comp (polynomial_pair (linear_polynomial linear_fst) hr) (linear_polynomial linear_cons)
   have hp : PolyBound divisionPair := polynomial_pair hnew hden
   have ht : PolyBound divisionTest := polynomial_comp hp BinarySubtract.less_polynomial
   have hrem : PolyBound divisionRemainder := polynomial_comp (polynomial_pair ht hp)
     (polynomial_choose (polynomial_comp (linear_polynomial linear_fst) trim_polynomial) BinarySubtract.difference_polynomial)
   have hQ : PolyBound divisionQ := polynomial_comp (polynomial_pair (polynomial_comp ht (linear_polynomial linear_not)) hq) (linear_polynomial linear_cons)
   unfold divideStepRealizer
   apply polynomial_congr
   exact polynomial_pair hden (polynomial_pair hrem hQ)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FoldPrefixBound
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

 theorem fold_prefix_bound {f : α×β → β} (R : Realizer f) (xs : List α) (b : β) (T V : ℕ)
    (hvol : ∀j,j≤ xs.length → volume ((xs.take j).foldl (fun b a => f (a,b)) b)≤ V)
    (htime : ∀j (hj : j< xs.length),R.time (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)≤ T) :
    Realizer.foldTime R b xs≤ xs.length*(T+20*(volume xs+2*V+1))+1 := by
   induction xs generalizing b with
   | nil => simp [Realizer.foldTime]
   | cons a xs ih =>
     have hb : volume b≤ V := by simpa using hvol 0 (by simp)
     have hb' : volume (f (a,b))≤ V := by simpa using hvol 1 (by simp)
     have ht : R.time (a,b)≤ T := by
       have ht0 := htime 0 (by simp)
       change R.time (a,b)≤ T at ht0
       exact ht0
     have hvol' : ∀j,j≤ xs.length → volume ((xs.take j).foldl (fun b a => f (a,b)) (f (a,b)))≤ V := by
       intro j hj
       have hh := hvol (j+1) (by simp only [List.length_cons]; omega)
       simpa only [List.take_succ_cons,List.foldl_cons] using hh
     have htime' : ∀j (hj : j< xs.length),R.time (xs[j],(xs.take j).foldl (fun b a => f (a,b)) (f (a,b)))≤ T := by
       intro j hj
       have hh := htime (j+1) (by simp only [List.length_cons]; omega)
       simpa only [List.take_succ_cons,List.foldl_cons,List.getElem_cons_succ] using hh
     have hh := ih (f (a,b)) hvol' htime'
     simp only [Realizer.foldTime,List.length_cons] at hh ⊢
     have hvolxs : volume xs≤ volume (a::xs) := by simp only [volume_cons]; omega
     have hbound : xs.length*(T+20*(volume xs+2*V+1))≤ xs.length*(T+20*(volume (a::xs)+2*V+1)) :=
       Nat.mul_le_mul_left _ (by omega)
     nlinarith only [hh,ht,hb,hb',hbound]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.BitFoldEnvelope
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {β : Type} [Coding β]

 theorem bit_fold_envelope {f : Bool×β → β} (R : Realizer f) (C q : ℕ)
    (htime : ∀x,R.time x≤ C*(volume x+1)^q)
    (xs : List Bool) (acc : β) (z : ℕ) (hz : 1≤ z) (hlen : xs.length≤ z)
    (hxs : volume xs≤5*z)
    (hvol : ∀j,j≤ xs.length → volume ((xs.take j).foldl (fun b a => f (a,b)) acc)≤12*z) :
    R.fold.time (xs,acc)≤(C*17^q+2000)*z^(q+2) := by
   have hT (j : ℕ) (hj : j< xs.length) : R.time (xs[j],(xs.take j).foldl (fun b a => f (a,b)) acc)≤ C*17^q*z^q := by
     have hh := htime (xs[j],(xs.take j).foldl (fun b a => f (a,b)) acc)
     have hb := volume_bool xs[j]
     have hs := hvol j hj.le
     have hv : volume (xs[j],(xs.take j).foldl (fun b a => f (a,b)) acc)+1≤17*z := by simp only [volume_pair]; omega
     have ht := hh.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hv q))
     simpa only [mul_pow,Nat.mul_assoc] using ht
   have hf := fold_prefix_bound R xs acc (C*17^q*z^q) (12*z) hvol hT
   have hq1 : z^(q+1)≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hq2 : z^2≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hzgrow : z≤ z^2 := by nlinarith
   have hmul : xs.length*(C*17^q*z^q+20*(volume xs+2*(12*z)+1))≤ z*(C*17^q*z^q+600*z) := Nat.mul_le_mul hlen (by omega)
   have hqprod : z*(C*17^q*z^q)=C*17^q*z^(q+1) := by rw [pow_succ]; ring
   have hf' : Realizer.foldTime R acc xs≤(C*17^q+1000)*z^(q+2) := by
     have ht := Nat.mul_le_mul_left (C*17^q) hq1
     have hc := Nat.mul_le_mul_left 1000 hq2
     simp only [Nat.mul_add,hqprod] at hmul
     nlinarith only [hf,hmul,ht,hc,hzgrow,hz]
   have hacc : volume acc≤12*z := by simpa only [List.take_zero,List.foldl_nil] using hvol 0 (by omega)
   have hpow : z≤ z^(q+2) := hzgrow.trans hq2
   rw [Realizer.time_fold]
   simp only [volume_pair]
   nlinarith only [hf',hxs,hacc,hpow,hz]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.DivisionRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem division_prefix_volume (A B : List Bool) (j : ℕ) (hj : j≤ A.length) :
     volume ((A.reverse.take j).foldl (fun s b => divideStep (b,s)) (B,([],[])))≤12*(A.length+B.length+1) := by
   let L := A.reverse.take j
   let s := L.foldl (fun s b => divideStep (b,s)) (B,([],[]))
   have hb := divide_fold_base L B [] []
   have hr := divide_fold_rlength L B [] []
   have hq := divide_fold_qlength L B [] []
   have hlen : L.length≤ A.length := by dsimp [L]; simp only [List.length_take,List.length_reverse]; omega
   change s.1=B at hb
   change s.2.1.length≤[].length+L.length at hr
   change s.2.2.length=[].length+L.length at hq
   simp only [List.length_nil,Nat.zero_add] at hr hq
   have hvB := BinaryAdder.volume_bits s.1
   have hvR := BinaryAdder.volume_bits s.2.1
   have hvQ := BinaryAdder.volume_bits s.2.2
   rw [hb] at hvB
   change volume (s.1,(s.2.1,s.2.2))≤ _
   simp only [volume_pair]
   rw [hb]
   omega

 theorem division_fold_time : ∃ C q : ℕ,0< C ∧ ∀ A B : List Bool,
     divideStepRealizer.fold.time (A.reverse,(B,([],[])))≤ C*(A.length+B.length+1)^q := by
   obtain ⟨C,q,hC,hR⟩ := divideStep_polynomial
   refine ⟨C*17^q+2000,q+2,by positivity,?_⟩
   intro A B
   apply bit_fold_envelope divideStepRealizer C q (fun x => (hR x).1)
   · omega
   · simp only [List.length_reverse]; omega
   · rw [volume_reverse]
     have hA := BinaryAdder.volume_bits A
     omega
   · intro j hj
     exact division_prefix_volume A B j (by simpa only [List.length_reverse] using hj)

 theorem divideInitial_polynomial : PolyBound divideInitial := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : List Bool×List Bool => ([] : List Bool))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   exact polynomial_pair (polynomial_comp (linear_polynomial linear_fst) reverse_polynomial)
     (polynomial_pair (linear_polynomial linear_snd) (polynomial_pair (linear_polynomial hn) (linear_polynomial hn)))

 theorem divisionFinish_polynomial : PolyBound divisionFinish :=
   polynomial_pair (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_snd)) trim_polynomial)
     (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_fst)) trim_polynomial)

 theorem divide_time : ∃ C q : ℕ,0< C ∧ ∀ A B : List Bool,
     divideRealizer.time (A,B)≤ C*(A.length+B.length+1)^q := by
   obtain ⟨C,q,hC,hfold⟩ := division_fold_time
   obtain ⟨I,p,hI,hinit⟩ := divideInitial_polynomial
   obtain ⟨D,r,hD,hpost⟩ := divisionFinish_polynomial
   let e := p+q+r+2
   refine ⟨I*5^p+C+D*13^r+1000,e,by positivity,?_⟩
   intro A B
   let z := A.length+B.length+1
   let initial : List Bool×DivisionState := (A.reverse,(B,([],[])))
   let final := A.reverse.foldl (fun s b => divideStep (b,s)) (B,([],[]))
   have hz : 1≤ z := by dsimp [z]; omega
   have hp : z^p≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hq : z^q≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hr : z^r≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hze : z≤ z^e := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by dsimp [e]; omega : 1≤ e)
   have hA := BinaryAdder.volume_bits A
   have hB := BinaryAdder.volume_bits B
   have hvx : volume (A,B)+1≤5*z := by simp only [volume_pair]; dsimp [z]; omega
   have hvi : volume initial≤7*z := by dsimp [initial]; simp only [volume_pair,volume_nil,volume_reverse]; dsimp [z]; omega
   have hvf : volume final≤12*z := by
     have hh := division_prefix_volume A B A.length le_rfl
     rw [← List.length_reverse (as := A), List.take_length] at hh
     simpa only [List.length_reverse] using hh
   have hi : divideInitial.time (A,B)≤ I*5^p*z^e := by
     have hh := ((hinit (A,B)).1).trans (Nat.mul_le_mul_left I (Nat.pow_le_pow_left hvx p))
     simp only [mul_pow] at hh
     exact hh.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (I*5^p) hp)
   have hf : divideStepRealizer.fold.time initial≤ C*z^e := (hfold A B).trans (Nat.mul_le_mul_left C hq)
   have ho : divisionFinish.time final≤ D*13^r*z^e := by
     have hh := ((hpost final).1).trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left (show volume final+1≤13*z by omega) r))
     simp only [mul_pow] at hh
     exact hh.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*13^r) hr)
   have hcopy : 10*(volume initial+1)+10*(volume final+1)≤1000*z^e := by omega
   have heq : divideRealizer.time (A,B)=divideInitial.time (A,B)+divideStepRealizer.fold.time initial+
       10*(volume initial+1)+divisionFinish.time final+10*(volume final+1) := by
     dsimp only [divideRealizer,divide]
     simp only [Realizer.time_congr,Realizer.time_comp,Function.comp_apply]
     rfl
   rw [heq]
   change _≤(I*5^p+C+D*13^r+1000)*z^e
   nlinarith only [hi,hf,ho,hcopy]

 theorem divide_lengths (A B : List Bool) :
     (divide A B).1.length≤ A.length ∧ (divide A B).2.length≤ A.length := by
   have hr := divide_fold_rlength A.reverse B [] []
   have hq := divide_fold_qlength A.reverse B [] []
   simp only [List.length_nil,Nat.zero_add,List.length_reverse] at hr hq
   exact ⟨(trim_length _).trans hq.le,(trim_length _).trans hr⟩

 theorem divide_polynomial : PolyBound divideRealizer := by
   obtain ⟨C,q,hC,hT⟩ := divide_time
   refine ⟨C+12,q+1,by omega,?_⟩
   rintro ⟨A,B⟩
   let z := volume (A,B)+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hA := bits_length_volume A
   have hB := bits_length_volume B
   have hbase : A.length+B.length+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hp : (A.length+B.length+1)^q≤ z^(q+1) := (Nat.pow_le_pow_left hbase q).trans (Nat.pow_le_pow_right hz (by omega))
   have ht := (hT A B).trans (Nat.mul_le_mul_left C hp)
   have hvQ := BinaryAdder.volume_bits (divide A B).1
   have hvR := BinaryAdder.volume_bits (divide A B).2
   have hlen := divide_lengths A B
   have hpow : z≤ z^(q+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+1)
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume ((divide A B).1,(divide A B).2)≤ _
     simp only [volume_pair]
     have hv : volume (divide A B).1+volume (divide A B).2+1≤12*z^(q+1) := by omega
     simpa only [z,volume_pair] using hv.trans (Nat.mul_le_mul_right (z^(q+1)) (show 12≤ C+12 from Nat.le_add_left _ _))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialIterateBounded
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

 theorem polynomial_iterate_bounded {f : α → α} {R : Realizer f} (hR : PolyBound R) (E : ℕ)
    (hg : ∀x j,volume (f^[j] x)≤ E*(volume x+1)) : PolyBound R.iterate := by
   obtain ⟨C,q,hC,hR⟩ := hR
   let F := C*(E+1)^q
   refine ⟨100000*(F+E+10),q+2,by dsimp [F]; positivity,?_⟩
   rintro ⟨n,a⟩
   let z := volume (n,a)+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hn : n+1≤ z := by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have ha : volume a+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hV (j : ℕ) (_hj : j≤ n) : volume (f^[j] a)≤ E*z :=
     (hg a j).trans (Nat.mul_le_mul_left E ha)
   have hT (j : ℕ) (hj : j< n) : R.time (f^[j] a)≤ F*z^q := by
     have hh := (hR (f^[j] a)).1
     have hv := hV j hj.le
     have hbase : volume (f^[j] a)+1≤(E+1)*z := by nlinarith
     have ht := hh.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
     simpa only [F,mul_pow,Nat.mul_assoc] using ht
   have ht := Realizer.time_iterate_le R n a (F*z^q) (E*z) hT hV
   have hq : z^(q+1)≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hq2 : z^2≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hze : z≤ z^(q+2) := (show z≤ z^2 by nlinarith).trans hq2
   constructor
   · change _≤100000*(F+E+10)*z^(q+2)
     have hmul : (n+1)*(F*z^q+E*z+n+1)≤ z*(F*z^q+(E+3)*z) := Nat.mul_le_mul hn (by nlinarith)
     have hmul' := Nat.mul_le_mul_left 10000 hmul
     have hp1 := Nat.mul_le_mul_left (10000*F) hq
     have hp2 := Nat.mul_le_mul_left (10000*(E+3)) hq2
     have hs : R.iterate.time (n,a)≤(10000*F+10000*(E+3))*z^(q+2) := by
       rw [pow_succ] at hp1
       nlinarith only [ht,hmul',hp1,hp2]
     exact hs.trans (Nat.mul_le_mul_right _ (iterate_coefficient F E))
   · change volume (f^[n] a)≤100000*(F+E+10)*z^(q+2)
     exact (hV n le_rfl).trans ((Nat.mul_le_mul_left E hze).trans
       (Nat.mul_le_mul_right _ (by have := iterate_output_coefficient F E; omega)))

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.BinaryGcdRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack.BinaryGcd
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def stepRealizer : Realizer step :=
   (((Realizer.snd.comp nonemptyBits).pair Realizer.id).comp
     ((Realizer.snd.pair (divideRealizer.comp Realizer.snd)).choose Realizer.id)).congr (fun s => by
       rcases s with ⟨A,B⟩
       cases B <;> simp [step,nonemptyBits])

 theorem step_polynomial : PolyBound stepRealizer := by
   unfold stepRealizer
   apply polynomial_congr
   exact polynomial_comp
     (polynomial_pair (linear_polynomial (linear_comp linear_snd nonempty_linear)) (linear_polynomial linear_id))
     (polynomial_choose (polynomial_pair (linear_polynomial linear_snd)
       (polynomial_comp divide_polynomial (linear_polynomial linear_snd))) (linear_polynomial linear_id))

 theorem iterate_volume (s : List Bool×List Bool) (t : ℕ) : volume (step^[t] s)≤5*(volume s+1) := by
   rcases s with ⟨A,B⟩
   have hlen := length_iter (A,B) t
   dsimp only at hlen
   have hA := bits_length_volume A
   have hB := bits_length_volume B
   have hvA := BinaryAdder.volume_bits (step^[t] (A,B)).1
   have hvB := BinaryAdder.volume_bits (step^[t] (A,B)).2
   change volume ((step^[t] (A,B)).1,(step^[t] (A,B)).2)≤ _
   simp only [volume_pair]
   omega

 theorem iterate_polynomial : PolyBound stepRealizer.iterate :=
   polynomial_iterate_bounded step_polynomial 5 iterate_volume

 def iterationCount : Realizer (fun s : List Bool×List Bool => 2*s.2.length) :=
   ((Realizer.snd.comp BinaryAdder.wordLength).pair (Realizer.snd.comp BinaryAdder.wordLength)).comp Realizer.add
     |>.congr (fun s => by dsimp only [Function.comp_apply]; omega)
 def initialRealizer : Realizer (fun s : List Bool×List Bool => (trim s.1,trim s.2)) :=
   (Realizer.fst.comp trimRealizer).pair (Realizer.snd.comp trimRealizer)
 def runRealizer : Realizer (fun s : List Bool×List Bool => run s.1 s.2) :=
   ((iterationCount.pair initialRealizer).comp stepRealizer.iterate).congr (fun _ => rfl)
 def gcdRealizer : Realizer (fun s : List Bool×List Bool => gcd s.1 s.2) := runRealizer.comp Realizer.fst

 theorem wordLength_polynomial : PolyBound BinaryAdder.wordLength := by
   refine ⟨1000002,2,by omega,?_⟩
   intro A
   have ht := BinaryAdder.wordLength_time A
   have hlen := bits_length_volume A
   have hp := Nat.pow_le_pow_left (show A.length+1≤ volume A+1 by omega) 2
   have hz : 1≤ volume A+1 := by omega
   have hpow : volume A+1≤(volume A+1)^2 := by nlinarith
   constructor
   · exact ht.trans ((Nat.mul_le_mul_left 1000000 hp).trans (Nat.mul_le_mul_right _ (by omega)))
   · simp only [volume_nat]
     omega

 theorem nat_add_polynomial : PolyBound Realizer.add := by
   refine ⟨10000001,2,by omega,?_⟩
   rintro ⟨a,b⟩
   have ht := Realizer.time_add_le a b
   have hbase : a+b+1≤ volume (a,b)+1 := by simp only [volume_pair,volume_nat]; omega
   have hp := Nat.pow_le_pow_left hbase 2
   have hv : volume (a+b)≤2*(volume (a,b)+1)^2 := by
     simp only [volume_nat,volume_pair]
     nlinarith
   constructor
   · exact ht.trans ((Nat.mul_le_mul_left 10000000 hp).trans (Nat.mul_le_mul_right _ (by omega)))
   · exact hv.trans (Nat.mul_le_mul_right _ (by omega))

 theorem iterationCount_polynomial : PolyBound iterationCount := by
   unfold iterationCount
   apply polynomial_congr
   exact polynomial_comp
     (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) wordLength_polynomial)
       (polynomial_comp (linear_polynomial linear_snd) wordLength_polynomial))
     nat_add_polynomial

 theorem initial_polynomial : PolyBound initialRealizer :=
   polynomial_pair (polynomial_comp (linear_polynomial linear_fst) trim_polynomial)
     (polynomial_comp (linear_polynomial linear_snd) trim_polynomial)

 theorem gcd_polynomial : PolyBound gcdRealizer := by
   apply polynomial_comp _ (linear_polynomial linear_fst)
   unfold runRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair iterationCount_polynomial initial_polynomial) iterate_polynomial

end EdgeSublinearMWIS.Main.RawStack.BinaryGcd
end

-- Solutions.BinaryRational
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def normalizeWords (A B : List Bool) : List Bool×List Bool :=
   let D := BinaryGcd.gcd A B
   ((divide A D).1,(divide B D).1)

 def gcdArguments : Realizer (fun x : List Bool×List Bool => (x,BinaryGcd.gcd x.1 x.2)) :=
   Realizer.id.pair BinaryGcd.gcdRealizer
 def normalizeFirst : Realizer (fun x : (List Bool×List Bool)×List Bool => (divide x.1.1 x.2).1) :=
   (((Realizer.fst.comp Realizer.fst).pair Realizer.snd).comp divideRealizer).comp Realizer.fst
 def normalizeSecond : Realizer (fun x : (List Bool×List Bool)×List Bool => (divide x.1.2 x.2).1) :=
   (((Realizer.fst.comp Realizer.snd).pair Realizer.snd).comp divideRealizer).comp Realizer.fst
 def normalizeWordsRealizer : Realizer (fun x : List Bool×List Bool => normalizeWords x.1 x.2) :=
   (gcdArguments.comp (normalizeFirst.pair normalizeSecond)).congr (fun _ => rfl)

 theorem normalizeWords_polynomial : PolyBound normalizeWordsRealizer := by
   have h1 : PolyBound normalizeFirst := polynomial_comp
     (polynomial_comp (polynomial_pair (linear_polynomial (linear_comp linear_fst linear_fst)) (linear_polynomial linear_snd)) divide_polynomial)
     (linear_polynomial linear_fst)
   have h2 : PolyBound normalizeSecond := polynomial_comp
     (polynomial_comp (polynomial_pair (linear_polynomial (linear_comp linear_fst linear_snd)) (linear_polynomial linear_snd)) divide_polynomial)
     (linear_polynomial linear_fst)
   unfold normalizeWordsRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (linear_polynomial linear_id) BinaryGcd.gcd_polynomial) (polynomial_pair h1 h2)

 theorem normalizeWords_values (A B : List Bool) (hB : 0< value B) :
     value (normalizeWords A B).1=value A/(value A).gcd (value B) ∧
     value (normalizeWords A B).2=value B/(value A).gcd (value B) := by
   have hD : 0< value (BinaryGcd.gcd A B) := by rw [BinaryGcd.gcd_value]; exact Nat.gcd_pos_of_pos_right _ hB
   exact ⟨(divide_value A _ hD).1.trans (by rw [BinaryGcd.gcd_value]),
     (divide_value B _ hD).1.trans (by rw [BinaryGcd.gcd_value])⟩

 theorem normalizeWords_canonical (A B : List Bool) :
     trim (normalizeWords A B).1=(normalizeWords A B).1 ∧ trim (normalizeWords A B).2=(normalizeWords A B).2 :=
   ⟨trim_idem _,trim_idem _⟩

 def signedValue (b : Bool) (A : List Bool) : ℤ := if b then -(value A : ℤ) else value A

 theorem signedValue_natAbs (b : Bool) (A : List Bool) : (signedValue b A).natAbs=value A := by
   cases b <;> simp [signedValue]

 theorem normalized_rat_num_den (z : ℤ) (d : ℕ) (hd : 0< d) :
     ((z : ℚ)/d).num.natAbs=z.natAbs/(z.natAbs.gcd d) ∧
     ((z : ℚ)/d).den=d/(z.natAbs.gcd d) := by
   have he : (z : ℚ)/(d : ℚ)=Rat.normalize z d (by omega) := by
     rw [Rat.normalize_eq_mkRat,Rat.mkRat_eq_divInt,Rat.divInt_eq_div]
     norm_cast
   rw [he,Rat.num_normalize,Rat.den_normalize]
   constructor
   · rw [Int.natAbs_ediv_of_dvd]
     · simp
     · exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
   · rfl

 theorem normalizeWords_rat (b : Bool) (A B : List Bool) (hB : 0< value B) :
     (normalizeWords A B).1=natBits (((signedValue b A : ℚ)/value B).num.natAbs) ∧
     (normalizeWords A B).2=natBits (((signedValue b A : ℚ)/value B).den) := by
   have hv := normalizeWords_values A B hB
   have hr := normalized_rat_num_den (signedValue b A) (value B) hB
   rw [signedValue_natAbs] at hr
   have hc := normalizeWords_canonical A B
   constructor
   · rw [canonical_eq_natBits _ hc.1,hv.1,← hr.1]
   · rw [canonical_eq_natBits _ hc.2,hv.2,← hr.2]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryListCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def appendBits : Realizer (fun x : List Bool×List Bool => x.1++x.2) :=
   ((((Realizer.fst.comp Realizer.reverse).pair Realizer.snd).comp Realizer.cons.fold)).congr
     (fun x => by simp only [Function.comp_apply,Realizer.fold_cons_eq,List.reverse_reverse])

 theorem cons_fold_polynomial : PolyBound (Realizer.cons : Realizer (fun x : Bool×List Bool => x.1::x.2)).fold := by
   refine ⟨100000,3,by omega,?_⟩
   rintro ⟨A,B⟩
   let z := A.length+B.length+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hvol : ∀j,j≤ A.length → volume ((A.take j).foldl (fun s b => b::s) B)≤12*z := by
     intro j hj
     rw [Realizer.fold_cons_eq]
     have hv := BinaryAdder.volume_bits ((A.take j).reverse++B)
     simp only [List.length_append,List.length_reverse,List.length_take] at hv
     dsimp [z]
     omega
   have ht := bit_fold_envelope (Realizer.cons : Realizer (fun x : Bool×List Bool => x.1::x.2)) 3 1
     (fun x => by change volume x+2≤3*(volume x+1)^1; simp only [pow_one]; omega) A B z hz (by dsimp [z]; omega)
     (by have hh := BinaryAdder.volume_bits A; dsimp [z]; omega) hvol
   have hbase : z≤ volume (A,B)+1 := by
     have hA := bits_length_volume A
     have hB := bits_length_volume B
     dsimp [z]; simp only [volume_pair]; omega
   have hp := Nat.pow_le_pow_left hbase 3
   constructor
   · have he : 3*17^1+2000≤100000 := by norm_num
     exact ht.trans ((Nat.mul_le_mul_left _ hp).trans (Nat.mul_le_mul_right _ he))
   · change volume (A.foldl (fun s b => b::s) B)≤ _
     have hv := hvol A.length le_rfl
     rw [List.take_length] at hv
     have hh : z≤(volume (A,B)+1)^3 := hbase.trans (by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤ volume (A,B)+1) (by omega : 1≤3))
     have hs : volume (A.foldl (fun s b => b::s) B)≤12*(volume (A,B)+1)^3 := by omega
     exact hs.trans (Nat.mul_le_mul_right _ (by omega))

 theorem appendBits_polynomial : PolyBound appendBits := by
   unfold appendBits
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) reverse_polynomial)
     (linear_polynomial linear_snd)) cons_fold_polynomial

 def prependTrue : Realizer (fun L : List Bool => true::L) := ((Realizer.constant true).pair Realizer.id).comp Realizer.cons
 theorem prependTrue_linear : Linear prependTrue := by
   have ht : Linear (Realizer.constant true : Realizer (fun _ : List Bool => true)) := linear_bool _ 2000 (fun L => by change (2*3+1)*(20*volume L+50*3+50)≤ _; omega)
   exact linear_comp (linear_pair ht linear_id) linear_cons
 def replicateTrue : Realizer (fun n : ℕ => List.replicate n true) :=
   ((Realizer.id.pair Realizer.nil).comp prependTrue.iterate).congr (fun n => by
     change (fun L : List Bool => true::L)^[n] []=List.replicate n true
     induction n with
     | zero => rfl
     | succ n ih => rw [Function.iterate_succ_apply',ih,List.replicate_succ])
 theorem replicateTrue_polynomial : PolyBound replicateTrue := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : ℕ => ([] : List Bool))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   unfold replicateTrue
   apply polynomial_congr
   apply polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial hn))
   exact polynomial_iterate (linear_polynomial prependTrue_linear) 4 (fun L => by simp only [volume_cons,volume_bool_true]; omega)

 def prefixBits (A : List Bool) : List Bool := List.replicate A.length true++false::A
 def falseCons : Realizer (fun L : List Bool => false::L) := (Realizer.false.pair Realizer.id).comp Realizer.cons
 theorem falseCons_linear : Linear falseCons := by
   have ht : Linear (Realizer.false : Realizer (fun _ : List Bool => false)) := linear_bool _ 3 (fun _ => by change 2≤ _; omega)
   exact linear_comp (linear_pair ht linear_id) linear_cons
 def prefixRealizer : Realizer prefixBits :=
   ((BinaryAdder.wordLength.comp replicateTrue).pair falseCons).comp appendBits
 theorem prefix_polynomial : PolyBound prefixRealizer :=
   polynomial_comp (polynomial_pair (polynomial_comp BinaryGcd.wordLength_polynomial replicateTrue_polynomial)
     (linear_polynomial falseCons_linear)) appendBits_polynomial

 theorem prefix_natBits (n : ℕ) : prefixBits (natBits n)=encodeNat n := by
   simp only [prefixBits,encodeNat,List.append_assoc,List.singleton_append]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SerializeRational
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev SignedWords := Bool×(List Bool×List Bool)
 def rationalSign (s : SignedWords) : Bool := s.1 && !(trim s.2.1).isEmpty
 def rationalBits (s : SignedWords) : List Bool :=
   let N := normalizeWords s.2.1 s.2.2
   rationalSign s :: (prefixBits N.1++prefixBits N.2)
 def signRealizer : Realizer rationalSign :=
   (Realizer.fst.pair (((Realizer.snd.comp Realizer.fst).comp trimRealizer).comp nonemptyBits)).comp Realizer.and
 def normalizedRealizer : Realizer (fun s : SignedWords => normalizeWords s.2.1 s.2.2) := Realizer.snd.comp normalizeWordsRealizer
 def unsignedBitsRealizer : Realizer (fun s : List Bool×List Bool => prefixBits s.1++prefixBits s.2) :=
   ((Realizer.fst.comp prefixRealizer).pair (Realizer.snd.comp prefixRealizer)).comp appendBits
 def rationalBitsRealizer : Realizer rationalBits :=
   (signRealizer.pair (normalizedRealizer.comp unsignedBitsRealizer)).comp Realizer.cons
 theorem rationalBits_polynomial : PolyBound rationalBitsRealizer := by
   have hs : PolyBound signRealizer := polynomial_comp
     (polynomial_pair (linear_polynomial linear_fst)
       (polynomial_comp (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_fst)) trim_polynomial)
         (linear_polynomial nonempty_linear))) (linear_polynomial linear_and)
   have hn : PolyBound normalizedRealizer := polynomial_comp (linear_polynomial linear_snd) normalizeWords_polynomial
   have hu : PolyBound unsignedBitsRealizer := polynomial_comp
     (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) prefix_polynomial)
       (polynomial_comp (linear_polynomial linear_snd) prefix_polynomial)) appendBits_polynomial
   exact polynomial_comp (polynomial_pair hs (polynomial_comp hn hu)) (linear_polynomial linear_cons)

 theorem rational_sign (b : Bool) (A B : List Bool) (hB : 0< value B) :
     rationalSign (b,(A,B))=decide ((((signedValue b A : ℚ)/value B).num)<0) := by
   have hv : (trim A).isEmpty=false ↔ 0< value A := by
     constructor
     · intro h
       have hn : trim A≠[] := by intro he; simp [he] at h
       have hh := BinaryGcd.value_positive (trim A) (trim_idem A) hn
       rwa [trim_value] at hh
     · intro h
       cases he : trim A with
       | nil => have hh := trim_value A; rw [he] at hh; simp [value] at hh; omega
       | cons a L => rfl
   have hneg : (((signedValue b A : ℚ)/value B).num<0) ↔ b=true ∧ 0< value A := by
     have hp : (0 : ℚ)< value B := by exact_mod_cast hB
     rw [Rat.num_neg,div_neg_iff]
     cases b <;> simp [signedValue,hp,not_lt_of_gt hp]
   cases b <;> cases he : (trim A).isEmpty <;> simp_all [rationalSign]

 theorem rationalBits_correct (b : Bool) (A B : List Bool) (hB : 0< value B) :
     rationalBits (b,(A,B))=encodeRat ((signedValue b A : ℚ)/value B) := by
   have hn := normalizeWords_rat b A B hB
   dsimp only [rationalBits]
   rw [hn.1,hn.2,prefix_natBits,prefix_natBits,rational_sign b A B hB]
   rfl

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.WordParser
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def takeWordStep (s : List Bool×List Bool) : List Bool×List Bool :=
   if s.1.isEmpty then s else (s.1.tail,s.1.headD false::s.2)
 def takeWordStepRealizer : Realizer takeWordStep :=
   (((Realizer.fst.comp nonemptyBits).pair Realizer.id).comp
     (((Realizer.fst.comp BinaryAdder.tailBits).pair
       (((Realizer.fst.comp BinaryAdder.headBit).pair Realizer.snd).comp Realizer.cons)).choose Realizer.id)).congr (fun s => by
       rcases s with ⟨L,R⟩
       cases L <;> rfl)

 theorem takeWordStep_linear : Linear takeWordStepRealizer := by
   unfold takeWordStepRealizer
   apply linear_congr
   exact linear_comp (linear_pair (linear_comp linear_fst nonempty_linear) linear_id)
     (linear_choose (linear_pair (linear_comp linear_fst BinaryAdder.tailBits_linear)
       (linear_comp (linear_pair (linear_comp linear_fst BinaryAdder.headBit_linear) linear_snd) linear_cons)) linear_id)

 theorem takeWordStep_volume (s : List Bool×List Bool) : volume (takeWordStep s)≤ volume s := by
   rcases s with ⟨L,R⟩
   cases L with
   | nil => rfl
   | cons a L => simp only [takeWordStep,List.isEmpty_cons,Bool.false_eq_true,if_false,List.tail_cons,List.headD_cons,volume_pair,volume_cons]; omega

 theorem takeWordStep_iterate (L R : List Bool) (k : ℕ) :
     takeWordStep^[k] (L,R)=(L.drop k,(L.take k).reverse++R) := by
   induction k generalizing L R with
   | zero => simp
   | succ k ih =>
     rw [Function.iterate_succ_apply]
     cases L with
     | nil => simpa only [takeWordStep,List.isEmpty_nil,if_true,List.drop_nil,List.take_nil,List.reverse_nil,List.nil_append] using ih [] R
     | cons a L =>
       change takeWordStep^[k] (L,a::R)=_
       rw [ih,List.drop_succ_cons,List.take_succ_cons,List.reverse_cons]
       simp only [List.append_assoc,List.singleton_append]

 def splitWord (L : List Bool) (k : ℕ) : List Bool×List Bool := (L.take k,L.drop k)
 def splitWordRealizer : Realizer (fun x : List Bool×ℕ => splitWord x.1 x.2) :=
   (((Realizer.snd.pair (Realizer.fst.pair Realizer.nil)).comp takeWordStepRealizer.iterate).comp
     ((Realizer.snd.comp Realizer.reverse).pair Realizer.fst)).congr (fun x => by
       dsimp only [Function.comp_apply,splitWord]
       rw [takeWordStep_iterate]
       simp)

 theorem splitWord_polynomial : PolyBound splitWordRealizer := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : List Bool×ℕ => ([] : List Bool))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   have hi := polynomial_iterate (linear_polynomial takeWordStep_linear) 0 (fun x => by simpa only [Nat.add_zero] using takeWordStep_volume x)
   unfold splitWordRealizer
   apply polynomial_congr
   exact polynomial_comp
     (polynomial_comp (polynomial_pair (linear_polynomial linear_snd)
       (polynomial_pair (linear_polynomial linear_fst) (linear_polynomial hn))) hi)
     (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) reverse_polynomial) (linear_polynomial linear_fst))

 def readWord (L : List Bool) : List Bool×List Bool :=
   let k := (L.takeWhile id).length
   splitWord (L.drop (k+1)) k

 theorem readWord_prefix (A rest : List Bool) : readWord (prefixBits A++rest)=(A,rest) := by
   have hk : ((prefixBits A++rest).takeWhile id).length=A.length := by
     simp only [prefixBits,List.append_assoc]
     have h (n : ℕ) : ((List.replicate n true++false::(A++rest)).takeWhile id).length=n := by
       induction n with
       | zero => simp
       | succ n ih => simpa using congrArg Nat.succ ih
     exact h A.length
   dsimp only [readWord]
   rw [hk]
   have hd : (prefixBits A++rest).drop (A.length+1)=A++rest := by
     simp only [prefixBits,List.append_assoc]
     rw [← List.drop_drop,List.drop_left' (by simp)]
     rfl
   rw [hd]
   simp only [splitWord,List.take_left,List.drop_left]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ConstantCode
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

 theorem linear_constant (b : β) : Linear (Realizer.constant b : Realizer (fun _ : α => b)) := by
   let C := (2*volume b+1)*(50*volume b+70)+volume b+1
   refine linear_of _ C (by dsimp [C]; positivity) ?_ ?_
   · intro x
     change (2*volume b+1)*(20*volume x+50*volume b+50)≤ C*(volume x+1)
     have hb : 20*volume x+50*volume b+50≤(50*volume b+70)*(volume x+1) := by
       nlinarith [Nat.zero_le (volume b*volume x)]
     have hh := Nat.mul_le_mul_left (2*volume b+1) hb
     have hc : (2*volume b+1)*(50*volume b+70)≤ C := by dsimp [C]; omega
     exact hh.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (volume x+1) hc)
   · intro x
     change volume b≤ C*(volume x+1)
     have hc : volume b≤ C := by dsimp [C]; omega
     exact hc.trans (Nat.le_mul_of_pos_right _ (by omega))

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.LeadingParser
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def leadingStepRealizer : Realizer Binary.leadingStep := (Uniform.binaryLeadingStep (I:=Unit)).specialize ()
 theorem leadingStep_polynomial : PolyBound leadingStepRealizer := by
   obtain ⟨C,hC⟩ := Costs.leadingStepCost
   refine ⟨C+10,1,by omega,?_⟩
   rintro ⟨a,b,k⟩
   have ht := hC (a,(b,k))
   simp only [pow_one] at ht
   have hbase : k+2≤ volume (a,(b,k))+1 := by simp only [volume_pair,volume_nat]; omega
   have hv : volume (Binary.leadingStep (a,(b,k)))≤ volume (a,(b,k))+5 := by
     cases a <;> cases b <;> simp [Binary.leadingStep,volume_pair,volume_nat] <;> omega
   constructor
   · change _≤(C+10)*(volume (a,(b,k))+1)^1
     rw [pow_one]
     exact ht.trans ((Nat.mul_le_mul_left C hbase).trans (by nlinarith))
   · rw [pow_one]
     nlinarith

 theorem leading_fold_volume (L : List Bool) (b : Bool) (k : ℕ) :
     volume (L.foldl (fun s a => Binary.leadingStep (a,s)) (b,k))≤2*(k+L.length)+5 := by
   have hc := Binary.leading_fold L b k
   have hlen : Binary.leading L≤ L.length := by exact (List.takeWhile_sublist _).length_le
   have hb := volume_bool (L.foldl (fun s a => Binary.leadingStep (a,s)) (b,k)).1
   change volume ((L.foldl (fun s a => Binary.leadingStep (a,s)) (b,k)).1,
     (L.foldl (fun s a => Binary.leadingStep (a,s)) (b,k)).2)≤ _
   simp only [volume_pair,volume_nat,hc]
   split_ifs <;> omega

 theorem leading_fold_polynomial : PolyBound leadingStepRealizer.fold := by
   obtain ⟨C,q,hC,hR⟩ := leadingStep_polynomial
   refine ⟨C*17^q+2010,q+2,by positivity,?_⟩
   rintro ⟨L,b,k⟩
   let z := volume (L,(b,k))+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hL := bits_length_volume L
   have hbase : k+L.length+1≤ z := by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have hvol : ∀j,j≤ L.length → volume ((L.take j).foldl (fun s a => Binary.leadingStep (a,s)) (b,k))≤12*z := by
     intro j hj
     have hh := leading_fold_volume (L.take j) b k
     simp only [List.length_take] at hh
     omega
   have ht := bit_fold_envelope leadingStepRealizer C q (fun x => (hR x).1) L (b,k) z hz
     (by omega) (by dsimp [z]; simp only [volume_pair]; omega) hvol
   have hv := hvol L.length le_rfl
   rw [List.take_length] at hv
   have hp : z≤ z^(q+2) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+2)
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (L.foldl (fun s a => Binary.leadingStep (a,s)) (b,k))≤ _
     exact hv.trans ((Nat.mul_le_mul_left 12 hp).trans (Nat.mul_le_mul_right _ (by omega)))

 def leadingRealizer : Realizer (fun L : List Bool => (L.takeWhile id).length) :=
   (((Realizer.id.pair (Realizer.constant (true,0))).comp leadingStepRealizer.fold).comp Realizer.snd).congr
     (fun L => by simpa only [Function.comp_apply,id_eq,Nat.zero_add,ite_true,Binary.leading] using Binary.leading_fold L true 0)
 theorem leading_polynomial : PolyBound leadingRealizer := by
   unfold leadingRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_id)
     (linear_polynomial (linear_constant (true,0)))) leading_fold_polynomial) (linear_polynomial linear_snd)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ReadWordCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem succ_linear : Linear Realizer.succ := by
   refine linear_of _ 300 (by omega) (fun n => (Realizer.time_succ_le n).trans (by simp only [volume_nat]; omega)) ?_
   intro n
   simp only [volume_nat]
   omega

 def skipPrefixRealizer : Realizer (fun L : List Bool => L.drop ((L.takeWhile id).length+1)) :=
   (((Realizer.id.pair (leadingRealizer.comp Realizer.succ)).comp splitWordRealizer).comp Realizer.snd).congr (fun _ => rfl)
 def readWordRealizer : Realizer readWord :=
   ((skipPrefixRealizer.pair leadingRealizer).comp splitWordRealizer).congr (fun _ => rfl)
 theorem skipPrefix_polynomial : PolyBound skipPrefixRealizer := by
   unfold skipPrefixRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp
     (polynomial_pair (linear_polynomial linear_id) (polynomial_comp leading_polynomial (linear_polynomial succ_linear)))
     splitWord_polynomial) (linear_polynomial linear_snd)
 theorem readWord_polynomial : PolyBound readWordRealizer := by
   unfold readWordRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair skipPrefix_polynomial leading_polynomial) splitWord_polynomial

 theorem readWord_length (L : List Bool) : (readWord L).1.length+(readWord L).2.length≤ L.length := by
   dsimp only [readWord,splitWord]
   simp only [List.length_take,List.length_drop]
   omega

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ReadRational
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def readRational (L : List Bool) : SignedWords×List Bool :=
   let A := readWord L.tail
   let B := readWord A.2
   ((L.headD false,(A.1,B.1)),B.2)
 def numeratorRealizer : Realizer (fun L : List Bool => readWord L.tail) := BinaryAdder.tailBits.comp readWordRealizer
 def denominatorRealizer : Realizer (fun L : List Bool => readWord (readWord L.tail).2) :=
   (numeratorRealizer.comp Realizer.snd).comp readWordRealizer
 def readRationalRealizer : Realizer readRational :=
   (BinaryAdder.headBit.pair ((numeratorRealizer.comp Realizer.fst).pair (denominatorRealizer.comp Realizer.fst))).pair
     (denominatorRealizer.comp Realizer.snd)
 theorem readRational_polynomial : PolyBound readRationalRealizer := by
   have hn : PolyBound numeratorRealizer := polynomial_comp (linear_polynomial BinaryAdder.tailBits_linear) readWord_polynomial
   have hd : PolyBound denominatorRealizer := polynomial_comp (polynomial_comp hn (linear_polynomial linear_snd)) readWord_polynomial
   exact polynomial_pair (polynomial_pair (linear_polynomial BinaryAdder.headBit_linear)
     (polynomial_pair (polynomial_comp hn (linear_polynomial linear_fst)) (polynomial_comp hd (linear_polynomial linear_fst))))
     (polynomial_comp hd (linear_polynomial linear_snd))

 theorem readRational_prefix (b : Bool) (A B rest : List Bool) :
     readRational (b::(prefixBits A++prefixBits B++rest))=((b,(A,B)),rest) := by
   simp only [readRational,List.tail_cons,List.headD_cons,List.append_assoc,readWord_prefix]

 theorem readRational_code (q : RationalCode) (rest : List Bool) :
     readRational (q.bits++rest)=((decide (q.numerator<0),(natBits q.numerator.natAbs,natBits q.denominator)),rest) := by
   have he : q.bits++rest=decide (q.numerator<0)::
       (prefixBits (natBits q.numerator.natAbs)++prefixBits (natBits q.denominator)++rest) := by
     simp only [RationalCode.bits,encodeInt,prefix_natBits,List.singleton_append,List.cons_append,List.append_assoc,List.nil_append]
   rw [he,readRational_prefix]

 theorem signedValue_encode (z : ℤ) : signedValue (decide (z<0)) (natBits z.natAbs)=z := by
   cases z <;> simp [signedValue,value_natBits] <;> omega

 def normalizeInputRealizer : Realizer (fun L : List Bool => rationalBits (readRational L).1) :=
   (readRationalRealizer.comp Realizer.fst).comp rationalBitsRealizer
 theorem normalizeInput_polynomial : PolyBound normalizeInputRealizer :=
   polynomial_comp (polynomial_comp readRational_polynomial (linear_polynomial linear_fst)) rationalBits_polynomial

 theorem normalizeInput_correct (q : RationalCode) :
     rationalBits (readRational q.bits).1=encodeRat q.value := by
   have he := readRational_code q []
   simp only [List.append_nil] at he
   rw [he]
   have hB : 0< value (natBits q.denominator) := by rw [value_natBits]; exact q.positive
   rw [rationalBits_correct _ _ _ hB,signedValue_encode,value_natBits]
   rfl

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.CappedBinary
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def capStep (x : Bool×(ℕ×ℕ)) : ℕ×ℕ := (min x.2.2 (2*x.2.1+x.1.toNat),x.2.2)

 theorem capStep_second (b : Bool) (v c : ℕ) : (capStep (b,(v,c))).2=c := rfl
 theorem capStep_first (b : Bool) (v c : ℕ) : (capStep (b,(v,c))).1≤ c := Nat.min_le_left _ _
 theorem capFold_second (L : List Bool) (v c : ℕ) :
     (L.foldl (fun s b => capStep (b,s)) (v,c)).2=c := by
   induction L generalizing v with
   | nil => rfl
   | cons b L ih => exact ih _
 theorem capFold_bound (L : List Bool) (v c : ℕ) :
     (L.foldl (fun s b => capStep (b,s)) (v,c)).1≤ v+c := by
   cases L with
   | nil => simp
   | cons b L =>
     have h (L : List Bool) (v : ℕ) (hv : v≤ c) : (L.foldl (fun s b => capStep (b,s)) (v,c)).1≤ c := by
       induction L generalizing v with
       | nil => exact hv
       | cons b L ih => exact ih _ (capStep_first b v c)
     exact (h L _ (capStep_first b v c)).trans (by omega)

 theorem cap_min_step (b : Bool) (v c : ℕ) : min c (2*min c v+b.toNat)=min c (2*v+b.toNat) := by
   by_cases h : v≤ c
   · rw [Nat.min_eq_right h]
   · have hv : c≤ v := by omega
     rw [Nat.min_eq_left hv,Nat.min_eq_left (by omega),Nat.min_eq_left (by omega)]

 theorem capFold_value (L : List Bool) (v c : ℕ) (hv : v≤ c) :
     (L.foldl (fun s b => capStep (b,s)) (v,c)).1=min c (value L.reverse+2^L.length*v) := by
   induction L generalizing v with
   | nil => simp only [List.foldl_nil,List.reverse_nil,value,List.length_nil,pow_zero,Nat.one_mul,Nat.zero_add,Nat.min_eq_right hv]
   | cons b L ih =>
     rw [List.foldl_cons]
     change (L.foldl (fun s b => capStep (b,s)) (min c (2*v+b.toNat),c)).1=_
     rw [ih _ (Nat.min_le_left _ _),List.reverse_cons,BinaryAdder.value_append]
     simp only [value,List.length_reverse,List.length_cons,pow_succ,Nat.mul_zero,Nat.add_zero]
     have h (X P v c : ℕ) (hP : 1≤ P) : min c (X+P*min c v)=min c (X+P*v) := by
       by_cases hh : v≤ c
       · rw [Nat.min_eq_right hh]
       · have hc : c≤ v := by omega
         rw [Nat.min_eq_left hc,Nat.min_eq_left (by nlinarith),Nat.min_eq_left (by nlinarith)]
     rw [h _ _ _ _ (one_le_pow₀ (by omega : 1≤2))]
     congr 1
     ring

 def cappedValue (A : List Bool) (c : ℕ) : ℕ :=
   (A.reverse.foldl (fun s b => capStep (b,s)) (0,c)).1
 theorem cappedValue_eq (A : List Bool) (c : ℕ) : cappedValue A c=min c (value A) := by
   have hh := capFold_value A.reverse 0 c (by omega)
   simpa only [cappedValue,List.reverse_reverse,Nat.mul_zero,Nat.add_zero] using hh

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialProgram
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.TreeToTM2
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem realizer_poly_program {f : List Bool → List Bool} (R : Realizer f) (hR : PolyBound R) :
     ∃ (P : EdgeSublinearMWIS.Main.Program) (K q : ℕ),0< K ∧ 0< q ∧
       ∀ input, EdgeSublinearMWIS.Main.Runs P input (f input) (K*(input.length+1)^q) := by
   obtain ⟨C,q,hC,hR⟩ := hR
   obtain ⟨P,F,hF,hRuns⟩ := EdgeSublinearMWIS.Main.realizer_native_program f R
   refine ⟨P,F*(2*C*5^q+2),q+1,by positivity,by omega,?_⟩
   intro input
   have hRun := hRuns input
   apply NativeCompiler.runs_mono _ _ _ hRun
   let z := input.length+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hv := EdgeSublinearMWIS.Main.BinaryAdder.volume_bits input
   have hi : volume input+1≤5*z := by dsimp [z]; omega
   have hp := Nat.pow_le_pow_left hi q
   rw [mul_pow] at hp
   have hq : z^q≤ z^(q+1) := Nat.pow_le_pow_right hz (by omega)
   have hqp : (volume input+1)^q≤5^q*z^(q+1) := hp.trans (Nat.mul_le_mul_left _ hq)
   have ht := ((hR input).1).trans (Nat.mul_le_mul_left C hqp)
   have ho := ((hR input).2).trans (Nat.mul_le_mul_left C hqp)
   have hl := EdgeSublinearMWIS.Main.RawStack.bits_length_volume (f input)
   have hze : z≤ z^(q+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+1)
   change input.length+1≤ z^(q+1) at hze
   have hs : R.time input+input.length+(f input).length+1≤(2*C*5^q+2)*z^(q+1) := by
     nlinarith only [ht,ho,hl,hze]
   change F*(R.time input+input.length+(f input).length+1)≤ F*(2*C*5^q+2)*z^(q+1)
   simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left F hs

end EdgeSublinearMWIS.Main.TreeToTM2
end

-- Solutions.CappedBinaryRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def boolNat : Realizer Bool.toNat := Realizer.reinterpret _ (by intro b; cases b <;> rfl)
 theorem boolNat_linear : Linear boolNat := by
   refine linear_of _ 3 (by omega) (fun b => by change volume b+2≤ _; omega) ?_
   intro b
   cases b <;> decide
 theorem nat_le_polynomial : PolyBound Realizer.le := by
   refine ⟨1000000001,2,by omega,?_⟩
   rintro ⟨a,b⟩
   have ht := Realizer.time_le_le a b
   have hbase : a+b+1≤ volume (a,b)+1 := by simp only [volume_pair,volume_nat]; omega
   have hp := Nat.pow_le_pow_left hbase 2
   have hv := volume_bool (decide (a≤ b))
   have hz : 1≤(volume (a,b)+1)^2 := one_le_pow₀ (by omega)
   constructor
   · exact ht.trans ((Nat.mul_le_mul_left 1000000000 hp).trans (Nat.mul_le_mul_right _ (by omega)))
   · change volume (decide (a≤ b))≤ _
     omega
 def minRealizer : Realizer (fun x : ℕ×ℕ => min x.1 x.2) :=
   ((Realizer.le.pair Realizer.id).comp (Realizer.fst.choose Realizer.snd)).congr (fun x => by simp [min_def])
 theorem min_polynomial : PolyBound minRealizer := by
   unfold minRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair nat_le_polynomial (linear_polynomial linear_id))
     (polynomial_choose (linear_polynomial linear_fst) (linear_polynomial linear_snd))

 def capCurrent : Realizer (fun x : Bool×(ℕ×ℕ) => x.2.1) := Realizer.snd.comp Realizer.fst
 def capLimit : Realizer (fun x : Bool×(ℕ×ℕ) => x.2.2) := Realizer.snd.comp Realizer.snd
 def capNext : Realizer (fun x : Bool×(ℕ×ℕ) => 2*x.2.1+x.1.toNat) :=
   ((((capCurrent.pair capCurrent).comp Realizer.add).pair (Realizer.fst.comp boolNat)).comp Realizer.add).congr
     (fun _ => by dsimp only [Function.comp_apply]; omega)
 def capStepRealizer : Realizer capStep := ((capLimit.pair capNext).comp minRealizer).pair capLimit
 theorem capStep_polynomial : PolyBound capStepRealizer := by
   have hc : PolyBound capCurrent := linear_polynomial (linear_comp linear_snd linear_fst)
   have hl : PolyBound capLimit := linear_polynomial (linear_comp linear_snd linear_snd)
   have hn : PolyBound capNext := by
     unfold capNext
     apply polynomial_congr
     exact polynomial_comp (polynomial_pair (polynomial_comp (polynomial_pair hc hc) BinaryGcd.nat_add_polynomial)
       (linear_polynomial (linear_comp linear_fst boolNat_linear))) BinaryGcd.nat_add_polynomial
   exact polynomial_pair (polynomial_comp (polynomial_pair hl hn) min_polynomial) hl

 theorem capFold_volume (L : List Bool) (v c : ℕ) :
     volume (L.foldl (fun s b => capStep (b,s)) (v,c))≤2*v+4*c+3 := by
   have h1 := capFold_bound L v c
   have h2 := capFold_second L v c
   change volume ((L.foldl (fun s b => capStep (b,s)) (v,c)).1,
     (L.foldl (fun s b => capStep (b,s)) (v,c)).2)≤ _
   simp only [volume_pair,volume_nat,h2]
   omega
 theorem cap_fold_polynomial : PolyBound capStepRealizer.fold := by
   obtain ⟨C,q,hC,hR⟩ := capStep_polynomial
   refine ⟨C*17^q+2010,q+2,by positivity,?_⟩
   rintro ⟨L,v,c⟩
   let z := volume (L,(v,c))+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hL := bits_length_volume L
   have hsmall : v+c+L.length+1≤ z := by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have hvol : ∀j,j≤ L.length → volume ((L.take j).foldl (fun s b => capStep (b,s)) (v,c))≤12*z := by
     intro j _
     have hh := capFold_volume (L.take j) v c
     omega
   have ht := bit_fold_envelope capStepRealizer C q (fun x => (hR x).1) L (v,c) z hz
     (by omega) (by dsimp [z]; simp only [volume_pair]; omega) hvol
   have hv := hvol L.length le_rfl
   rw [List.take_length] at hv
   have hp : z≤ z^(q+2) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+2)
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (L.foldl (fun s b => capStep (b,s)) (v,c))≤ _
     exact hv.trans ((Nat.mul_le_mul_left 12 hp).trans (Nat.mul_le_mul_right _ (by omega)))

 def cappedValueRealizer : Realizer (fun x : List Bool×ℕ => cappedValue x.1 x.2) :=
   (((Realizer.fst.comp Realizer.reverse).pair ((Realizer.constant 0).pair Realizer.snd)).comp capStepRealizer.fold).comp Realizer.fst
 theorem cappedValue_polynomial : PolyBound cappedValueRealizer :=
   polynomial_comp (polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) reverse_polynomial)
     (polynomial_pair (linear_polynomial (linear_constant (0 : ℕ))) (linear_polynomial linear_snd))) cap_fold_polynomial)
     (linear_polynomial linear_fst)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.NaturalBinaryCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem trim_volume (A : List Bool) : volume (trim A)≤ volume A := by
   induction A with
   | nil => rfl
   | cons b A ih =>
     by_cases ht : trim A=[]
     · cases b <;> simp [trim,ht,volume_cons] <;> have hh := volume_pos A <;> omega
     · simp only [trim,ht,if_false,volume_cons]
       omega
 theorem increment_volume (A : List Bool) : volume (increment A)≤ volume A+4 := by
   induction A with
   | nil => decide
   | cons b A ih => cases b <;> simp [increment,volume_cons] at * <;> omega

 def nextWord (A : List Bool) : List Bool := trim (BinaryAdder.word A [true])
 def nextWordRealizer : Realizer nextWord :=
   ((Realizer.id.pair (Realizer.constant [true])).comp BinaryAdder.wordRealizer).comp trimRealizer
 theorem nextWord_polynomial : PolyBound nextWordRealizer :=
   polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_id)
     (linear_polynomial (linear_constant [true]))) word_polynomial) trim_polynomial
 theorem nextWord_value (A : List Bool) : value (nextWord A)=value A+1 := by
   rw [nextWord,trim_value,BinaryAdder.word_value]
   simp [value]
 theorem nextWord_canonical (A : List Bool) : trim (nextWord A)=nextWord A := trim_idem _
 theorem nextWord_eq (A : List Bool) : nextWord A=trim (increment A) := by
   apply canonical_value_injective _ _ (nextWord_canonical A) (trim_idem _)
   rw [nextWord_value,trim_value,increment_value]
 theorem nextWord_volume (A : List Bool) : volume (nextWord A)≤ volume A+4 := by
   rw [nextWord_eq]
   exact (trim_volume _).trans (increment_volume A)
 theorem nextWord_iter_value (n : ℕ) : value (nextWord^[n] [])=n := by
   induction n with
   | zero => rfl
   | succ n ih => rw [Function.iterate_succ_apply',nextWord_value,ih]
 theorem nextWord_iter_canonical (n : ℕ) : trim (nextWord^[n] [])=nextWord^[n] [] := by
   cases n with
   | zero => rfl
   | succ n => rw [Function.iterate_succ_apply']; exact nextWord_canonical _
 def naturalWordRealizer : Realizer natBits :=
   ((Realizer.id.pair Realizer.nil).comp nextWordRealizer.iterate).congr (fun n => by
     change nextWord^[n] []=natBits n
     rw [canonical_eq_natBits _ (nextWord_iter_canonical n),nextWord_iter_value])
 theorem naturalWord_polynomial : PolyBound naturalWordRealizer := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : ℕ => ([] : List Bool))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   unfold naturalWordRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial hn))
     (polynomial_iterate nextWord_polynomial 4 nextWord_volume)
 def naturalCodeRealizer : Realizer encodeNat := (naturalWordRealizer.comp prefixRealizer).congr prefix_natBits
 theorem naturalCode_polynomial : PolyBound naturalCodeRealizer := by
   unfold naturalCodeRealizer
   apply polynomial_congr
   exact polynomial_comp naturalWord_polynomial prefix_polynomial

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EncodingBounds
noncomputable section

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.EncodingBounds

 theorem natBits_length (n : ℕ) : (natBits n).length ≤ n := by
  simpa only [natBits, List.length_map] using
    (Nat.digits_length_le_iff (by decide : 1 < 2) n).mpr (show n < 2 ^ n from Nat.lt_two_pow_self)

 theorem encodeNat_length (n : ℕ) : (encodeNat n).length ≤ 2 * n + 1 := by
  have h := natBits_length n
  simp only [encodeNat, List.length_append, List.length_replicate, List.length_singleton]
  omega

 theorem rationalBits_length (r : RationalCode) : 1 ≤ r.bits.length := by
  simp only [RationalCode.bits, encodeInt, List.length_append, List.length_singleton]
  omega

 theorem order_le_data {n : ℕ} (w : Fin n → RationalCode) (ε : RationalCode) :
    n ≤ (rationalData w ε).length := by
  have hsum : (∑ _v : Fin n, 1) ≤ ∑ v : Fin n, (w v).bits.length :=
    Finset.sum_le_sum (fun v hv => rationalBits_length (w v))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hsum
  have heq : (rationalData w ε).length = (∑ v, (w v).bits.length) + ε.bits.length := by
    simp [rationalData, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  omega

 theorem graphBits_length {n : ℕ} (G : SimpleGraph (Fin n)) :
    (graphBits G).length ≤ (n + 1) ^ 2 := by
  classical
  have hpart (u : Fin n) : ((List.finRange n).filter (fun v => u < v)).length ≤ n := by
    simpa using (List.length_filter_le (fun v : Fin n => decide (u < v)) (List.finRange n))
  have hsum : (∑ u : Fin n, ((List.finRange n).filter (fun v => u < v)).length) ≤ n * n := by
    calc
      _ ≤ ∑ _u : Fin n, n := Finset.sum_le_sum (fun v hv => hpart v)
      _ = n * n := by simp
  have heq : (graphBits G).length = (encodeNat n).length +
      ∑ u : Fin n, ((List.finRange n).filter (fun v => u < v)).length := by
    simp [graphBits, List.length_flatMap, List.finRange, List.map_ofFn, List.sum_ofFn]
  have henc := encodeNat_length n
  nlinarith

 theorem input_length {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode) :
    (weightedInput G w ε).length + 1 ≤ 3 * ((rationalData w ε).length + 1) ^ 2 := by
  have hn := order_le_data w ε
  have hg := graphBits_length G
  simp only [weightedInput, List.length_append]
  nlinarith

end EdgeSublinearMWIS.Main.EncodingBounds
end

-- Solutions.ReadNatural
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def readNatural (L : List Bool) : ℕ×List Bool :=
   let A := readWord L
   (cappedValue A.1 (L.length+1),A.2)
 def parserCap : Realizer (fun L : List Bool => L.length+1) := BinaryAdder.wordLength.comp Realizer.succ
 def readNaturalRealizer : Realizer readNatural :=
   ((((readWordRealizer.comp Realizer.fst).pair parserCap).comp cappedValueRealizer).pair (readWordRealizer.comp Realizer.snd))
 theorem readNatural_polynomial : PolyBound readNaturalRealizer :=
   polynomial_pair (polynomial_comp (polynomial_pair (polynomial_comp readWord_polynomial (linear_polynomial linear_fst))
     (polynomial_comp BinaryGcd.wordLength_polynomial (linear_polynomial succ_linear))) cappedValue_polynomial)
     (polynomial_comp readWord_polynomial (linear_polynomial linear_snd))

 theorem readWord_encoded (n : ℕ) (rest : List Bool) : readWord (encodeNat n++rest)=(natBits n,rest) := by
   rw [← prefix_natBits,readWord_prefix]
 theorem readNatural_encoded (n : ℕ) (rest : List Bool) (h : n≤(encodeNat n++rest).length+1) :
     readNatural (encodeNat n++rest)=(n,rest) := by
   dsimp only [readNatural]
   rw [readWord_encoded,cappedValue_eq,value_natBits,Nat.min_eq_right h]

 theorem weighted_order_bound {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode) :
     n≤(weightedInput G w ε).length+1 := by
   have h := EncodingBounds.order_le_data w ε
   simp only [weightedInput,List.length_append]
   omega

 theorem readNatural_weighted {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode) :
     (readNatural (weightedInput G w ε)).1=n := by
   let rest := ((List.finRange n).flatMap (fun u => ((List.finRange n).filter (fun v => u< v)).map
     (fun v => decide (G.Adj u v))))++rationalData w ε
   have he : weightedInput G w ε=encodeNat n++rest := by simp only [weightedInput,graphBits,List.append_assoc]; rfl
   have hb := weighted_order_bound G w ε
   rw [he] at hb ⊢
   rw [readNatural_encoded n rest hb]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.WordValueCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def valueStep (x : Bool×ℕ) : ℕ := 2*x.2+x.1.toNat
 def valueStepRealizer : Realizer valueStep :=
   ((((Realizer.snd.pair Realizer.snd).comp Realizer.add).pair (Realizer.fst.comp boolNat)).comp Realizer.add).congr
     (fun _ => by dsimp only [Function.comp_apply,valueStep]; omega)
 theorem valueStep_polynomial : PolyBound valueStepRealizer := by
   unfold valueStepRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair
     (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_snd)) BinaryGcd.nat_add_polynomial)
     (linear_polynomial (linear_comp linear_fst boolNat_linear))) BinaryGcd.nat_add_polynomial
 theorem valueFold (L : List Bool) (v : ℕ) :
     L.foldl (fun v b => valueStep (b,v)) v=value L.reverse+2^L.length*v := by
   induction L generalizing v with
   | nil => simp [value]
   | cons b L ih =>
     rw [List.foldl_cons,ih,List.reverse_cons,BinaryAdder.value_append]
     simp only [valueStep,value,List.length_reverse,List.length_cons,pow_succ,Nat.mul_zero,Nat.add_zero]
     ring
 theorem value_drop_le (A : List Bool) (k : ℕ) : value (A.drop k)≤ value A := by
   induction k generalizing A with
   | zero => rfl
   | succ k ih =>
     cases A with
     | nil => simp [value]
     | cons b A => rw [List.drop_succ_cons]; exact (ih A).trans (by dsimp only [value]; omega)
 theorem valuePrefix (A : List Bool) (j : ℕ) :
     (A.reverse.take j).foldl (fun v b => valueStep (b,v)) 0≤ value A := by
   rw [valueFold,Nat.mul_zero,Nat.add_zero,List.reverse_take,List.reverse_reverse,List.length_reverse]
   exact value_drop_le A _
 def valueInitial : Realizer (fun A : List Bool => (A.reverse,(0 : ℕ))) := Realizer.reverse.pair (Realizer.constant 0)
 def valueRealizer : Realizer value := (valueInitial.comp valueStepRealizer.fold).congr (fun A => by
   change A.reverse.foldl (fun v b => valueStep (b,v)) 0=value A
   rw [valueFold,List.reverse_reverse]
   simp only [Nat.mul_zero,Nat.add_zero])
 theorem valueInitial_polynomial : PolyBound valueInitial := polynomial_pair reverse_polynomial (linear_polynomial (linear_constant (0 : ℕ)))
 theorem value_time : ∃ C q : ℕ,0< C ∧ ∀ A : List Bool,
     valueRealizer.time A≤ C*(value A+A.length+1)^q := by
   obtain ⟨C,q,hC,hR⟩ := valueStep_polynomial
   obtain ⟨I,p,hI,hinit⟩ := valueInitial_polynomial
   let F := C*17^q+2000
   let e := p+q+3
   refine ⟨I*5^p+F+100,e,by dsimp [F]; positivity,?_⟩
   intro A
   let z := value A+A.length+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hL : A.length≤ z := by dsimp [z]; omega
   have hV : value A≤ z := by dsimp [z]; omega
   have hvolA := BinaryAdder.volume_bits A
   have hprefix : ∀j,j≤ A.reverse.length → volume ((A.reverse.take j).foldl (fun v b => valueStep (b,v)) 0)≤12*z := by
     intro j _
     have hh := valuePrefix A j
     simp only [volume_nat]
     omega
   have hfold := bit_fold_envelope valueStepRealizer C q (fun x => (hR x).1) A.reverse 0 z hz
     (by simpa only [List.length_reverse] using hL) (by rw [volume_reverse]; omega) hprefix
   have hp : z^p≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hq : z^(q+2)≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hze : z≤ z^e := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by dsimp [e]; omega : 1≤ e)
   have hi : valueInitial.time A≤ I*5^p*z^e := by
     have hh := ((hinit A).1).trans (Nat.mul_le_mul_left I (Nat.pow_le_pow_left (show volume A+1≤5*z by omega) p))
     simp only [mul_pow] at hh
     exact hh.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (I*5^p) hp)
   have hf := hfold.trans (Nat.mul_le_mul_left F hq)
   have hcopy : 10*(volume (A.reverse,(0 : ℕ))+1)≤100*z^e := by
     simp only [volume_pair,volume_nat,volume_reverse]
     omega
   have heq : valueRealizer.time A=valueInitial.time A+valueStepRealizer.fold.time (A.reverse,0)+10*(volume (A.reverse,(0 : ℕ))+1) := by
     dsimp only [valueRealizer]
     simp only [Realizer.time_congr,Realizer.time_comp,Function.comp_apply]
   rw [heq]
   change _≤(I*5^p+F+100)*z^e
   nlinarith only [hi,hf,hcopy]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RationalBatch
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem volume_take_drop (L : List Bool) (k : ℕ) : volume (L.take k)+volume (L.drop k)=volume L+1 := by
   have hh := volume_append (L.take k) (L.drop k)
   rw [List.take_append_drop] at hh
   omega
 theorem volume_drop_le (L : List Bool) (k : ℕ) : volume (L.drop k)≤ volume L := by
   have hh := volume_take_drop L k
   have hp := volume_pos (L.take k)
   omega
 theorem readWord_volume (L : List Bool) : volume (readWord L).1+volume (readWord L).2≤ volume L+1 := by
   dsimp only [readWord,splitWord]
   have hh := volume_take_drop (L.drop ((L.takeWhile id).length+1)) ((L.takeWhile id).length)
   have hd := volume_drop_le L ((L.takeWhile id).length+1)
   omega
 theorem readRational_volume (L : List Bool) : volume (readRational L).1+volume (readRational L).2≤ volume L+7 := by
   have hA := readWord_volume L.tail
   have hB := readWord_volume (readWord L.tail).2
   have ht : volume L.tail≤ volume L := by cases L <;> simp [volume_cons] <;> omega
   have hs := volume_bool (L.headD false)
   dsimp only [readRational]
   simp only [volume_pair]
   omega

 abbrev BatchState := List Bool×List SignedWords
 def batchStep (s : BatchState) : BatchState :=
   let A := readRational s.1
   (A.2,A.1::s.2)
 def batchStepRealizer : Realizer batchStep :=
   (((Realizer.fst.comp readRationalRealizer).comp Realizer.snd).pair
     ((((Realizer.fst.comp readRationalRealizer).comp Realizer.fst).pair Realizer.snd).comp Realizer.cons))
 theorem batchStep_polynomial : PolyBound batchStepRealizer :=
   polynomial_pair (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) readRational_polynomial) (linear_polynomial linear_snd))
     (polynomial_comp (polynomial_pair
       (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) readRational_polynomial) (linear_polynomial linear_fst))
       (linear_polynomial linear_snd)) (linear_polynomial linear_cons))
 theorem batchStep_volume (s : BatchState) : volume (batchStep s)≤ volume s+8 := by
   rcases s with ⟨L,R⟩
   have hv := readRational_volume L
   simp only [batchStep,volume_pair,volume_cons]
   omega

 def readMany (n : ℕ) (L : List Bool) : List SignedWords×List Bool :=
   let s := batchStep^[n] (L,[])
   (s.2.reverse,s.1)
 def readManyRealizer : Realizer (fun x : ℕ×List Bool => readMany x.1 x.2) :=
   (((Realizer.fst.pair (Realizer.snd.pair Realizer.nil)).comp batchStepRealizer.iterate).comp
     ((Realizer.snd.comp Realizer.reverse).pair Realizer.fst))
 theorem readMany_polynomial : PolyBound readManyRealizer := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : ℕ×List Bool => ([] : List SignedWords))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   unfold readManyRealizer
   refine polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_fst)
     (polynomial_pair (linear_polynomial linear_snd) (linear_polynomial hn)))
       (polynomial_iterate batchStep_polynomial 8 batchStep_volume))
     (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) ?_) (linear_polynomial linear_fst))
   -- The generic reverse routine has a quadratic bound in coded volume.
   refine ⟨201,2,by omega,?_⟩
   intro L
   have hlen : L.length≤ volume L := by
     induction L with
     | nil => simp
     | cons a L ih => simp only [List.length_cons,volume_cons]; omega
   have ht := Uniform.time_reverse (I:=Unit) (α:=fun _ => SignedWords) () L
   have hp : L.length+1≤ volume L+1 := by omega
   have hm := Nat.mul_le_mul_right (200*(volume L+1)) hp
   constructor
   · change Realizer.reverse.time L≤ _
     have he : 200*(L.length+1)*(volume L+1)≤200*(volume L+1)^2 := by nlinarith only [hm]
     exact ht.trans (he.trans (Nat.mul_le_mul_right _ (by omega)))
   · rw [volume_reverse]
     nlinarith

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 def codeWords (q : RationalCode) : SignedWords :=
   (decide (q.numerator<0),(natBits q.numerator.natAbs,natBits q.denominator))
 theorem batchStep_codes (qs : List RationalCode) (rest : List Bool) (acc : List SignedWords) :
     batchStep^[qs.length] (qs.flatMap RationalCode.bits++rest,acc)=
       (rest,(qs.map codeWords).reverse++acc) := by
   induction qs generalizing acc with
   | nil => simp
   | cons q qs ih =>
     rw [List.length_cons,Function.iterate_succ_apply]
     simp only [List.flatMap_cons,List.append_assoc,batchStep,readRational_code]
     rw [ih,List.map_cons,List.reverse_cons]
     simp only [List.append_assoc,List.singleton_append,codeWords]
 theorem readMany_codes (qs : List RationalCode) (rest : List Bool) :
     readMany qs.length (qs.flatMap RationalCode.bits++rest)=(qs.map codeWords,rest) := by
   dsimp only [readMany]
   rw [batchStep_codes]
   simp
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialIterateGrowth
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

 theorem growth_coefficient (F E : ℕ) : 10000*F+10000*E+10000≤100000*(F+E+10) := by omega
 theorem growth_output_coefficient (F E : ℕ) : E≤100000*(F+E+10) := by omega

 theorem polynomial_iterate_growth {f : α → α} {R : Realizer f} (hR : PolyBound R) (E r : ℕ)
    (hg : ∀x j,volume (f^[j] x)≤ E*(volume x+j+1)^r) : PolyBound R.iterate := by
   obtain ⟨C,q,hC,hR⟩ := hR
   let F := C*(E+1)^q
   let e := r*q+r+2
   refine ⟨100000*(F+E+10),e,by dsimp [F]; positivity,?_⟩
   rintro ⟨n,a⟩
   let z := volume (n,a)+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hn : n+1≤ z := by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have ha : volume a+n+1≤ z := by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have hV (j : ℕ) (hj : j≤ n) : volume (f^[j] a)≤ E*z^r :=
     (hg a j).trans (Nat.mul_le_mul_left E (Nat.pow_le_pow_left (by omega) r))
   have hT (j : ℕ) (hj : j< n) : R.time (f^[j] a)≤ F*z^(r*q) := by
     have hh := (hR (f^[j] a)).1
     have hv := hV j hj.le
     have hp : 1≤ z^r := one_le_pow₀ hz
     have hbase : volume (f^[j] a)+1≤(E+1)*z^r := by nlinarith
     have ht := hh.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
     simpa only [F,mul_pow,pow_mul,Nat.mul_assoc] using ht
   have ht := Realizer.time_iterate_le R n a (F*z^(r*q)) (E*z^r) hT hV
   have hq : z^(r*q+1)≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hr : z^(r+1)≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have h2 : z^2≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   constructor
   · change _≤100000*(F+E+10)*z^e
     have hm := Nat.mul_le_mul hn (show F*z^(r*q)+E*z^r+n+1≤ F*z^(r*q)+E*z^r+z by omega)
     have hm' := Nat.mul_le_mul_left 10000 hm
     have hpq := Nat.mul_le_mul_left (10000*F) hq
     have hpr := Nat.mul_le_mul_left (10000*E) hr
     have hp2 := Nat.mul_le_mul_left 10000 h2
     have hs : R.iterate.time (n,a)≤(10000*F+10000*E+10000)*z^e := by
       rw [pow_succ] at hpq hpr
       nlinarith only [ht,hm',hpq,hpr,hp2]
     exact hs.trans (Nat.mul_le_mul_right _ (growth_coefficient F E))
   · change volume (f^[n] a)≤100000*(F+E+10)*z^e
     have hp := Nat.pow_le_pow_right hz (by dsimp [e]; omega : r≤ e)
     have hh := (hV n le_rfl).trans (Nat.mul_le_mul_left E hp)
     exact hh.trans (Nat.mul_le_mul_right _ (growth_output_coefficient F E))

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.TriangularCode
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def triStep (s : ℕ×ℕ) : ℕ×ℕ := (s.1+1,s.2+s.1)
 def triStepRealizer : Realizer triStep := (Realizer.fst.comp Realizer.succ).pair
   ((Realizer.snd.pair Realizer.fst).comp Realizer.add)
 theorem triStep_polynomial : PolyBound triStepRealizer :=
   polynomial_pair (linear_polynomial (linear_comp linear_fst succ_linear))
     (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) BinaryGcd.nat_add_polynomial)

 theorem triStep_first (i s j : ℕ) : (triStep^[j] (i,s)).1=i+j := by
   induction j with
   | zero => rfl
   | succ j ih => rw [Function.iterate_succ_apply']; dsimp only [triStep]; omega
 theorem triStep_second (i s j : ℕ) : (triStep^[j] (i,s)).2≤ s+j*(i+j) := by
   induction j with
   | zero => simp
   | succ j ih => rw [Function.iterate_succ_apply']; dsimp only [triStep]; rw [triStep_first]; nlinarith
 theorem triStep_growth (s : ℕ×ℕ) (j : ℕ) : volume (triStep^[j] s)≤10*(volume s+j+1)^2 := by
   rcases s with ⟨i,s⟩
   let z := volume (i,s)+j+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hbase : i+s+j+1≤ z := by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have h1 := triStep_first i s j
   have h2 := triStep_second i s j
   have hp : j*(i+j)≤ z*z := Nat.mul_le_mul (by omega) (by omega)
   change volume ((triStep^[j] (i,s)).1,(triStep^[j] (i,s)).2)≤10*z^2
   simp only [volume_pair,volume_nat,h1]
   nlinarith
 theorem triStep_iterate_poly : PolyBound triStepRealizer.iterate :=
   polynomial_iterate_growth triStep_polynomial 10 2 triStep_growth

 def triangular (n : ℕ) : ℕ := (triStep^[n] (0,0)).2
 theorem triStep_sum (n : ℕ) : triStep^[n] (0,0)=(n,∑ i ∈ Finset.range n,i) := by
   induction n with
   | zero => simp
   | succ n ih => rw [Function.iterate_succ_apply',ih]; simp [triStep,Finset.sum_range_succ]
 theorem triangular_eq (n : ℕ) : triangular n=n*(n-1)/2 := by
   rw [triangular,triStep_sum,Finset.sum_range_id]
 def triangularRealizer : Realizer triangular :=
   (((Realizer.id.pair (Realizer.constant (0,0))).comp triStepRealizer.iterate).comp Realizer.snd)
 theorem triangular_polynomial : PolyBound triangularRealizer :=
   polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_id)
     (linear_polynomial (linear_constant ((0 : ℕ),(0 : ℕ))))) triStep_iterate_poly) (linear_polynomial linear_snd)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GraphRawCode
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 noncomputable def adjacencyBits {n : ℕ} (G : SimpleGraph (Fin n)) : List Bool :=
   (List.finRange n).flatMap (fun u => ((List.finRange n).filter (fun v => u< v)).map (fun v => decide (G.Adj u v)))
 theorem adjacency_row_length {n : ℕ} (u : Fin n) :
     ((List.finRange n).filter (fun v => u< v)).length=n-1-u.val := by
   rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_finRange n))]
   have he : ((List.finRange n).filter (fun v => u< v)).toFinset=Finset.Ioi u := by
     ext v
     simp
   rw [he,Fin.card_Ioi]
 theorem adjacencyBits_length {n : ℕ} (G : SimpleGraph (Fin n)) : (adjacencyBits G).length=triangular n := by
   have he : (adjacencyBits G).length=∑ u : Fin n,((List.finRange n).filter (fun v => u< v)).length := by
     simp [adjacencyBits,List.length_flatMap,List.finRange,List.map_ofFn,List.sum_ofFn]
   rw [he]
   simp_rw [adjacency_row_length]
   rw [Fin.sum_univ_eq_sum_range (fun u => n-1-u) n,Finset.sum_range_reflect (fun u => u) n,
     Finset.sum_range_id,triangular_eq]
 theorem graphBits_eq {n : ℕ} (G : SimpleGraph (Fin n)) : graphBits G=encodeNat n++adjacencyBits G := rfl

 def graphStart (L : List Bool) : ℕ×(List Bool×List Bool) :=
   let p := readNatural L
   (p.1,splitWord p.2 (triangular p.1))
 def graphStartRealizer : Realizer graphStart :=
   (readNaturalRealizer.comp Realizer.fst).pair
     (((readNaturalRealizer.comp Realizer.snd).pair ((readNaturalRealizer.comp Realizer.fst).comp triangularRealizer)).comp splitWordRealizer)
 theorem graphStart_polynomial : PolyBound graphStartRealizer :=
   polynomial_pair (polynomial_comp readNatural_polynomial (linear_polynomial linear_fst))
     (polynomial_comp (polynomial_pair (polynomial_comp readNatural_polynomial (linear_polynomial linear_snd))
       (polynomial_comp (polynomial_comp readNatural_polynomial (linear_polynomial linear_fst)) triangular_polynomial)) splitWord_polynomial)

 theorem graphStart_weighted {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode) :
     graphStart (weightedInput G w ε)=(n,(adjacencyBits G,rationalData w ε)) := by
   have he : weightedInput G w ε=encodeNat n++(adjacencyBits G++rationalData w ε) := by
     rw [weightedInput,graphBits_eq,List.append_assoc]
   have hb := weighted_order_bound G w ε
   rw [he] at hb ⊢
   dsimp only [graphStart]
   rw [readNatural_encoded n _ hb,← adjacencyBits_length G]
   simp only [splitWord,List.take_left,List.drop_left]

 theorem graph_order_bound {n : ℕ} (G : SimpleGraph (Fin n)) : n≤(graphBits G).length+1 := by
   by_cases hn : 2≤ n
   · have htri : n-1≤ triangular n := by
       rw [triangular_eq,Nat.le_div_iff_mul_le (by omega : 0<2)]
       simpa only [Nat.mul_comm 2 (n-1)] using Nat.mul_le_mul_right (n-1) hn
     rw [graphBits_eq,List.length_append,adjacencyBits_length]
     omega
   · omega

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.HeightMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.HeightMath

 theorem exponential_dominates (n : ℕ) : (n+1)*4^n≤9^n := by
   induction n with
   | zero => simp
   | succ n ih =>
     have hsmall : 4*(n+2)≤9*(n+1) := by omega
     have hh := Nat.mul_le_mul_left (4^n) hsmall
     have hi := Nat.mul_le_mul_left 9 ih
     rw [pow_succ,pow_succ]
     nlinarith only [hh,hi]
 theorem height_search_bound (n : ℕ) : 2^(2*n)*n≤3^(2*n) := by
   have hh := exponential_dominates n
   have h2 : 2^(2*n)=(4:ℕ)^n := by rw [pow_mul]; rfl
   have h3 : 3^(2*n)=(9:ℕ)^n := by rw [pow_mul]; rfl
   rw [h2,h3]
   simpa only [Nat.mul_comm] using (Nat.mul_le_mul_right _ (Nat.le_succ n)).trans hh
 theorem height_find_exists (n : ℕ) :
     ∃ j,(List.range (2*n+1)).find? (fun j => decide (2^j*n≤3^j))=some j := by
   apply Option.ne_none_iff_exists'.mp
   intro h
   have hh := List.find?_eq_none.mp h (2*n) (List.mem_range.mpr (by omega))
   exact hh (by simpa only [decide_eq_true_eq] using height_search_bound n)
 theorem height_found (n : ℕ) :
     (List.range (2*n+1)).find? (fun j => decide (2^j*n≤3^j))=some (height n) := by
   obtain ⟨j,hj⟩ := height_find_exists n
   simp only [height,hj,Option.getD_some]
 theorem height_spec (n : ℕ) : 2^(height n)*n≤3^(height n) := by
   have hh := List.find?_some (height_found n)
   simpa only [decide_eq_true_eq] using hh
 theorem height_le_twice (n : ℕ) : height n≤2*n := by
   have hh := List.mem_of_find?_eq_some (height_found n)
   have hh' := List.mem_range.mp hh
   omega
 theorem height_zero : height 0=0 := by simp [height]
 theorem height_one : height 1=0 := by decide
 theorem height_pos (n : ℕ) (hn : 2≤ n) : 0< height n := by
   have hh := height_spec n
   by_contra h
   have he : height n=0 := by omega
   rw [he] at hh
   simp only [pow_zero,one_mul] at hh
   omega
end EdgeSublinearMWIS.Main.HeightMath

namespace EdgeSublinearMWIS.Main.HeightMath
 theorem height_minimal (n j : ℕ) (hj : j< height n) : ¬2^j*n≤3^j := by
   obtain ⟨hp,i,hi,he,hbefore⟩ := List.find?_eq_some_iff_getElem.mp (height_found n)
   have hie : i=height n := by simpa only [List.getElem_range] using he
   have hji : j< i := by omega
   have hh := hbefore j hji
   intro hc
   have ht : decide (2^j*n≤3^j)=true := by simpa only [decide_eq_true_eq] using hc
   have : False := by simpa only [List.getElem_range,ht,Bool.not_true,Bool.false_eq_true] using hh
   exact this
 theorem height_le_of_condition (n j : ℕ) (hj : 2^j*n≤3^j) : height n≤ j := by
   by_contra h
   exact height_minimal n j (by omega) hj
 theorem height_monotone : Monotone height := by
   intro m n hmn
   apply height_le_of_condition
   exact (Nat.mul_le_mul_left (2^height n) hmn).trans (height_spec n)
 theorem height_le_clog (n : ℕ) : height n≤2*Nat.clog 2 n := by
   let l := Nat.clog 2 n
   apply height_le_of_condition
   have hn : n≤2^l := Nat.le_pow_clog (by decide) n
   calc
     2^(2*l)*n≤2^(2*l)*2^l := Nat.mul_le_mul_left _ hn
     _ = 8^l := by
       rw [← pow_add,show 2*l+l=3*l by omega,pow_mul]
       rfl
     _ ≤ 9^l := Nat.pow_le_pow_left (by decide) l
     _ = 3^(2*l) := by rw [pow_mul]; rfl
end EdgeSublinearMWIS.Main.HeightMath

namespace EdgeSublinearMWIS.Main.HeightMath
 theorem height_balanced_step (w d : ℕ) (hw : 2≤ w) (hd : 3*d≤2*w) : height d+1≤ height w := by
   have hp := height_pos w hw
   let j := height w-1
   have hj : j+1=height w := by dsimp [j]; omega
   have hh := height_spec w
   rw [← hj,pow_succ,pow_succ] at hh
   have hm := Nat.mul_le_mul_left (2^j) hd
   have hc : 3*(2^j*d)≤3*(3^j) := by nlinarith only [hm,hh]
   have hc' : 2^j*d≤3^j := Nat.le_of_mul_le_mul_left hc (by decide : 0<3)
   have hh' := height_le_of_condition d j hc'
   omega
end EdgeSublinearMWIS.Main.HeightMath
end

-- Solutions.HeightLogBounds
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.HeightMath

 theorem one_le_logTwo {n : ℕ} (hn : 2≤ n) : 1≤ logTwo n := by
   have hnR : (2:ℝ)≤ n := by exact_mod_cast hn
   have hl := Real.log_le_log (by norm_num : (0:ℝ)<2) hnR
   rw [logTwo,le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))]
   simpa using hl
 theorem height_le_logTwo {n : ℕ} (hn : 2≤ n) : (height n:ℝ)≤4*logTwo n := by
   have h1 := one_le_logTwo hn
   have hlogb : 0≤ Real.logb 2 (n:ℝ) := by change 0≤ logTwo n; linarith
   have hc := Nat.ceil_lt_add_one hlogb
   have he : ⌈Real.logb (2:ℝ) (n:ℝ)⌉₊=Nat.clog 2 n := by simpa using Real.natCeil_logb_natCast 2 n
   rw [he] at hc
   change (Nat.clog 2 n:ℝ)< logTwo n+1 at hc
   have hh : (height n:ℝ)≤2*(Nat.clog 2 n:ℝ) := by exact_mod_cast height_le_clog n
   linarith
 theorem order_le_two_pow_height (n : ℕ) : n≤2^height n := by
   have hh := height_spec n
   have h3 : (3:ℕ)^height n≤2^height n*2^height n := by
     rw [← mul_pow]
     exact Nat.pow_le_pow_left (by decide) _
   have hp : 0<(2:ℕ)^height n := by positivity
   exact Nat.le_of_mul_le_mul_left (hh.trans h3) hp
 theorem logTwo_le_height {n : ℕ} (hn : 2≤ n) : logTwo n≤(height n:ℝ) := by
   have hp : (0:ℝ)< n := by exact_mod_cast (by omega : 0< n)
   have hh : (n:ℝ)≤(2:ℝ)^height n := by exact_mod_cast order_le_two_pow_height n
   have hl := Real.log_le_log hp hh
   rw [Real.log_pow] at hl
   rw [logTwo,div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))]
   exact hl
end EdgeSublinearMWIS.Main.HeightMath
end

-- Solutions.ThresholdBounds
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.HeightMath

 theorem threshold_monotone (B a : ℕ) (δ : ℚ) (hδ : 0<δ) : Monotone (fun n => threshold B a n δ) := by
   intro m n hmn
   unfold threshold
   apply max_le_max le_rfl
   apply Nat.ceil_mono
   apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B)
   apply pow_le_pow_left₀ (by positivity)
   apply div_le_div_of_nonneg_right _ hδ.le
   exact_mod_cast height_monotone hmn
 theorem threshold_log_bound (B a n : ℕ) (δ : ℚ) (hn : 2≤ n) (hδ : 0<δ) (hδ1 : δ<1) :
     (threshold B a n δ:ℝ)≤((B:ℝ)*4^(4*a-2)+1)*((δ:ℝ)⁻¹*logTwo n)^(4*a-2) := by
   let e := 4*a-2
   let X := (δ:ℝ)⁻¹*logTwo n
   have hd : (0:ℝ)<δ := by exact_mod_cast hδ
   have hd1 : (δ:ℝ)<1 := by exact_mod_cast hδ1
   have hinv : 1≤(δ:ℝ)⁻¹ := by rw [← one_div,le_div_iff₀ hd]; simpa using hd1.le
   have hlog := one_le_logTwo hn
   have hX : 1≤ X := by
     have hh := mul_le_mul hinv hlog (by norm_num : (0:ℝ)≤1) (by linarith : (0:ℝ)≤(δ:ℝ)⁻¹)
     simpa only [one_mul] using hh
   have hXp : 1≤ X^e := one_le_pow₀ hX
   have hheight : (height n:ℝ)/(δ:ℝ)≤4*X := by
     have hh := div_le_div_of_nonneg_right (height_le_logTwo hn) hd.le
     have he : 4*logTwo n/(δ:ℝ)=4*X := by dsimp [X]; simp only [div_eq_mul_inv]; ring
     exact hh.trans_eq he
   have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ)≤(height n:ℝ)/(δ:ℝ)) hheight e
   rw [mul_pow] at hpow
   have hmul := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg B : (0:ℝ)≤ B)
   have hv : (0:ℚ)≤(B:ℚ)*((height n:ℚ)/δ)^e := by positivity
   have hceilQ := Nat.ceil_lt_add_one hv
   have hceil : (⌈(B:ℚ)*((height n:ℚ)/δ)^e⌉₊:ℝ)<(B:ℝ)*((height n:ℝ)/(δ:ℝ))^e+1 := by exact_mod_cast hceilQ
   change (threshold B a n δ:ℝ)≤((B:ℝ)*4^e+1)*X^e
   rw [threshold,Nat.cast_max,Nat.cast_one]
   change max 1 (⌈(B:ℚ)*((height n:ℚ)/δ)^e⌉₊:ℝ)≤((B:ℝ)*4^e+1)*X^e
   apply max_le
   · have hnon : 0≤(B:ℝ)*4^e*X^e := by positivity
     nlinarith only [hXp,hnon]
   · nlinarith only [hceil,hmul,hXp]
end EdgeSublinearMWIS.Main.HeightMath
end

-- Solutions.SeparatorScale
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.HeightMath

 def pathScale (L n : ℕ) (δ : ℚ) : ℕ := ⌈(L:ℚ)*(height n:ℚ)/δ⌉₊
 theorem pathScale_lower (L n : ℕ) (δ : ℚ) :
     (L:ℝ)*(height n:ℝ)/(δ:ℝ)≤(pathScale L n δ:ℝ) := by
   have hh := Nat.le_ceil ((L:ℚ)*(height n:ℚ)/δ)
   unfold pathScale
   exact_mod_cast hh
 theorem pathScale_pos (L n : ℕ) (δ : ℚ) (hL : 1≤ L) (hn : 2≤ n) (hδ : 0<δ) (hδ1 : δ<1) :
     1≤ pathScale L n δ := by
   have hh := pathScale_lower L n δ
   have hd : (0:ℝ)<δ := by exact_mod_cast hδ
   have hd1 : (δ:ℝ)<1 := by exact_mod_cast hδ1
   have hH : (1:ℝ)≤ height n := by exact_mod_cast height_pos n hn
   have hLR : (1:ℝ)≤ L := by exact_mod_cast hL
   have hprod : (1:ℝ)≤(L:ℝ)*(height n:ℝ) := by nlinarith
   have hh' : (1:ℝ)≤(L:ℝ)*(height n:ℝ)/(δ:ℝ) := (le_div_iff₀ hd).mpr (by nlinarith)
   exact_mod_cast hh'.trans hh
 theorem pathScale_upper (L n : ℕ) (δ : ℚ) (hn : 2≤ n) (hδ : 0<δ) (hδ1 : δ<1) :
     (pathScale L n δ:ℝ)≤((L:ℝ)+1)*((height n:ℝ)/(δ:ℝ)) := by
   have hδR : (0:ℝ)<δ := by exact_mod_cast hδ
   have hδR1 : (δ:ℝ)<1 := by exact_mod_cast hδ1
   have hh := Nat.ceil_lt_add_one (show (0:ℚ)≤(L:ℚ)*(height n:ℚ)/δ by positivity)
   have hc : (pathScale L n δ:ℝ)<(L:ℝ)*(height n:ℝ)/(δ:ℝ)+1 := by
     unfold pathScale
     exact_mod_cast hh
   have hheight : (1:ℝ)≤ height n := by exact_mod_cast height_pos n hn
   have hbase : (1:ℝ)≤(height n:ℝ)/(δ:ℝ) := (le_div_iff₀ hδR).mpr (by linarith)
   have he : (L:ℝ)*(height n:ℝ)/(δ:ℝ)=(L:ℝ)*((height n:ℝ)/(δ:ℝ)) := by ring
   rw [he] at hc
   nlinarith
 theorem pathScale_source (c : ℝ) (L n : ℕ) (δ : ℚ) (hL : c≤ L) (hc : 0≤ c) (hn : 2≤ n) (hδ : 0<δ) :
     c*(δ:ℝ)⁻¹*logTwo n≤(pathScale L n δ:ℝ) := by
   have hd : (0:ℝ)<δ := by exact_mod_cast hδ
   have hlog := one_le_logTwo hn
   have hH := logTwo_le_height hn
   have hmul := mul_le_mul hL hH (by linarith : (0:ℝ)≤ logTwo n) (Nat.cast_nonneg L : (0:ℝ)≤ L)
   have hdiv := div_le_div_of_nonneg_right hmul hd.le
   have he : c*logTwo n/(δ:ℝ)=c*(δ:ℝ)⁻¹*logTwo n := by rw [div_eq_mul_inv]; ring
   rw [he] at hdiv
   exact hdiv.trans (pathScale_lower L n δ)
end EdgeSublinearMWIS.Main.HeightMath
end

-- Solutions.SeparatorThreshold
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.HeightMath

 theorem threshold_ge_power (B a n : ℕ) (δ : ℚ) :
     (B:ℝ)*((height n:ℝ)/(δ:ℝ))^(4*a-2)≤(threshold B a n δ:ℝ) := by
   have hh := Nat.le_ceil ((B:ℚ)*((height n:ℚ)/δ)^(4*a-2))
   have hm : (⌈(B:ℚ)*((height n:ℚ)/δ)^(4*a-2)⌉₊:ℚ)≤(threshold B a n δ:ℚ) := by
     exact_mod_cast (le_max_right 1 ⌈(B:ℚ)*((height n:ℚ)/δ)^(4*a-2)⌉₊)
   have hc := hh.trans hm
   exact_mod_cast hc
 theorem threshold_dominates_scale (B L a n : ℕ) (c : ℝ) (δ : ℚ)
     (hc : 0≤ c) (hB : c*((L:ℝ)+1)^(4*a-2)≤ B)
     (hn : 2≤ n) (hδ : 0<δ) (hδ1 : δ<1) :
     c*(pathScale L n δ:ℝ)^(4*a-2)≤(threshold B a n δ:ℝ) := by
   have hscale := pathScale_upper L n δ hn hδ hδ1
   have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (pathScale L n δ)) hscale (4*a-2)
   rw [mul_pow] at hpow
   have hh := mul_le_mul_of_nonneg_left hpow hc
   have hd : (0:ℝ)<δ := by exact_mod_cast hδ
   have hm := mul_le_mul_of_nonneg_right hB (show (0:ℝ)≤((height n:ℝ)/(δ:ℝ))^(4*a-2) by positivity)
   have he : c*(((L:ℝ)+1)^(4*a-2)*((height n:ℝ)/(δ:ℝ))^(4*a-2))=
       (c*((L:ℝ)+1)^(4*a-2))*((height n:ℝ)/(δ:ℝ))^(4*a-2) := by ring
   rw [he] at hh
   exact hh.trans (hm.trans (threshold_ge_power B a n δ))
end EdgeSublinearMWIS.Main.HeightMath
end

-- Solutions.LightSeparatorCall
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main
open HeightMath

 theorem light_separator_call (C : GraphClass) (a : ℕ) (K : ℝ)
     (hereditary : Hereditary C) (ha : 2≤ a) (bound : TreewidthBound C a K) :
     ∃ (B L : ℕ) (M : Program) (time : Polynomial ℕ),0< B ∧ 1≤ L ∧
       ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode),
         2≤ n → C n G → (∀v,0≤(x v).value ∧ (x v).value≤1) → 0<δ.value → δ.value<1 →
         (threshold B a n δ.value:ℝ)≤ vertexSum (fun v => ((x v).value:ℝ)) Finset.univ →
         edgeEnergy G (fun v => ((x v).value:ℝ))≤
           (vertexSum (fun v => ((x v).value:ℝ)) Finset.univ)^2/threshold B a n δ.value →
         ∃ (S : Finset (Fin n)) (t : ℕ),
           Runs M (flowInput G x δ++encodeNat (pathScale L n δ.value)) (false::mask S) t ∧
           t≤ time.eval ((flowInput G x δ++encodeNat (pathScale L n δ.value)).length+1) ∧
           Light G Finset.univ S δ.value (fun v => ((x v).value:ℝ)) := by
   obtain ⟨M,c₀,time,hc₀,hM⟩ := lemma_8
   obtain ⟨c,hc,hObstruct⟩ := lemma_11 C a K hereditary ha bound
   let L := max 1 ⌈c₀⌉₊
   let B := max 1 ⌈c*((L:ℝ)+1)^(4*a-2)⌉₊
   have hL : 1≤ L := le_max_left _ _
   have hL' : c₀≤(L:ℝ) := (Nat.le_ceil c₀).trans (by exact_mod_cast le_max_right 1 ⌈c₀⌉₊)
   have hB : 1≤ B := le_max_left _ _
   have hB' : c*((L:ℝ)+1)^(4*a-2)≤(B:ℝ) := by
     dsimp only [B]
     exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈c*((L:ℝ)+1)^(4*a-2)⌉₊)
   refine ⟨B,L,M,time,by omega,hL,?_⟩
   intro n G x δ hn hG hx hd hd1 hmass henergy
   let ell := pathScale L n δ.value
   have hell : 1≤ ell := pathScale_pos L n δ.value hL hn hd hd1
   have hTheta : 1≤ threshold B a n δ.value := le_max_left _ _
   have hThetaR : (0:ℝ)< threshold B a n δ.value := by exact_mod_cast (by omega : 0< threshold B a n δ.value)
   have hmasspos : 0< vertexSum (fun v => ((x v).value:ℝ)) Finset.univ := hThetaR.trans_le hmass
   have hellR : (1:ℝ)≤ ell := by exact_mod_cast hell
   obtain ⟨p,hp,hpbound,hNo⟩ := hObstruct (ell:ℝ) hellR
   have hpR : (0:ℝ)< p := by exact_mod_cast (by omega : 0< p)
   have hdom : (p:ℝ)≤ threshold B a n δ.value :=
     hpbound.trans (threshold_dominates_scale B L a n c δ.value hc.le hB' hn hd hd1)
   have hcost : ∀v,0≤((x v).value:ℝ) ∧ ((x v).value:ℝ)≤1 := by intro v; exact_mod_cast hx v
   have hno := hNo n G (fun v => ((x v).value:ℝ)) hG hcost (hdom.trans hmass)
     (henergy.trans (div_le_div_of_nonneg_left (sq_nonneg _) hpR hdom))
   have hscale : c₀*(δ.value:ℝ)⁻¹*logTwo n≤ ell := pathScale_source c₀ L n δ.value hL' hc₀.le hn hd
   obtain ⟨t,ht,hout⟩ := hM n G x δ ell hn (fun v => (hx v).1) hmasspos hd hd1 hscale
   rcases hout with hlight|hpath
   · obtain ⟨S,hRun,hLight⟩ := hlight
     exact ⟨S,t,hRun,ht,hLight⟩
   · obtain ⟨W,f,hRun,hPath⟩ := hpath
     exact False.elim (hno ⟨W,realPaths f,hPath⟩)
end EdgeSublinearMWIS.Main
end

-- Solutions.PolynomialMap
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 theorem length_volume (L : List α) : L.length≤ volume L := by
   induction L with
   | nil => simp
   | cons a L ih => simp only [List.length_cons,volume_cons]; omega
 def mapEnvironment {f : α×γ → β} (R : Realizer f) :
     Realizer (fun x : List α×γ => x.1.map (fun a => f (a,x.2))) := (R.uniform Unit).map.specialize ()
 theorem mapEnvironment_time {f : α×γ → β} (R : Realizer f) (x : List α×γ) :
     (mapEnvironment R).time x=(R.uniform Unit).map.time () x := rfl

 theorem polynomial_mapEnvironment {f : α×γ → β} {R : Realizer f} (hR : PolyBound R) : PolyBound (mapEnvironment R) := by
   obtain ⟨C,q,hC,hR⟩ := hR
   refine ⟨100000*(C+10),q+2,by positivity,?_⟩
   rintro ⟨xs,e⟩
   let z := volume (xs,e)+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hlen := length_volume xs
   have hlenz : xs.length+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hvolz : volume xs+volume e+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hq : z^q≤ z^(q+1) := Nat.pow_le_pow_right hz (by omega)
   have hze : z≤ z^(q+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+1)
   have hp1 : 1≤ z^(q+1) := one_le_pow₀ hz
   have hbounds (a : α) (ha : a∈xs) : R.time (a,e)≤ C*z^q ∧ volume (f (a,e))≤ C*z^q := by
     have hv := volume_mem_le ha
     have hbase : volume (a,e)+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
     have hh := hR (a,e)
     exact ⟨hh.1.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q)),
       hh.2.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))⟩
   have hout : volume (xs.map (fun a => f (a,e)))≤(C+2)*z^(q+1) := by
     have hh := volume_list_le (xs.map (fun a => f (a,e))) (C*z^q) (by
       intro b hb
       obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
       exact (hbounds a ha).2)
     rw [List.length_map] at hh
     have hm := Nat.mul_le_mul (show xs.length≤ z by omega) (show C*z^q+1≤ C*z^q+1 by rfl)
     have he : z*(C*z^q+1)=C*z^(q+1)+z := by rw [pow_succ]; ring
     rw [he] at hm
     nlinarith only [hh,hm,hze,hp1]
   have ht := Uniform.time_map (R.uniform Unit) () xs e (C*z^q) (fun a ha => (hbounds a ha).1)
   rw [Nat.mul_assoc] at ht
   have hinner : C*z^q+volume xs+volume e+volume (xs.map (fun a => f (a,e)))+1≤(2*C+6)*z^(q+1) := by
     have htime := Nat.mul_le_mul_left C hq
     nlinarith only [htime,hout,hvolz,hze,hp1]
   have hmul := Nat.mul_le_mul_left 30000 (Nat.mul_le_mul hlenz hinner)
   have he : 30000*(z*((2*C+6)*z^(q+1)))=30000*(2*C+6)*z^(q+2) := by rw [pow_succ]; ring
   rw [he] at hmul
   have hcoef : 30000*(2*C+6)≤100000*(C+10) := by omega
   constructor
   · rw [mapEnvironment_time]
     change (R.uniform Unit).map.time () (xs,e)≤100000*(C+10)*z^(q+2)
     have hh : (R.uniform Unit).map.time () (xs,e)≤30000*(2*C+6)*z^(q+2) := ht.trans hmul
     exact hh.trans (Nat.mul_le_mul_right (z^(q+2)) hcoef)
   · change volume (xs.map (fun a => f (a,e)))≤ _
     have hp := Nat.pow_le_pow_right hz (by omega : q+1≤ q+2)
     exact hout.trans ((Nat.mul_le_mul_left (C+2) hp).trans (Nat.mul_le_mul_right _ (by omega)))

 def mapList {f : α → β} (R : Realizer f) : Realizer (fun xs : List α => xs.map f) :=
   ((Realizer.id.pair Realizer.unit).comp (mapEnvironment (Realizer.fst.comp R))).congr (fun _ => rfl)
 theorem polynomial_mapList {f : α → β} {R : Realizer f} (hR : PolyBound R) : PolyBound (mapList R) := by
   have hu : Linear (Realizer.unit : Realizer (fun _ : List α => ())) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   unfold mapList
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial hu))
     (polynomial_mapEnvironment (polynomial_comp (linear_polynomial linear_fst) hR))

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.ListPolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

 theorem reverse_polynomial_generic : PolyBound (Realizer.reverse : Realizer (fun L : List α => L.reverse)) := by
   refine ⟨201,2,by omega,?_⟩
   intro L
   have hlen := length_volume L
   have ht := Uniform.time_reverse (I:=Unit) (α:=fun _ => α) () L
   have hm := Nat.mul_le_mul_right (200*(volume L+1)) (show L.length+1≤ volume L+1 by omega)
   constructor
   · have he : 200*(L.length+1)*(volume L+1)≤200*(volume L+1)^2 := by nlinarith only [hm]
     exact ht.trans (he.trans (Nat.mul_le_mul_right _ (by omega)))
   · rw [volume_reverse]
     nlinarith
 theorem take_volume_le (L : List α) (j : ℕ) : volume (L.take j)≤ volume L := by
   have hh := volume_append (L.take j) (L.drop j)
   rw [List.take_append_drop] at hh
   have hp := volume_pos (L.drop j)
   omega
 theorem cons_fold_polynomial_generic : PolyBound (Realizer.cons : Realizer (fun x : α×List α => x.1::x.2)).fold := by
   refine ⟨200,2,by omega,?_⟩
   rintro ⟨A,B⟩
   let z := volume (A,B)+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hlen : A.length≤ z := by have hh := length_volume A; dsimp [z]; simp only [volume_pair]; omega
   have hbase : volume A+volume B+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hv (j : ℕ) (_hj : j≤ A.length) : volume ((A.take j).foldl (fun s a => a::s) B)≤ z := by
     rw [Realizer.fold_cons_eq]
     have hh := volume_append (A.take j).reverse B
     rw [volume_reverse] at hh
     have ht := take_volume_le A j
     omega
   have ht (j : ℕ) (hj : j< A.length) :
       (Realizer.cons : Realizer (fun x : α×List α => x.1::x.2)).time (A[j],(A.take j).foldl (fun s a => a::s) B)≤5*z := by
     have ha := volume_mem_le (List.getElem_mem hj)
     have hb := hv j hj.le
     change volume (A[j],(A.take j).foldl (fun s a => a::s) B)+2≤ _
     simp only [volume_pair]
     omega
   have hh := fold_prefix_bound (Realizer.cons : Realizer (fun x : α×List α => x.1::x.2)) A B (5*z) z hv ht
   have hm := Nat.mul_le_mul hlen (show 5*z+20*(volume A+2*z+1)≤100*z by omega)
   have hp : z≤ z^2 := by nlinarith
   constructor
   · rw [Realizer.time_fold]
     change 2*volume (A,B)+6+Realizer.foldTime Realizer.cons B A≤200*z^2
     have he : volume (A,B)+1=z := rfl
     nlinarith only [hh,hm,hp,he,hz]
   · change volume (A.foldl (fun s a => a::s) B)≤ _
     have ho := hv A.length le_rfl
     rw [List.take_length] at ho
     exact ho.trans (hp.trans (Nat.le_mul_of_pos_left _ (by omega)))

 def appendList : Realizer (fun x : List α×List α => x.1++x.2) :=
   ((((Realizer.fst.comp Realizer.reverse).pair Realizer.snd).comp Realizer.cons.fold)).congr
     (fun _ => by simp only [Function.comp_apply,Realizer.fold_cons_eq,List.reverse_reverse])
 theorem appendList_polynomial : PolyBound (appendList : Realizer (fun x : List α×List α => x.1++x.2)) := by
   unfold appendList
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) reverse_polynomial_generic)
     (linear_polynomial linear_snd)) cons_fold_polynomial_generic

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.PolynomialFoldBounded
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

 theorem polynomial_fold_bounded {f : α×β → β} {R : Realizer f} (hR : PolyBound R) (E : ℕ)
     (hV : ∀ (xs : List α) b j,j≤ xs.length → volume ((xs.take j).foldl (fun b a => f (a,b)) b)≤ E*(volume (xs,b)+1)) :
     PolyBound R.fold := by
   obtain ⟨C,q,hC,hR⟩ := hR
   let F := C*(E+3)^q
   refine ⟨F+100*E+200,q+2,by dsimp [F]; positivity,?_⟩
   rintro ⟨xs,b⟩
   let z := volume (xs,b)+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hlen : xs.length≤ z := by have hh := length_volume xs; dsimp [z]; simp only [volume_pair]; omega
   have hxs : volume xs≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hv (j : ℕ) (hj : j≤ xs.length) : volume ((xs.take j).foldl (fun b a => f (a,b)) b)≤ E*z := hV xs b j hj
   have ht (j : ℕ) (hj : j< xs.length) : R.time (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)≤ F*z^q := by
     have ha := volume_mem_le (List.getElem_mem hj)
     have hb := hv j hj.le
     have hbase : volume (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)+1≤(E+3)*z := by simp only [volume_pair]; nlinarith
     have hh := ((hR _).1).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
     simpa only [F,mul_pow,Nat.mul_assoc] using hh
   have hh := fold_prefix_bound R xs b (F*z^q) (E*z) hv ht
   have hp1 : z^(q+1)≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hp2 : z^2≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hp : z≤ z^(q+2) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+2)
   have hm := Nat.mul_le_mul hlen (show F*z^q+20*(volume xs+2*(E*z)+1)≤ F*z^q+(40*E+40)*z by nlinarith)
   have he : z*(F*z^q+(40*E+40)*z)=F*z^(q+1)+(40*E+40)*z^2 := by rw [pow_succ]; ring
   rw [he] at hm
   have htime := Nat.mul_le_mul_left F hp1
   have hcopy := Nat.mul_le_mul_left (40*E+40) hp2
   constructor
   · rw [Realizer.time_fold]
     change 2*volume (xs,b)+6+Realizer.foldTime R b xs≤(F+100*E+200)*z^(q+2)
     have hinput : volume (xs,b)+1=z := rfl
     nlinarith only [hh,hm,htime,hcopy,hp,hinput,hz]
   · change volume (xs.foldl (fun b a => f (a,b)) b)≤ _
     have hv' := hv xs.length le_rfl
     rw [List.take_length] at hv'
     have hout := hv'.trans (Nat.mul_le_mul_left E hp)
     have hcoef : E≤ F+100*E+200 := by omega
     exact hout.trans (Nat.mul_le_mul_right _ hcoef)

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.ListFlattenRepeat
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

 def flattenStep (s : List α×List α) : List α := s.2++s.1
 def flattenStepRealizer : Realizer (flattenStep (α:=α)) := (Realizer.snd.pair Realizer.fst).comp appendList
 theorem flattenStep_polynomial : PolyBound (flattenStepRealizer (α:=α)) :=
   polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) appendList_polynomial
 theorem flattenFold (xs : List (List α)) (acc : List α) : xs.foldl (fun b a => flattenStep (a,b)) acc=acc++xs.flatten := by
   induction xs generalizing acc with
   | nil => simp
   | cons a xs ih => rw [List.foldl_cons,ih]; simp [flattenStep,List.append_assoc]
 theorem flatten_fold_polynomial : PolyBound (flattenStepRealizer (α:=α)).fold := by
   apply polynomial_fold_bounded flattenStep_polynomial 1
   intro xs acc j _
   rw [flattenFold]
   have hflat := volume_flatten (xs.take j)
   have ht := take_volume_le xs j
   have ha := volume_append acc (xs.take j).flatten
   simp only [volume_pair,one_mul]
   omega
 def flattenList : Realizer (fun xs : List (List α) => xs.flatten) :=
   ((Realizer.id.pair Realizer.nil).comp flattenStepRealizer.fold).congr (fun xs => by change xs.foldl (fun b a => flattenStep (a,b)) []=xs.flatten; rw [flattenFold]; rfl)
 theorem flattenList_polynomial : PolyBound (flattenList (α:=α)) := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : List (List α) => ([] : List α))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   unfold flattenList
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial hn)) flatten_fold_polynomial

 def repeatStep (s : α×List α) : α×List α := (s.1,s.1::s.2)
 def repeatStepRealizer : Realizer (repeatStep (α:=α)) := Realizer.fst.pair Realizer.cons
 theorem repeatStep_linear : Linear (repeatStepRealizer (α:=α)) := linear_pair linear_fst linear_cons
 theorem repeatStep_iterate (n : ℕ) (a : α) (L : List α) : repeatStep^[n] (a,L)=(a,List.replicate n a++L) := by
   induction n with
   | zero => rfl
   | succ n ih => rw [Function.iterate_succ_apply',ih]; simp only [repeatStep,List.replicate_succ,List.cons_append]
 theorem volume_replicate (n : ℕ) (a : α) : volume (List.replicate n a)=n*(volume a+1)+1 := by
   induction n with
   | zero => simp
   | succ n ih => rw [List.replicate_succ,volume_cons,ih]; ring
 theorem repeatStep_growth (s : α×List α) (j : ℕ) : volume (repeatStep^[j] s)≤3*(volume s+j+1)^2 := by
   rcases s with ⟨a,L⟩
   let z := volume (a,L)+j+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hbase : volume a+volume L+j+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hp : j*(volume a+1)≤ z*z := Nat.mul_le_mul (by omega) (by omega)
   have ha := volume_append (List.replicate j a) L
   rw [volume_replicate] at ha
   rw [repeatStep_iterate,volume_pair]
   change _≤3*z^2
   nlinarith
 def replicateList : Realizer (fun x : ℕ×α => List.replicate x.1 x.2) :=
   (((Realizer.fst.pair (Realizer.snd.pair Realizer.nil)).comp repeatStepRealizer.iterate).comp Realizer.snd).congr
     (fun x => by dsimp only [Function.comp_apply]; rw [repeatStep_iterate]; simp)
 theorem replicateList_polynomial : PolyBound (replicateList (α:=α)) := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : ℕ×α => ([] : List α))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   unfold replicateList
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_fst)
     (polynomial_pair (linear_polynomial linear_snd) (linear_polynomial hn)))
       (polynomial_iterate_growth (linear_polynomial repeatStep_linear) 3 2 repeatStep_growth)) (linear_polynomial linear_snd)

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.RangePolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RawStack

 theorem rangeStep_first (i : ℕ) (L : List ℕ) (j : ℕ) :
     ((fun s : ℕ×List ℕ => (s.1+1,s.1::s.2))^[j] (i,L)).1=i+j := by
   induction j with
   | zero => rfl
   | succ j ih => rw [Function.iterate_succ_apply']; dsimp only; omega
 theorem rangeStep_list_volume (i : ℕ) (L : List ℕ) (j : ℕ) :
     volume ((fun s : ℕ×List ℕ => (s.1+1,s.1::s.2))^[j] (i,L)).2≤ volume L+j*(2*i+2*j+2) := by
   induction j with
   | zero => simp
   | succ j ih =>
     rw [Function.iterate_succ_apply']
     dsimp only
     rw [volume_cons,volume_nat,rangeStep_first]
     nlinarith
 theorem rangeStep_growth (s : ℕ×List ℕ) (j : ℕ) :
     volume ((fun s : ℕ×List ℕ => (s.1+1,s.1::s.2))^[j] s)≤10*(volume s+j+1)^2 := by
   rcases s with ⟨i,L⟩
   let z := volume (i,L)+j+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hbase : i+volume L+j+1≤ z := by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have hfirst := rangeStep_first i L j
   have hlist := rangeStep_list_volume i L j
   have hp : j*(2*i+2*j+2)≤ z*(2*z+2) := Nat.mul_le_mul (by omega) (by omega)
   change volume (((fun s : ℕ×List ℕ => (s.1+1,s.1::s.2))^[j] (i,L)).1,
     ((fun s : ℕ×List ℕ => (s.1+1,s.1::s.2))^[j] (i,L)).2)≤10*z^2
   rw [volume_pair,volume_nat,hfirst]
   nlinarith
 theorem range_polynomial : PolyBound Realizer.range := by
   have hs : Linear Realizer.rangeStep := linear_pair (linear_comp linear_fst succ_linear) linear_cons
   have hi : PolyBound Realizer.rangeStep.iterate := polynomial_iterate_growth (linear_polynomial hs) 10 2 rangeStep_growth
   have hz : Linear (Realizer.zero : Realizer (fun _ : ℕ => (0 : ℕ))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   have hn : Linear (Realizer.nil : Realizer (fun _ : ℕ => ([] : List ℕ))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   unfold Realizer.range
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_id)
     (linear_polynomial (linear_pair hz hn))) hi)
     (polynomial_comp (linear_polynomial linear_snd) reverse_polynomial_generic)

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.FilterPolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α γ : Type} [Coding α] [Coding γ]

 def selectSingleton {p : α×γ → Bool} (P : Realizer p) : Realizer (fun x : α×γ => if p x then [x.1] else []) :=
   (P.pair Realizer.id).comp ((((Realizer.fst.pair Realizer.nil).comp Realizer.cons)).choose Realizer.nil)
 theorem selectSingleton_polynomial {p : α×γ → Bool} {P : Realizer p} (hP : PolyBound P) : PolyBound (selectSingleton P) := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : α×γ => ([] : List α))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   exact polynomial_comp (polynomial_pair hP (linear_polynomial linear_id))
     (polynomial_choose (linear_polynomial (linear_comp (linear_pair linear_fst hn) linear_cons)) (linear_polynomial hn))
 theorem filter_flatten (p : α×γ → Bool) (xs : List α) (e : γ) :
     (xs.map (fun a => if p (a,e) then [a] else [])).flatten=xs.filter (fun a => p (a,e)) := by
   induction xs with
   | nil => rfl
   | cons a xs ih => cases hp : p (a,e) <;> simp [hp,ih]
 def filterEnvironment {p : α×γ → Bool} (P : Realizer p) :
     Realizer (fun x : List α×γ => x.1.filter (fun a => p (a,x.2))) :=
   ((mapEnvironment (selectSingleton P)).comp flattenList).congr (fun x => filter_flatten p x.1 x.2)
 theorem filterEnvironment_polynomial {p : α×γ → Bool} {P : Realizer p} (hP : PolyBound P) : PolyBound (filterEnvironment P) := by
   unfold filterEnvironment
   apply polynomial_congr
   exact polynomial_comp (polynomial_mapEnvironment (selectSingleton_polynomial hP)) flattenList_polynomial

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.ListAccessCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RawStack
variable {α : Type} [Coding α]

 def tailList : Realizer (fun L : List α => L.tail) := (Uniform.tail (I:=Unit) (α:=fun _ => α)).specialize ()
 theorem tailList_linear : Linear (tailList (α:=α)) := by
   refine linear_of _ 3 (by omega) (fun L => by change volume L+2≤ _; omega) ?_
   intro L
   cases L with
   | nil => simp
   | cons a L => simp only [List.tail_cons,volume_cons]; omega
 theorem tailList_volume (L : List α) : volume L.tail≤ volume L := by
   cases L with
   | nil => rfl
   | cons a L => simp only [List.tail_cons,volume_cons]; omega
 theorem tail_iterate (L : List α) (k : ℕ) : List.tail^[k] L=L.drop k := by
   induction k with
   | zero => rfl
   | succ k ih => rw [Function.iterate_succ_apply',ih,List.tail_drop]
 def dropList : Realizer (fun x : List α×ℕ => x.1.drop x.2) :=
   ((Realizer.snd.pair Realizer.fst).comp tailList.iterate).congr (fun x => by
     change List.tail^[x.2] x.1=x.1.drop x.2
     exact tail_iterate _ _)
 theorem dropList_polynomial : PolyBound (dropList (α:=α)) := by
   unfold dropList
   apply polynomial_congr
   exact polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst))
     (polynomial_iterate (linear_polynomial tailList_linear) 0 (fun L => by simpa only [Nat.add_zero] using tailList_volume L))

 def headNat : Realizer (fun L : List ℕ => L.headD 0) where
   transform := Data.head
   charge := fun x => x.size+2
   routine := Routine.select true
   correct L := by cases L <;> rfl
 theorem headNat_linear : Linear headNat := by
   refine linear_of _ 3 (by omega) (fun L => by change volume L+2≤ _; omega) ?_
   intro L
   cases L with
   | nil => simp
   | cons a L => simp only [List.headD_cons,volume_cons]; omega
 def lookupNat : Realizer (fun x : List ℕ×ℕ => (x.1.drop x.2).headD 0) := dropList.comp headNat
 theorem lookupNat_polynomial : PolyBound lookupNat := polynomial_comp dropList_polynomial (linear_polynomial headNat_linear)
 def lookupBool : Realizer (fun x : List Bool×ℕ => (x.1.drop x.2).headD false) := dropList.comp BinaryAdder.headBit
 theorem lookupBool_polynomial : PolyBound lookupBool := polynomial_comp dropList_polynomial (linear_polynomial BinaryAdder.headBit_linear)

 def countStep : Realizer (fun x : α×ℕ => x.2+1) := Realizer.snd.comp Realizer.succ
 theorem count_fold (L : List α) (k : ℕ) : L.foldl (fun k (_ : α) => k+1) k=k+L.length := by
   induction L generalizing k with
   | nil => simp
   | cons a L ih => rw [List.foldl_cons,ih,List.length_cons]; omega
 theorem countStep_fold_polynomial : PolyBound (countStep (α:=α)).fold := by
   apply polynomial_fold_bounded (linear_polynomial (linear_comp linear_snd succ_linear)) 3
   intro L k j hj
   dsimp only [Function.comp_apply]
   rw [count_fold]
   have hlen := length_volume L
   simp only [volume_nat,volume_pair,List.length_take]
   omega
 def listLength : Realizer (fun L : List α => L.length) :=
   ((Realizer.id.pair (Realizer.constant 0)).comp countStep.fold).congr (fun L => by
     change L.foldl (fun k (_ : α) => k+1) 0=L.length
     simp only [count_fold,Nat.zero_add])
 theorem listLength_polynomial : PolyBound (listLength (α:=α)) := by
   unfold listLength
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial (linear_constant (0 : ℕ)))) countStep_fold_polynomial

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.DecodeWordList
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def decodeWordsRealizer : Realizer (fun xs : List (List Bool) => xs.map value) := mapList valueRealizer
 theorem natList_volume (xs : List ℕ) : volume xs=2*xs.sum+2*xs.length+1 := by
   induction xs with
   | nil => simp
   | cons a xs ih => simp only [volume_cons,volume_nat,List.sum_cons,List.length_cons,ih]; ring
 theorem value_le_sum (xs : List (List Bool)) (a : List Bool) (ha : a∈xs) : value a≤(xs.map value).sum := by
   induction xs with
   | nil => simp at ha
   | cons b xs ih =>
     simp only [List.mem_cons] at ha
     simp only [List.map_cons,List.sum_cons]
     rcases ha with rfl|ha
     · omega
     · exact (ih ha).trans (by omega)
 theorem decodeWords_time : ∃ C q : ℕ,0< C ∧ ∀xs : List (List Bool),
     decodeWordsRealizer.time xs≤ C*(volume xs+(xs.map value).sum+1)^q := by
   obtain ⟨C,q,hC,hR⟩ := value_time
   refine ⟨30000*(C+40)+200,q+2,by positivity,?_⟩
   intro xs
   let z := volume xs+(xs.map value).sum+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hlen := length_volume xs
   have hlenz : xs.length+1≤ z := by dsimp [z]; omega
   have hvolz : volume xs≤ z := by dsimp [z]; omega
   have hout : volume (xs.map value)≤3*z := by rw [natList_volume,List.length_map]; dsimp [z]; omega
   have hze : z≤ z^(q+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+1)
   have hq : z^q≤ z^(q+1) := Nat.pow_le_pow_right hz (by omega)
   let R := (Realizer.fst : Realizer (Prod.fst : List Bool×Unit → List Bool)).comp valueRealizer
   have hT (a : List Bool) (ha : a∈xs) : R.time (a,())≤(C+30)*z^(q+1) := by
     have hva := volume_mem_le ha
     have hla := bits_length_volume a
     have hvalue := value_le_sum xs a ha
     have hbase : value a+a.length+1≤ z := by dsimp [z]; omega
     have ht := (hR a).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
     have ht := ht.trans (Nat.mul_le_mul_left C hq)
     dsimp only [R]
     rw [Realizer.time_comp,Realizer.time_fst]
     simp only [volume_pair,volume_unit]
     nlinarith only [ht,hva,hvolz,hze,hz]
   have ht := Uniform.time_map (R.uniform Unit) () xs () ((C+30)*z^(q+1)) hT
   rw [Nat.mul_assoc] at ht
   have hm := Nat.mul_le_mul_left 30000 (Nat.mul_le_mul hlenz
     (show (C+30)*z^(q+1)+volume xs+volume ()+volume (xs.map (fun a => value a))+1≤(C+40)*z^(q+1) by
       simp only [volume_unit]; nlinarith only [hout,hvolz,hze,hz]))
   have he : 30000*(z*((C+40)*z^(q+1)))=30000*(C+40)*z^(q+2) := by rw [pow_succ]; ring
   rw [he] at hm
   have hmap : (mapEnvironment R).time (xs,())≤30000*(C+40)*z^(q+2) := by
     rw [mapEnvironment_time]
     exact ht.trans hm
   have hze2 : z≤ z^(q+2) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+2)
   have heq : decodeWordsRealizer.time xs=(mapEnvironment R).time (xs,())+51*volume xs+74 := by
     dsimp only [decodeWordsRealizer,mapList]
     simp only [Realizer.time_congr,Realizer.time_comp,Realizer.time_pair,Realizer.time_id,volume_pair,volume_unit,Function.comp_apply]
     change volume xs+2+2+20*(volume xs+volume xs+1+1)+(mapEnvironment R).time (xs,())+10*(volume xs+1+1+1)=_
     ring
   rw [heq]
   change _≤(30000*(C+40)+200)*z^(q+2)
   nlinarith only [hmap,hvolz,hze2,hz]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OwnerIndices
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def ownerBlock (x : ℕ×List ℕ) : List ℕ := List.replicate ((x.2.drop x.1).headD 0) x.1
 def ownerBlockRealizer : Realizer ownerBlock :=
   (((Realizer.snd.pair Realizer.fst).comp lookupNat).pair Realizer.fst).comp replicateList
 theorem ownerBlock_polynomial : PolyBound ownerBlockRealizer :=
   polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) lookupNat_polynomial)
     (linear_polynomial linear_fst)) replicateList_polynomial
 def ownerIndices (counts : List ℕ) : List ℕ :=
   ((List.range counts.length).map (fun i => ownerBlock (i,counts))).flatten
 def ownerIndicesRealizer : Realizer ownerIndices :=
   ((((listLength.comp Realizer.range).pair Realizer.id).comp (mapEnvironment ownerBlockRealizer)).comp flattenList)
 theorem ownerIndices_polynomial : PolyBound ownerIndicesRealizer :=
   polynomial_comp (polynomial_comp (polynomial_pair (polynomial_comp listLength_polynomial range_polynomial)
     (linear_polynomial linear_id)) (polynomial_mapEnvironment ownerBlock_polynomial)) flattenList_polynomial

 theorem lookup_ofFn {n : ℕ} (t : Fin n → ℕ) (i : Fin n) : ((List.ofFn t).drop i.val).headD 0=t i := by
   rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn]
   simp [i.isLt]
 theorem map_range_ofFn {α : Type} (n : ℕ) (f : ℕ → α) : (List.range n).map f=List.ofFn (fun i : Fin n => f i.val) := by
   rw [← finRange_val n,List.map_map]
   simp only [List.finRange,List.map_ofFn,Function.comp_def,id_eq]
 theorem ownerIndices_ofFn {n : ℕ} (t : Fin n → ℕ) :
     ownerIndices (List.ofFn t)=(List.finRange n).flatMap (fun v => List.replicate (t v) v.val) := by
   dsimp only [ownerIndices]
   rw [List.length_ofFn,map_range_ofFn]
   have he : (fun i : Fin n => ownerBlock (i.val,List.ofFn t))=(fun i : Fin n => List.replicate (t i) i.val) := by
     funext i
     dsimp only [ownerBlock]
     rw [lookup_ofFn]
   rw [he]
   simp only [List.flatMap_def,List.finRange,List.map_ofFn,Function.comp_def,id_eq]
 theorem ownerIndices_length {n : ℕ} (t : Fin n → ℕ) : (ownerIndices (List.ofFn t)).length=totalCopies t := by
   rw [ownerIndices_ofFn]
   simp [List.length_flatMap,List.finRange,List.map_ofFn,List.sum_ofFn,totalCopies]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.WeightedHelpers
noncomputable section

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.WeightedHelpers

 def beforeCount {n : ℕ} (t : Fin n → ℕ) (v : Fin n) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u => u < v), t u

 theorem beforeCount_add {n : ℕ} (t : Fin n → ℕ) (v : Fin n) :
    beforeCount t v + t v = ∑ u ∈ Finset.univ.filter (fun u => u ≤ v), t u := by
  classical
  have hset : Finset.univ.filter (fun u : Fin n => u ≤ v) =
      insert v (Finset.univ.filter (fun u : Fin n => u < v)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    exact le_iff_lt_or_eq.trans or_comm
  rw [hset, Finset.sum_insert (by simp)]
  exact Nat.add_comm _ _

 theorem beforeCount_le_total {n : ℕ} (t : Fin n → ℕ) (v : Fin n) :
    beforeCount t v + t v ≤ totalCopies t := by
  classical
  rw [beforeCount_add]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

 theorem cumulative_le_beforeCount {n : ℕ} (t : Fin n → ℕ) {u v : Fin n} (huv : u < v) :
    (∑ x ∈ Finset.univ.filter (fun x => x ≤ u), t x) ≤ beforeCount t v := by
  classical
  apply Finset.sum_le_sum_of_subset
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact lt_of_le_of_lt hx huv

 theorem owner_of_interval {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t))
    (v : Fin n) (lo : beforeCount t v ≤ j.val) (hi : j.val < beforeCount t v + t v) :
    copyOwner t j = some v := by
  classical
  unfold copyOwner
  rw [show List.finRange n = List.ofFn (fun v : Fin n => v) from rfl]
  apply (List.find?_ofFn_eq_some_of_injective (Function.injective_id)).mpr
  refine ⟨?_, ?_⟩
  · simpa only [id_eq, decide_eq_true_eq, ← beforeCount_add] using hi
  · intro u huv
    simp only [decide_eq_true_eq, not_lt]
    exact (cumulative_le_beforeCount t huv).trans lo

 theorem owner_interval {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t))
    (v : Fin n) (h : copyOwner t j = some v) :
    beforeCount t v ≤ j.val ∧ j.val < beforeCount t v + t v := by
  classical
  unfold copyOwner at h
  rw [show List.finRange n = List.ofFn (fun v : Fin n => v) from rfl] at h
  have hh := (List.find?_ofFn_eq_some_of_injective (Function.injective_id)).mp h
  simp only [id_eq] at hh
  have hi : j.val < beforeCount t v + t v := by
    simpa only [decide_eq_true_eq, ← beforeCount_add] using hh.1
  refine ⟨?_, hi⟩
  by_cases hz : v.val = 0
  · have hv : ∀ u : Fin n, ¬ u < v := by intro u; simp only [Fin.lt_def]; omega
    simp [beforeCount, hv]
  · let u : Fin n := ⟨v.val - 1, by omega⟩
    have huv : u < v := by simp only [Fin.lt_def]; dsimp [u]; omega
    have hu := hh.2 u huv
    simp only [decide_eq_true_eq, not_lt] at hu
    have hset : Finset.univ.filter (fun x : Fin n => x ≤ u) =
        Finset.univ.filter (fun x : Fin n => x < v) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val,
        Fin.lt_def]
      dsimp [u]
      omega
    simpa [hset, beforeCount] using hu

 def copyIndex {n : ℕ} (t : Fin n → ℕ) (v : Fin n) (i : Fin (t v)) :
    Fin (totalCopies t) :=
  ⟨beforeCount t v + i.val, (Nat.add_lt_add_left i.isLt _).trans_le (beforeCount_le_total t v)⟩

 theorem owner_copyIndex {n : ℕ} (t : Fin n → ℕ) (v : Fin n) (i : Fin (t v)) :
    copyOwner t (copyIndex t v i) = some v := by
  apply owner_of_interval
  · exact Nat.le_add_right _ _
  · exact Nat.add_lt_add_left i.isLt _

 theorem owner_exists {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t)) :
    ∃ v, copyOwner t j = some v := by
  classical
  by_contra h
  have hnone : copyOwner t j = none := by
    cases he : copyOwner t j with
    | none => rfl
    | some v => exact False.elim (h ⟨v, he⟩)
  unfold copyOwner at hnone
  have hf := List.find?_eq_none.mp hnone
  by_cases hn : n = 0
  · subst n
    have hz : totalCopies t = 0 := by simp [totalCopies]
    have := j.isLt
    omega
  · let v : Fin n := ⟨n-1, by omega⟩
    have hp := hf v (by simp)
    simp only [decide_eq_true_eq, not_lt] at hp
    have heq : Finset.univ.filter (fun u : Fin n => u ≤ v) = Finset.univ := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val]
      dsimp [v]
      have hu := u.isLt
      exact iff_true_intro (Nat.le_pred_of_lt u.isLt)
    rw [heq] at hp
    exact Nat.not_le_of_lt j.isLt hp

noncomputable def fiberEquiv {n : ℕ} (t : Fin n → ℕ) (v : Fin n) :
    {j : Fin (totalCopies t) // copyOwner t j = some v} ≃ Fin (t v) where
  toFun j := ⟨j.val.val - beforeCount t v, by
    have h := owner_interval t j.val v j.property
    omega⟩
  invFun i := ⟨copyIndex t v i, owner_copyIndex t v i⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    dsimp [copyIndex]
    have h := (owner_interval t j.val v j.property).1
    omega
  right_inv i := by
    apply Fin.ext
    simp [copyIndex]

 theorem fiber_card {n : ℕ} (t : Fin n → ℕ) (v : Fin n) :
    (Finset.univ.filter (fun j => copyOwner t j = some v)).card = t v := by
  classical
  simpa only [Fintype.card_coe, Fintype.card_fin, Finset.card_univ, Fintype.card_subtype]
    using Fintype.card_congr (fiberEquiv t v)

 theorem max_weight_le {n : ℕ} (w : Fin n → ℚ) (v : Fin n) :
    w v ≤ maximumWeight w := by
  have hne : List.ofFn w ≠ [] := List.ne_nil_of_mem (List.mem_ofFn.mpr ⟨v, rfl⟩)
  unfold maximumWeight
  rw [List.foldl_max_eq_max hne]
  exact (List.le_max_of_mem (List.mem_ofFn.mpr ⟨v, rfl⟩)).trans (le_max_right _ _)

 theorem max_weight_attained {n : ℕ} (w : Fin n → ℚ) (hpos : 0 < maximumWeight w) :
    ∃ v, maximumWeight w = w v := by
  have hne : List.ofFn w ≠ [] := by
    intro h
    have : maximumWeight w = 0 := by simp [maximumWeight, h]
    linarith
  have hEq : maximumWeight w = (List.ofFn w).max hne := by
    unfold maximumWeight at *
    rw [List.foldl_max_eq_max hne] at *
    exact max_eq_right (by by_contra h; rw [max_eq_left (le_of_not_ge h)] at hpos; linarith)
  have hmem := List.max_mem hne
  obtain ⟨v, hv⟩ := List.mem_ofFn.mp hmem
  exact ⟨v, hEq.trans hv.symm⟩

 theorem weightedAlpha_bdd {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (w : Fin n → ℚ) : BddAbove {z : ℝ | ∃ I ⊆ W, G.IsIndepSet (I : Set (Fin n)) ∧
      z = ∑ v ∈ I, (w v : ℝ)} := by
  classical
  apply (Set.finite_range (fun I : Finset (Fin n) => ∑ v ∈ I, (w v : ℝ))).bddAbove.mono
  rintro z ⟨I, hI, hi, rfl⟩
  exact Set.mem_range_self _

 theorem weightedAlpha_member {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (w : Fin n → ℚ) (I : Finset (Fin n)) (hI : I ⊆ W) (hind : G.IsIndepSet (I : Set (Fin n))) :
    (∑ v ∈ I, (w v : ℝ)) ≤ weightedAlphaOn G W w := by
  exact le_csSup (weightedAlpha_bdd G W w) ⟨I, hI, hind, rfl⟩

 theorem weightedAlpha_attained {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (w : Fin n → ℚ) : ∃ I ⊆ W, G.IsIndepSet (I : Set (Fin n)) ∧
      weightedAlphaOn G W w = ∑ v ∈ I, (w v : ℝ) := by
  classical
  let S := {z : ℝ | ∃ I ⊆ W, G.IsIndepSet (I : Set (Fin n)) ∧ z = ∑ v ∈ I, (w v : ℝ)}
  have hne : S.Nonempty := by
    refine ⟨0, ∅, Finset.empty_subset _, ?_, by simp⟩
    simp
  have hfin : S.Finite := by
    apply (Set.finite_range (fun I : Finset (Fin n) => ∑ v ∈ I, (w v : ℝ))).subset
    rintro z ⟨I, hI, hi, rfl⟩
    exact Set.mem_range_self _
  exact hne.csSup_mem hfin

noncomputable def owner {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t)) : Fin n :=
  Classical.choose (owner_exists t j)

 theorem owner_spec {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t)) :
    copyOwner t j = some (owner t j) := Classical.choose_spec (owner_exists t j)

 theorem owner_eq_iff {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t)) (v : Fin n) :
    owner t j = v ↔ copyOwner t j = some v := by
  rw [owner_spec, Option.some.injEq]

 theorem owner_fiber_card {n : ℕ} (t : Fin n → ℕ) (v : Fin n) :
    (Finset.univ.filter (fun j => owner t j = v)).card = t v := by
  classical
  simp only [owner_eq_iff]
  exact fiber_card t v

 theorem rounded_adj_iff {n : ℕ} (G : SimpleGraph (Fin n)) (t : Fin n → ℕ)
    (i j : Fin (totalCopies t)) :
    (roundedGraph G t).Adj i j ↔ G.Adj (owner t i) (owner t j) := by
  constructor
  · rintro ⟨u, v, hu, hv, hadj⟩
    rw [← (owner_eq_iff t i u).mpr hu, ← (owner_eq_iff t j v).mpr hv] at hadj
    exact hadj
  · intro h
    exact ⟨owner t i, owner t j, owner_spec t i, owner_spec t j, h⟩

 theorem lift_card {n : ℕ} (t : Fin n → ℕ) (I : Finset (Fin n)) :
    (Finset.univ.filter (fun j => owner t j ∈ I)).card = ∑ v ∈ I, t v := by
  classical
  rw [← Finset.sum_card_fiberwise_eq_card_filter]
  exact Finset.sum_congr rfl (fun v hv => owner_fiber_card t v)

 theorem lift_independent {n : ℕ} (G : SimpleGraph (Fin n)) (t : Fin n → ℕ)
    (I : Finset (Fin n)) (hind : G.IsIndepSet (I : Set (Fin n))) :
    (roundedGraph G t).IsIndepSet (Finset.univ.filter (fun j => owner t j ∈ I) : Set (Fin (totalCopies t))) := by
  rw [SimpleGraph.isIndepSet_iff] at hind ⊢
  intro i hi j hj hij hadj
  have h := (rounded_adj_iff G t i j).mp hadj
  exact hind (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 (G.ne_of_adj h) h

 theorem alpha_lift_bound {n : ℕ} (G : SimpleGraph (Fin n)) (t : Fin n → ℕ)
    (I : Finset (Fin n)) (hind : G.IsIndepSet (I : Set (Fin n))) :
    ∑ v ∈ I, t v ≤ alpha (roundedGraph G t) Finset.univ := by
  classical
  rw [← lift_card]
  unfold alpha
  apply Finset.le_sup
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.subset_univ _, lift_independent G t I hind⟩

 theorem originalVertices_eq {n : ℕ} (t : Fin n → ℕ)
    (I : Finset (Fin (totalCopies t))) : originalVertices t I = I.image (owner t) := by
  classical
  ext v
  simp only [originalVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image, owner_eq_iff]

 theorem projection_independent {n : ℕ} (G : SimpleGraph (Fin n)) (t : Fin n → ℕ)
    (I : Finset (Fin (totalCopies t)))
    (hind : (roundedGraph G t).IsIndepSet (I : Set (Fin (totalCopies t)))) :
    G.IsIndepSet (originalVertices t I : Set (Fin n)) := by
  rw [SimpleGraph.isIndepSet_iff] at hind ⊢
  intro u hu v hv huv hadj
  rw [originalVertices_eq] at hu hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
  have h := (rounded_adj_iff G t i j).mpr hadj
  exact hind hi hj ((roundedGraph G t).ne_of_adj h) h

 theorem projection_card_bound {n : ℕ} (t : Fin n → ℕ)
    (I : Finset (Fin (totalCopies t))) : I.card ≤ ∑ v ∈ originalVertices t I, t v := by
  classical
  rw [originalVertices_eq, Finset.card_eq_sum_card_image (owner t) I]
  apply Finset.sum_le_sum
  intro v hv
  rw [← owner_fiber_card t v]
  exact Finset.card_le_card (by intro j hj; simp_all only [Finset.mem_filter, Finset.mem_univ, true_and])

 theorem maximumWeight_le_alpha {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (hpos : 0 < maximumWeight w) : (maximumWeight w : ℝ) ≤ weightedAlpha G w := by
  classical
  obtain ⟨v, hv⟩ := max_weight_attained w hpos
  rw [hv]
  have h := weightedAlpha_member G Finset.univ w {v} (Finset.subset_univ _) (by simp)
  simpa [weightedAlpha] using h

 theorem owner_positive {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t)) :
    0 < t (owner t j) := by
  have h := owner_interval t j (owner t j) (owner_spec t j)
  omega

 theorem rounded_mem_blowup {n : ℕ} (C : GraphClass) (G : SimpleGraph (Fin n))
    (hC : Hereditary C) (hG : C n G) (t : Fin n → ℕ) :
    BlowupClass C (totalCopies t) (roundedGraph G t) := by
  classical
  let V := {v : Fin n // 0 < t v}
  let m := Fintype.card V
  let e : V ≃ Fin m := Fintype.equivFin V
  let inc : Fin m ↪ Fin n :=
    ⟨fun v => (e.symm v).val, (Subtype.val_injective.comp e.symm.injective)⟩
  let H : SimpleGraph (Fin m) := G.comap inc
  have hH : C m H := hC G H inc hG (fun u v => Iff.rfl)
  let f : Fin (totalCopies t) → Fin m := fun j => e ⟨owner t j, owner_positive t j⟩
  refine ⟨m, H, hH, f, ?_, ?_⟩
  · intro v
    let u : V := e.symm v
    let j := copyIndex t u.val ⟨0, u.property⟩
    have hj : owner t j = u.val := (owner_eq_iff t j u.val).mpr (owner_copyIndex t u.val ⟨0, u.property⟩)
    refine ⟨j, ?_⟩
    dsimp [f]
    have hh : (⟨owner t j, owner_positive t j⟩ : V) = u := Subtype.ext hj
    rw [hh]
    exact e.apply_symm_apply v
  · intro i j
    change (roundedGraph G t).Adj i j ↔ G.Adj (inc (f i)) (inc (f j))
    simp only [inc, f, Equiv.symm_apply_apply, Function.Embedding.coeFn_mk]
    exact rounded_adj_iff G t i j

end EdgeSublinearMWIS.Main.WeightedHelpers
end

-- Solutions.OwnerSemantics
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open WeightedHelpers

 theorem sum_map_toFinset {α : Type} [DecidableEq α] (L : List α) (hL : L.Nodup) (f : α → ℕ) :
     (L.map f).sum=∑a∈L.toFinset,f a := by
   induction L with
   | nil => simp
   | cons a L ih =>
     have hh := List.nodup_cons.mp hL
     simp only [List.map_cons,List.sum_cons,List.toFinset_cons]
     rw [Finset.sum_insert (by simpa using hh.1),← ih hh.2]

 theorem prefix_vertices {n : ℕ} (v : Fin n) :
     ((List.finRange n).take v.val).toFinset=Finset.univ.filter (fun u => u< v) := by
   ext u
   simp only [List.mem_toFinset,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_take_iff_getElem]
   constructor
   · rintro ⟨j,hj,he⟩
     have hjv : j< v.val := lt_of_lt_of_le hj (Nat.min_le_left _ _)
     have hju : j=u.val := by simpa only [List.getElem_finRange,Fin.val_cast,Fin.val_mk] using congrArg Fin.val he
     change u.val< v.val
     omega
   · intro huv
     refine ⟨u.val,?_,?_⟩
     · simp only [List.length_finRange,lt_min_iff]
       exact ⟨huv,u.isLt⟩
     · simp only [List.getElem_finRange]
       apply Fin.ext
       rfl
 theorem prefix_block_length {n : ℕ} (t : Fin n → ℕ) (v : Fin n) :
     (((List.finRange n).take v.val).flatMap (fun u => List.replicate (t u) u.val)).length=beforeCount t v := by
   rw [List.length_flatMap]
   simp only [List.length_replicate]
   rw [sum_map_toFinset _ ((List.nodup_finRange n).sublist (List.take_sublist _ _)),prefix_vertices]
   rfl
 theorem finRange_split {n : ℕ} (v : Fin n) :
     List.finRange n=(List.finRange n).take v.val++v::(List.finRange n).drop (v.val+1) := by
   have he := List.take_append_drop v.val (List.finRange n)
   have hd := List.drop_eq_getElem_cons (by simpa using v.isLt : v.val<(List.finRange n).length)
   have hv : (List.finRange n)[v.val]=v := by simp only [List.getElem_finRange]; apply Fin.ext; rfl
   rw [hd,hv] at he
   exact he.symm

 theorem ownerIndices_get_interval {n : ℕ} (t : Fin n → ℕ) (v : Fin n) (j : ℕ)
     (hlo : beforeCount t v≤ j) (hhi : j< beforeCount t v+t v) :
     (ownerIndices (List.ofFn t))[j]?=some v.val := by
   rw [ownerIndices_ofFn,finRange_split v,List.flatMap_append,List.flatMap_cons]
   rw [List.getElem?_append_right (by rw [prefix_block_length]; exact hlo)]
   rw [prefix_block_length,List.getElem?_append_left (by simp only [List.length_replicate]; omega),List.getElem?_replicate,if_pos (by omega)]
 theorem ownerIndices_lookup {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t)) :
     ((ownerIndices (List.ofFn t)).drop j.val).headD 0=(owner t j).val := by
   have hi := owner_interval t j (owner t j) (owner_spec t j)
   rw [List.headD_eq_head?_getD,List.head?_drop,ownerIndices_get_interval t (owner t j) j.val hi.1 hi.2,Option.getD_some]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.VertexPairCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def ltNatRealizer : Realizer (fun x : ℕ×ℕ => decide (x.1< x.2)) :=
   (((Realizer.snd.pair Realizer.fst).comp Realizer.le).comp Realizer.not).congr (fun x => by
     dsimp only [Function.comp_apply]
     by_cases h : x.1< x.2
     · have hn : ¬x.2≤ x.1 := by omega
       simp [h,hn]
     · have hn : x.2≤ x.1 := by omega
       simp [h,hn])
 theorem ltNat_polynomial : PolyBound ltNatRealizer := by
   unfold ltNatRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) nat_le_polynomial) (linear_polynomial linear_not)
 def upperRow (u n : ℕ) : List (ℕ×ℕ) := ((List.range n).filter (fun v => u< v)).map (fun v => (u,v))
 def largerRealizer : Realizer (fun x : ℕ×ℕ => decide (x.2< x.1)) := (Realizer.snd.pair Realizer.fst).comp ltNatRealizer
 def upperColumns : Realizer (fun x : ℕ×ℕ => (List.range x.2).filter (fun v => x.1< v)) :=
   (((Realizer.snd.comp Realizer.range).pair Realizer.fst).comp (filterEnvironment largerRealizer))
 def upperRowRealizer : Realizer (fun x : ℕ×ℕ => upperRow x.1 x.2) :=
   ((upperColumns.pair Realizer.fst).comp (mapEnvironment (Realizer.snd.pair Realizer.fst)))
 theorem upperRow_polynomial : PolyBound upperRowRealizer := by
   have hc : PolyBound upperColumns := polynomial_comp
     (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) range_polynomial) (linear_polynomial linear_fst))
     (filterEnvironment_polynomial (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) ltNat_polynomial))
   exact polynomial_comp (polynomial_pair hc (linear_polynomial linear_fst))
     (polynomial_mapEnvironment (linear_polynomial (linear_pair linear_snd linear_fst)))
 def vertexPairs (n : ℕ) : List (ℕ×ℕ) := (List.range n).flatMap (fun u => upperRow u n)
 def vertexPairsRealizer : Realizer vertexPairs :=
   ((((Realizer.range.pair Realizer.id).comp (mapEnvironment upperRowRealizer)).comp flattenList))
 theorem vertexPairs_polynomial : PolyBound vertexPairsRealizer :=
   polynomial_comp (polynomial_comp (polynomial_pair range_polynomial (linear_polynomial linear_id))
     (polynomial_mapEnvironment upperRow_polynomial)) flattenList_polynomial

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ZipBitsCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
variable {α : Type} [Coding α]

 def zipBitsStep (s : α×(List Bool×List (α×Bool))) : List Bool×List (α×Bool) :=
   (s.2.1.tail,(s.1,s.2.1.headD false)::s.2.2)
 def zipBitsStepRealizer : Realizer (zipBitsStep (α:=α)) :=
   (((Realizer.snd.comp Realizer.fst).comp BinaryAdder.tailBits).pair
     ((Realizer.fst.pair ((Realizer.snd.comp Realizer.fst).comp BinaryAdder.headBit)).pair (Realizer.snd.comp Realizer.snd) |>.comp Realizer.cons))
 theorem zipBitsStep_linear : Linear (zipBitsStepRealizer (α:=α)) :=
   linear_pair (linear_comp (linear_comp linear_snd linear_fst) BinaryAdder.tailBits_linear)
     (linear_comp (linear_pair (linear_pair linear_fst (linear_comp (linear_comp linear_snd linear_fst) BinaryAdder.headBit_linear))
       (linear_comp linear_snd linear_snd)) linear_cons)
 theorem zipBitsFold_volume (L : List α) (bits : List Bool) (acc : List (α×Bool)) :
     volume (L.foldl (fun s a => zipBitsStep (a,s)) (bits,acc))≤ volume (bits,acc)+volume L+4*L.length := by
   induction L generalizing bits acc with
   | nil => simp
   | cons a L ih =>
     rw [List.foldl_cons]
     have ht : volume bits.tail≤ volume bits := tailList_volume bits
     have hb := volume_bool (bits.headD false)
     have hh := ih bits.tail ((a,bits.headD false)::acc)
     dsimp only [zipBitsStep] at hh ⊢
     simp only [volume_pair,volume_cons,List.length_cons] at hh ⊢
     omega
 theorem zipBits_fold_polynomial : PolyBound (zipBitsStepRealizer (α:=α)).fold := by
   apply polynomial_fold_bounded (linear_polynomial zipBitsStep_linear) 5
   intro keys ⟨bits,acc⟩ j hj
   have hh := zipBitsFold_volume (keys.take j) bits acc
   have ht := take_volume_le keys j
   have hlen := length_volume keys
   simp only [List.length_take] at hh
   simp only [volume_pair]
   simp only [volume_pair] at hh
   omega
 def zipBits (L : List α) (bits : List Bool) : List (α×Bool) :=
   ((L.foldl (fun s a => zipBitsStep (a,s)) (bits,[])).2).reverse
 def zipBitsRealizer : Realizer (fun s : List α×List Bool => zipBits s.1 s.2) :=
   (((Realizer.fst.pair (Realizer.snd.pair Realizer.nil)).comp zipBitsStepRealizer.fold).comp (Realizer.snd.comp Realizer.reverse))
 theorem zipBits_polynomial : PolyBound (zipBitsRealizer (α:=α)) := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : List α×List Bool => ([] : List (α×Bool)))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   exact polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_fst)
     (polynomial_pair (linear_polynomial linear_snd) (linear_polynomial hn))) zipBits_fold_polynomial)
     (polynomial_comp (linear_polynomial linear_snd) reverse_polynomial_generic)
 theorem zipBitsFold_map (L : List α) (f : α → Bool) (acc : List (α×Bool)) :
     L.foldl (fun s a => zipBitsStep (a,s)) (L.map f,acc)=([],(L.map (fun a => (a,f a))).reverse++acc) := by
   induction L generalizing acc with
   | nil => rfl
   | cons a L ih =>
     rw [List.map_cons,List.foldl_cons]
     change L.foldl (fun s a => zipBitsStep (a,s)) (L.map f,(a,f a)::acc)=_
     rw [ih,List.map_cons,List.reverse_cons]
     simp only [List.append_assoc,List.singleton_append]
 theorem zipBits_map (L : List α) (f : α → Bool) : zipBits L (L.map f)=L.map (fun a => (a,f a)) := by
   rw [zipBits,zipBitsFold_map]
   simp

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
variable {α : Type} [OAI.ThreeMachine.StackCompiler.Coding α]
 theorem zipBitsFold_map_append (L : List α) (f : α → Bool) (rest : List Bool) (acc : List (α×Bool)) :
     L.foldl (fun s a => zipBitsStep (a,s)) (L.map f++rest,acc)=(rest,(L.map (fun a => (a,f a))).reverse++acc) := by
   induction L generalizing acc with
   | nil => rfl
   | cons a L ih =>
     rw [List.map_cons,List.cons_append,List.foldl_cons]
     change L.foldl (fun s a => zipBitsStep (a,s)) (L.map f++rest,(a,f a)::acc)=_
     rw [ih,List.map_cons,List.reverse_cons]
     simp only [List.append_assoc,List.singleton_append]
 theorem zipBits_map_append (L : List α) (f : α → Bool) (rest : List Bool) :
     zipBits L (L.map f++rest)=L.map (fun a => (a,f a)) := by
   rw [zipBits,zipBitsFold_map_append]
   simp
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.AdjacencyTableCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem eqNat_polynomial : PolyBound Realizer.eqNat := by
   refine ⟨10000000001,2,by omega,?_⟩
   rintro ⟨a,b⟩
   have ht := Realizer.time_eqNat_le a b
   have hbase : a+b+1≤ volume (a,b)+1 := by simp only [volume_pair,volume_nat]; omega
   have hp := Nat.pow_le_pow_left hbase 2
   have hv := volume_bool (decide (a=b))
   have hz : 1≤(volume (a,b)+1)^2 := one_le_pow₀ (by omega)
   constructor
   · exact ht.trans ((Nat.mul_le_mul_left 10000000000 hp).trans (Nat.mul_le_mul_right _ (by omega)))
   · change volume (decide (a=b))≤ _
     omega
 abbrev Key := ℕ×ℕ
 abbrev Entry := Key×Bool
 def tableTest (s : Entry×Key) : Bool := decide (s.1.1=s.2)
 def entryKey : Realizer (fun s : Entry×Key => s.1.1) := Realizer.fst.comp Realizer.fst
 def tableTestRealizer : Realizer tableTest :=
   (((((entryKey.comp Realizer.fst).pair (Realizer.snd.comp Realizer.fst)).comp Realizer.eqNat).pair
     (((entryKey.comp Realizer.snd).pair (Realizer.snd.comp Realizer.snd)).comp Realizer.eqNat)).comp Realizer.and).congr
     (fun s => by
       dsimp only [Function.comp_apply,tableTest]
       by_cases h : s.1.1.1=s.2.1 <;> by_cases k : s.1.1.2=s.2.2 <;> simp [Prod.ext_iff,h,k])
 theorem tableTest_polynomial : PolyBound tableTestRealizer := by
   have hk : Linear entryKey := linear_comp linear_fst linear_fst
   unfold tableTestRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp hk linear_fst) (linear_comp linear_snd linear_fst))) eqNat_polynomial)
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp hk linear_snd) (linear_comp linear_snd linear_snd))) eqNat_polynomial))
     (linear_polynomial linear_and)
 def tableLookup (entries : List Entry) (key : Key) : Bool :=
   ((entries.filter (fun e => decide (e.1=key))).map Prod.snd).headD false
 def tableLookupRealizer : Realizer (fun s : List Entry×Key => tableLookup s.1 s.2) :=
   (((filterEnvironment tableTestRealizer).comp (mapList Realizer.snd)).comp BinaryAdder.headBit)
 theorem tableLookup_polynomial : PolyBound tableLookupRealizer :=
   polynomial_comp (polynomial_comp (filterEnvironment_polynomial tableTest_polynomial)
     (polynomial_mapList (linear_polynomial linear_snd))) (linear_polynomial BinaryAdder.headBit_linear)
 theorem tableLookup_map (keys : List Key) (f : Key → Bool) (key : Key) (hk : key∈keys) :
     tableLookup (keys.map (fun k => (k,f k))) key=f key := by
   induction keys with
   | nil => simp at hk
   | cons a keys ih =>
     by_cases h : a=key
     · subst a; simp [tableLookup]
     · have hm : key∈keys := by rcases List.mem_cons.mp hk with he|hm; exact False.elim (h he.symm); exact hm
       have hh := ih hm
       simpa only [tableLookup,List.map_cons,List.filter_cons,h,decide_false,Bool.false_eq_true,if_false] using hh

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 theorem tableLookup_map_missing (keys : List Key) (f : Key → Bool) (key : Key) (hk : key∉keys) :
     tableLookup (keys.map (fun k => (k,f k))) key=false := by
   induction keys with
   | nil => rfl
   | cons a keys ih =>
     have ha : a≠key := by intro he; subst a; simp at hk
     have ht : key∉keys := by intro hm; exact hk (List.mem_cons_of_mem a hm)
     have hh := ih ht
     simpa only [tableLookup,List.map_cons,List.filter_cons,ha,decide_false,Bool.false_eq_true,if_false] using hh
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.VertexPairSemantics
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler

 def finVertexPairs (n : ℕ) : List (Fin n×Fin n) :=
   (List.finRange n).flatMap (fun u => ((List.finRange n).filter (fun v => u< v)).map (fun v => (u,v)))
 theorem vertexPairs_fin (n : ℕ) : vertexPairs n=(finVertexPairs n).map (fun p => (p.1.val,p.2.val)) := by
   have hr : List.range n=(List.finRange n).map Fin.val := (finRange_val n).symm
   simp only [vertexPairs,upperRow,finVertexPairs,hr,List.flatMap_map,List.map_flatMap,List.map_map,List.filter_map,Function.comp_def,Fin.lt_def]
 theorem mem_finVertexPairs {n : ℕ} (u v : Fin n) : (u,v)∈finVertexPairs n ↔ u< v := by
   simp [finVertexPairs]
 theorem mem_vertexPairs {n : ℕ} (u v : Fin n) (h : u< v) : (u.val,v.val)∈vertexPairs n := by
   rw [vertexPairs_fin]
   exact List.mem_map.mpr ⟨(u,v),(mem_finVertexPairs u v).mpr h,rfl⟩
 noncomputable def adjacencyNat {n : ℕ} (G : SimpleGraph (Fin n)) (p : Key) : Bool :=
   if hu : p.1< n then if hv : p.2< n then decide (G.Adj ⟨p.1,hu⟩ ⟨p.2,hv⟩) else false else false
 theorem adjacencyNat_fin {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
     adjacencyNat G (u.val,v.val)=decide (G.Adj u v) := by simp only [adjacencyNat,dif_pos u.isLt,dif_pos v.isLt]
 theorem adjacencyBits_table {n : ℕ} (G : SimpleGraph (Fin n)) :
     adjacencyBits G=(vertexPairs n).map (adjacencyNat G) := by
   rw [vertexPairs_fin,List.map_map]
   have he : (fun p : Fin n×Fin n => adjacencyNat G (p.1.val,p.2.val))=(fun p => decide (G.Adj p.1 p.2)) := by
     funext p
     exact adjacencyNat_fin G p.1 p.2
   rw [show adjacencyNat G ∘ (fun p : Fin n×Fin n => (p.1.val,p.2.val))=(fun p => decide (G.Adj p.1 p.2)) from he]
   simp only [adjacencyBits,finVertexPairs,List.map_flatMap,List.map_map,Function.comp_def]
 theorem table_original_adj {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) (h : u< v) :
     tableLookup (zipBits (vertexPairs n) (adjacencyBits G)) (u.val,v.val)=decide (G.Adj u v) := by
   rw [adjacencyBits_table,zipBits_map,tableLookup_map _ _ _ (mem_vertexPairs u v h),adjacencyNat_fin]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OriginalAdjacencyQuery
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def maxNatRealizer : Realizer (fun x : ℕ×ℕ => max x.1 x.2) :=
   ((Realizer.le.pair Realizer.id).comp (Realizer.snd.choose Realizer.fst)).congr (fun x => by simp [max_def])
 theorem maxNat_polynomial : PolyBound maxNatRealizer := by
   unfold maxNatRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair nat_le_polynomial (linear_polynomial linear_id))
     (polynomial_choose (linear_polynomial linear_snd) (linear_polynomial linear_fst))
 def orderedPair (p : Key) : Key := (min p.1 p.2,max p.1 p.2)
 def orderedPairRealizer : Realizer orderedPair := minRealizer.pair maxNatRealizer
 theorem orderedPair_polynomial : PolyBound orderedPairRealizer := polynomial_pair min_polynomial maxNat_polynomial
 theorem vertexPairs_strict (n : ℕ) (p : Key) (h : p∈vertexPairs n) : p.1< p.2 := by
   obtain ⟨u,hu,hp⟩ := List.mem_flatMap.mp h
   obtain ⟨v,hv,he⟩ := List.mem_map.mp hp
   have hlt := (List.mem_filter.mp hv).2
   subst p
   exact of_decide_eq_true hlt
 theorem table_original_any {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
     tableLookup (zipBits (vertexPairs n) (adjacencyBits G)) (orderedPair (u.val,v.val))=decide (G.Adj u v) := by
   by_cases huv : u< v
   · have hn : u.val≤ v.val := huv.le
     simp only [orderedPair,min_eq_left hn,max_eq_right hn]
     exact table_original_adj G u v huv
   · by_cases hvu : v< u
     · have hn : v.val≤ u.val := hvu.le
       simp only [orderedPair,min_eq_right hn,max_eq_left hn]
       rw [table_original_adj G v u hvu,G.adj_comm]
     · have he : u=v := le_antisymm (le_of_not_gt hvu) (le_of_not_gt huv)
       subst v
       simp only [orderedPair,min_self,max_self]
       have hm : (u.val,u.val)∉vertexPairs n := by intro h; have hh := vertexPairs_strict n _ h; exact (Nat.lt_irrefl _) hh
       rw [adjacencyBits_table,zipBits_map,tableLookup_map_missing _ _ _ hm]
       simp

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RoundedGraphCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev RoundedEnv := List ℕ×List Entry
 abbrev RoundedQueryInput := Key×RoundedEnv
 def queryOwnerFirst : Realizer (fun x : RoundedQueryInput => (x.2.1.drop x.1.1).headD 0) :=
   ((Realizer.snd.comp Realizer.fst).pair (Realizer.fst.comp Realizer.fst)).comp lookupNat
 def queryOwnerSecond : Realizer (fun x : RoundedQueryInput => (x.2.1.drop x.1.2).headD 0) :=
   ((Realizer.snd.comp Realizer.fst).pair (Realizer.fst.comp Realizer.snd)).comp lookupNat
 def roundedQuery (x : RoundedQueryInput) : Bool := tableLookup x.2.2
   (orderedPair ((x.2.1.drop x.1.1).headD 0,(x.2.1.drop x.1.2).headD 0))
 def roundedQueryRealizer : Realizer roundedQuery :=
   ((Realizer.snd.comp Realizer.snd).pair ((queryOwnerFirst.pair queryOwnerSecond).comp orderedPairRealizer)).comp tableLookupRealizer
 theorem roundedQuery_polynomial : PolyBound roundedQueryRealizer := by
   have hu : PolyBound queryOwnerFirst := polynomial_comp
     (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) (linear_comp linear_fst linear_fst))) lookupNat_polynomial
   have hv : PolyBound queryOwnerSecond := polynomial_comp
     (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) (linear_comp linear_fst linear_snd))) lookupNat_polynomial
   exact polynomial_comp (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_snd))
     (polynomial_comp (polynomial_pair hu hv) orderedPair_polynomial)) tableLookup_polynomial

 abbrev GraphRoundingInput := ℕ×(List Bool×List ℕ)
 def roundedOwners : Realizer (fun s : GraphRoundingInput => ownerIndices s.2.2) := (Realizer.snd.comp Realizer.snd).comp ownerIndicesRealizer
 def originalTable : Realizer (fun s : GraphRoundingInput => zipBits (vertexPairs s.1) s.2.1) :=
   ((Realizer.fst.comp vertexPairsRealizer).pair (Realizer.snd.comp Realizer.fst)).comp zipBitsRealizer
 def roundedEnvironment : Realizer (fun s : GraphRoundingInput => (ownerIndices s.2.2,zipBits (vertexPairs s.1) s.2.1)) := roundedOwners.pair originalTable
 def roundedOrder : Realizer (fun s : GraphRoundingInput => (ownerIndices s.2.2).length) := roundedOwners.comp listLength
 def roundedBits (s : GraphRoundingInput) : List Bool :=
   (vertexPairs (ownerIndices s.2.2).length).map (fun p => roundedQuery (p,(ownerIndices s.2.2,zipBits (vertexPairs s.1) s.2.1)))
 def roundedBitsRealizer : Realizer roundedBits :=
   (((roundedOrder.comp vertexPairsRealizer).pair roundedEnvironment).comp (mapEnvironment roundedQueryRealizer))
 def roundedGraphCode (s : GraphRoundingInput) : List Bool := encodeNat (ownerIndices s.2.2).length++roundedBits s
 def roundedGraphRealizer : Realizer roundedGraphCode :=
   ((roundedOrder.comp naturalCodeRealizer).pair roundedBitsRealizer).comp appendBits
 theorem roundedOwners_polynomial : PolyBound roundedOwners := polynomial_comp (linear_polynomial (linear_comp linear_snd linear_snd)) ownerIndices_polynomial
 theorem originalTable_polynomial : PolyBound originalTable := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) vertexPairs_polynomial)
     (linear_polynomial (linear_comp linear_snd linear_fst))) zipBits_polynomial
 theorem roundedOrder_polynomial : PolyBound roundedOrder := polynomial_comp roundedOwners_polynomial listLength_polynomial
 theorem roundedEnvironment_polynomial : PolyBound roundedEnvironment := polynomial_pair roundedOwners_polynomial originalTable_polynomial
 theorem roundedBits_polynomial : PolyBound roundedBitsRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp roundedOrder_polynomial vertexPairs_polynomial) roundedEnvironment_polynomial)
   (polynomial_mapEnvironment roundedQuery_polynomial)
 theorem roundedGraph_polynomial : PolyBound roundedGraphRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp roundedOrder_polynomial naturalCode_polynomial) roundedBits_polynomial) appendBits_polynomial

 theorem roundedQuery_correct {n : ℕ} (G : SimpleGraph (Fin n)) (t : Fin n → ℕ)
     (i j : Fin (totalCopies t)) :
     roundedQuery ((i.val,j.val),(ownerIndices (List.ofFn t),zipBits (vertexPairs n) (adjacencyBits G)))=
       decide ((roundedGraph G t).Adj i j) := by
   dsimp only [roundedQuery]
   rw [ownerIndices_lookup,ownerIndices_lookup,table_original_any]
   congr 1
   exact propext (WeightedHelpers.rounded_adj_iff G t i j).symm

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 theorem vertexPairs_bounds (n : ℕ) (p : Key) (h : p∈vertexPairs n) : p.1< n ∧ p.2< n := by
   obtain ⟨u,hu,hp⟩ := List.mem_flatMap.mp h
   obtain ⟨v,hv,he⟩ := List.mem_map.mp hp
   have hnv := List.mem_range.mp (List.mem_filter.mp hv).1
   have hnu := List.mem_range.mp hu
   subst p
   exact ⟨hnu,hnv⟩
 theorem roundedGraphCode_correct {n : ℕ} (G : SimpleGraph (Fin n)) (t : Fin n → ℕ) :
     roundedGraphCode (n,(adjacencyBits G,List.ofFn t))=graphBits (roundedGraph G t) := by
   rw [roundedGraphCode,graphBits_eq,ownerIndices_length]
   congr 1
   dsimp only [roundedBits]
   rw [ownerIndices_length,adjacencyBits_table (roundedGraph G t)]
   apply List.map_congr_left
   intro p hp
   have hb := vertexPairs_bounds (totalCopies t) p hp
   let i : Fin (totalCopies t) := ⟨p.1,hb.1⟩
   let j : Fin (totalCopies t) := ⟨p.2,hb.2⟩
   exact (roundedQuery_correct G t i j).trans (adjacencyNat_fin (roundedGraph G t) i j).symm
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ProjectionCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def selectTrue (entries : List (ℕ×Bool)) : List ℕ := (entries.filter (fun e => e.2)).map Prod.fst
 def selectTrueRealizer : Realizer selectTrue :=
   ((((Realizer.id.pair (Realizer.constant ())).comp (filterEnvironment (Realizer.fst.comp Realizer.snd))).comp (mapList Realizer.fst)))
 theorem selectTrue_polynomial : PolyBound selectTrueRealizer :=
   polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial (linear_constant ())))
     (filterEnvironment_polynomial (linear_polynomial (linear_comp linear_fst linear_snd))))
     (polynomial_mapList (linear_polynomial linear_fst))
 def selectedCopies (owners : List ℕ) (bits : List Bool) : List ℕ :=
   selectTrue (zipBits (List.range owners.length) bits)
 def selectedCopiesRealizer : Realizer (fun s : List ℕ×List Bool => selectedCopies s.1 s.2) :=
   ((((Realizer.fst.comp listLength).comp Realizer.range).pair Realizer.snd).comp zipBitsRealizer).comp selectTrueRealizer
 theorem selectedCopies_polynomial : PolyBound selectedCopiesRealizer :=
   polynomial_comp (polynomial_comp (polynomial_pair
     (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) listLength_polynomial) range_polynomial)
     (linear_polynomial linear_snd)) zipBits_polynomial) selectTrue_polynomial
 def selectedOwners (owners : List ℕ) (bits : List Bool) : List ℕ :=
   (selectedCopies owners bits).map (fun i => (owners.drop i).headD 0)
 def ownerLookupRealizer : Realizer (fun s : ℕ×List ℕ => (s.2.drop s.1).headD 0) :=
   (Realizer.snd.pair Realizer.fst).comp lookupNat
 def selectedOwnersRealizer : Realizer (fun s : List ℕ×List Bool => selectedOwners s.1 s.2) :=
   (selectedCopiesRealizer.pair Realizer.fst).comp (mapEnvironment ownerLookupRealizer)
 theorem selectedOwners_polynomial : PolyBound selectedOwnersRealizer :=
   polynomial_comp (polynomial_pair selectedCopies_polynomial (linear_polynomial linear_fst))
     (polynomial_mapEnvironment (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) lookupNat_polynomial))
 def nonemptyNatList : Realizer (fun L : List ℕ => !L.isEmpty) := (Uniform.isCons (I:=Unit) (α:=fun _ => ℕ)).specialize ()
 theorem nonemptyNatList_linear : Linear nonemptyNatList := by
   apply linear_bool _ 10000
   intro L
   exact Realizer.time_test_le (fun L : List ℕ => !L.isEmpty) (by intro L; cases L <;> rfl) L
 def containsOwner (s : ℕ×List ℕ) : Bool := !(s.2.filter (fun a => decide (a=s.1))).isEmpty
 def containsOwnerRealizer : Realizer containsOwner :=
   (((Realizer.snd.pair Realizer.fst).comp (filterEnvironment Realizer.eqNat)).comp nonemptyNatList)
 theorem containsOwner_polynomial : PolyBound containsOwnerRealizer :=
   polynomial_comp (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst))
     (filterEnvironment_polynomial eqNat_polynomial)) (linear_polynomial nonemptyNatList_linear)
 def projectMask (n : ℕ) (counts : List ℕ) (bits : List Bool) : List Bool :=
   (List.range n).map (fun v => containsOwner (v,selectedOwners (ownerIndices counts) bits))
 abbrev ProjectInput := ℕ×(List ℕ×List Bool)
 def projectOwners : Realizer (fun s : ProjectInput => selectedOwners (ownerIndices s.2.1) s.2.2) :=
   (((Realizer.snd.comp Realizer.fst).comp ownerIndicesRealizer).pair (Realizer.snd.comp Realizer.snd)).comp selectedOwnersRealizer
 def projectMaskRealizer : Realizer (fun s : ProjectInput => projectMask s.1 s.2.1 s.2.2) :=
   ((Realizer.fst.comp Realizer.range).pair projectOwners).comp (mapEnvironment containsOwnerRealizer)
 theorem projectMask_polynomial : PolyBound projectMaskRealizer :=
   polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) range_polynomial)
     (polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_fst)) ownerIndices_polynomial)
       (linear_polynomial (linear_comp linear_snd linear_snd))) selectedOwners_polynomial))
     (polynomial_mapEnvironment containsOwner_polynomial)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GraphHelpers
noncomputable section

open scoped BigOperators
open EdgeSublinearMWIS.Main TreewidthApprox.Pushed
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.GraphHelpers

 theorem avoid_refl {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u : Fin n} (hu : u ∉ X) : AvoidReach G X u u := by
  exact ⟨.nil, by simpa using hu⟩

 theorem avoid_symm {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u v : Fin n} (h : AvoidReach G X u v) : AvoidReach G X v u := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by simpa using hp⟩

 theorem avoid_trans {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u v w : Fin n} (h1 : AvoidReach G X u v) (h2 : AvoidReach G X v w) : AvoidReach G X u w := by
  obtain ⟨p1, h1⟩ := h1
  obtain ⟨p2, h2⟩ := h2
  refine ⟨p1.append p2, ?_⟩
  intro z hz
  rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hz with hz | hz
  · exact h1 z hz
  · exact h2 z hz

 theorem comp_mem {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (u v : Fin n) :
    v ∈ avoidComp G X u ↔ AvoidReach G X u v := by
  classical
  simp [avoidComp]

 theorem comp_self {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u : Fin n} (hu : u ∉ X) : u ∈ avoidComp G X u :=
  (comp_mem G X u u).mpr (avoid_refl G X hu)

 theorem comp_outside {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u v : Fin n} (hv : v ∈ avoidComp G X u) : v ∉ X := by
  obtain ⟨p, hp⟩ := (comp_mem G X u v).mp hv
  exact hp v p.end_mem_support

 theorem comp_eq {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u v : Fin n} (hv : v ∈ avoidComp G X u) : avoidComp G X u = avoidComp G X v := by
  classical
  ext z
  simp only [comp_mem]
  have huv := (comp_mem G X u v).mp hv
  exact ⟨fun h => avoid_trans G X (avoid_symm G X huv) h, fun h => avoid_trans G X huv h⟩

 theorem comp_disjoint_or_eq {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (u v : Fin n) : Disjoint (avoidComp G X u) (avoidComp G X v) ∨
      avoidComp G X u = avoidComp G X v := by
  classical
  by_cases h : Disjoint (avoidComp G X u) (avoidComp G X v)
  · exact Or.inl h
  · obtain ⟨z, hzu, hzv⟩ := Finset.not_disjoint_iff.mp h
    exact Or.inr ((comp_eq G X hzu).trans (comp_eq G X hzv).symm)

 theorem comp_adj {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    {u v w : Fin n} (hv : v ∈ avoidComp G X u) (ha : G.Adj v w) (hw : w ∉ X) :
    w ∈ avoidComp G X u := by
  apply (comp_mem G X u w).mpr
  refine avoid_trans G X ((comp_mem G X u v).mp hv) ⟨ha.toWalk, ?_⟩
  intro z hz
  have hvX := comp_outside G X hv
  simp only [SimpleGraph.Adj.support_toWalk, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · exact hvX
  · exact hw

 theorem component_subset {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n))
    {D : Finset (Fin n)} (hD : D ∈ components G W S) : D ⊆ W \ S := by
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hD
  intro u hu
  have hx := comp_outside G (S ∪ (Finset.univ \ W)) hu
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, not_or,
    not_not] at hx
  exact Finset.mem_sdiff.mpr ⟨hx.2, hx.1⟩

 theorem component_cover {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n))
    {v : Fin n} (hv : v ∈ W \ S) :
    ∃ D ∈ components G W S, v ∈ D := by
  classical
  refine ⟨avoidComp G (S ∪ (Finset.univ \ W)) v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
  apply comp_self
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, not_or, not_not]
  exact ⟨(Finset.mem_sdiff.mp hv).2, (Finset.mem_sdiff.mp hv).1⟩

 theorem components_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n))
    {D E : Finset (Fin n)} (hD : D ∈ components G W S) (hE : E ∈ components G W S) :
    Disjoint D E ∨ D = E := by
  classical
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hD
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hE
  exact comp_disjoint_or_eq G _ u v

 theorem component_noEdge {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n))
    {D : Finset (Fin n)} (hD : D ∈ components G W S) :
    NoEdge G D ((W \ S) \ D) := by
  classical
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hD
  intro v hv w hw ha
  have hwWS := (Finset.mem_sdiff.mp hw).1
  have hwX : w ∉ S ∪ (Finset.univ \ W) := by
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, not_or, not_not]
    exact ⟨(Finset.mem_sdiff.mp hwWS).2, (Finset.mem_sdiff.mp hwWS).1⟩
  exact (Finset.mem_sdiff.mp hw).2 (comp_adj G _ hv ha hwX)

 theorem balanced_split {n : ℕ} (G : SimpleGraph (Fin n)) (W S : Finset (Fin n))
    (hbalanced : Balanced G W S) : ∃ L R : Finset (Fin n),
      IsPartition3 W L S R ∧ NoEdge G L R ∧
        3 * L.card ≤ 2 * W.card ∧ 3 * R.card ≤ 2 * W.card := by
  classical
  let P := components G W S
  let unionOf : Finset (Finset (Fin n)) → Finset (Fin n) := fun A => A.biUnion id
  let candidates := P.powerset.filter (fun A => 3 * (unionOf A).card ≤ 2 * W.card)
  have hne : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, unionOf]
  obtain ⟨A, hA, hmax⟩ := candidates.exists_max_image (fun A => (unionOf A).card) hne
  have hAP : A ⊆ P := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
  have hcap : 3 * (unionOf A).card ≤ 2 * W.card := (Finset.mem_filter.mp hA).2
  let L := unionOf A
  let R := (W \ S) \ L
  have hL : L ⊆ W \ S := by
    intro v hv
    obtain ⟨D, hDA, hvD⟩ := Finset.mem_biUnion.mp hv
    exact component_subset G W S (hAP hDA) hvD
  have hDmax (D : Finset (Fin n)) (hDP : D ∈ P) : D.card ≤ L.card := by
    have hDcand : {D} ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.singleton_subset_iff.mpr hDP, ?_⟩
      simpa [unionOf] using hbalanced.2 D hDP
    simpa [unionOf] using hmax {D} hDcand
  have hRcap : 3 * R.card ≤ 2 * W.card := by
    by_contra hh
    have hsum : R.card + L.card ≤ W.card := by
      rw [show R.card + L.card = (W \ S).card from Finset.card_sdiff_add_card_eq_card hL]
      exact Finset.card_le_card Finset.sdiff_subset
    have hLsmall : 3 * L.card < W.card := by omega
    have hRne : R.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨v, hvR⟩ := hRne
    obtain ⟨D, hDP, hvD⟩ := component_cover G W S (Finset.mem_sdiff.mp hvR).1
    have hDdis : Disjoint L D := by
      apply (Finset.disjoint_biUnion_left A id D).mpr
      intro E hEA
      rcases components_disjoint G W S (hAP hEA) hDP with hdis | heq
      · exact hdis
      · have hvL : v ∈ L := Finset.mem_biUnion.mpr ⟨E, hEA, heq.symm ▸ hvD⟩
        exact False.elim ((Finset.mem_sdiff.mp hvR).2 hvL)
    have hDsmall := hDmax D hDP
    have hcard : (unionOf (insert D A)).card = D.card + L.card := by
      simp only [unionOf, Finset.biUnion_insert]
      exact Finset.card_union_of_disjoint hDdis.symm
    have hnew : insert D A ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset hDP hAP, ?_⟩
      rw [hcard]
      omega
    have hmax' := hmax (insert D A) hnew
    rw [hcard] at hmax'
    have hDpos : 0 < D.card := Finset.card_pos.mpr ⟨v, hvD⟩
    change D.card + L.card ≤ L.card at hmax'
    omega
  have hNo : NoEdge G L R := by
    intro v hv u hu ha
    obtain ⟨D, hDA, hvD⟩ := Finset.mem_biUnion.mp hv
    have huD : u ∉ D := by
      intro huD
      exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_biUnion.mpr ⟨D, hDA, huD⟩)
    exact component_noEdge G W S (hAP hDA) v hvD u
      (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hu).1, huD⟩) ha
  refine ⟨L, R, ?_, hNo, hcap, hRcap⟩
  have hS := hbalanced.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hvL hvS
    exact (Finset.mem_sdiff.mp (hL hvL)).2 hvS
  · apply Finset.disjoint_left.mpr
    intro v hvL hvR
    exact (Finset.mem_sdiff.mp hvR).2 hvL
  · apply Finset.disjoint_left.mpr
    intro v hvS hvR
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hvR).1).2 hvS
  · ext v
    have hLv : v ∈ L → v ∈ W := fun h => (Finset.mem_sdiff.mp (hL h)).1
    have hSv : v ∈ S → v ∈ W := fun h => hS h
    simp only [Finset.mem_union, R, Finset.mem_sdiff]
    tauto

end EdgeSublinearMWIS.Main.GraphHelpers
end

-- Solutions.PartitionBridge
noncomputable section

open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.GraphHelpers TreewidthApprox.Pushed
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PartitionBridge

 theorem balanced_from_partition {n : ℕ} (G : SimpleGraph (Fin n)) (W L S R : Finset (Fin n))
    (hpart : IsPartition3 W L S R) (hNo : NoEdge G L R)
    (hL : 3 * L.card ≤ 2 * W.card) (hR : 3 * R.card ≤ 2 * W.card) : Balanced G W S := by
  classical
  have hunion := hpart.2.2.2
  have hS : S ⊆ W := by intro x hx; rw [← hunion]; simp [hx]
  have hWS : W \ S = L ∪ R := by
    ext v
    have hLS := Finset.disjoint_left.mp hpart.1
    have hSR := Finset.disjoint_left.mp hpart.2.2.1
    rw [← hunion]
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hX : Finset.univ \ (S ∪ (Finset.univ \ W)) = L ∪ R := by
    rw [← hWS]
    ext v
    simp
    tauto
  have hparts : Disjoint L R ∧ Disjoint L ∅ ∧ Disjoint R ∅ ∧
      L ∪ R ∪ ∅ = Finset.univ \ (S ∪ (Finset.univ \ W)) := by
    refine ⟨hpart.2.1, by simp, by simp, ?_⟩
    simpa only [Finset.union_empty] using hX.symm
  have hno3 : NoEdge G L R ∧ NoEdge G L ∅ ∧ NoEdge G R ∅ := by
    exact ⟨hNo, by simp [NoEdge], by simp [NoEdge]⟩
  obtain ⟨hcompL, hcompR, hcomp0⟩ := TreewidthApprox.Partition.comp_subset_part G _ L R ∅ hparts hno3
  refine ⟨hS, ?_⟩
  intro D hD
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hD
  rw [hWS, Finset.mem_union] at hv
  rcases hv with hv | hv
  · exact (Nat.mul_le_mul_left 3 (Finset.card_le_card (hcompL v hv))).trans hL
  · exact (Nat.mul_le_mul_left 3 (Finset.card_le_card (hcompR v hv))).trans hR

 theorem lift_balanced {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
    (f : Fin m ↪ Fin n) (W : Finset (Fin n)) (S0 : Finset (Fin m))
    (hW : (Finset.univ.image f) = W)
    (hAdj : ∀ u v, H.Adj u v ↔ G.Adj (f u) (f v)) (hbal : Balanced H Finset.univ S0) :
    Balanced G W (S0.image f) ∧ (S0.image f).card = S0.card := by
  classical
  obtain ⟨L0, R0, hpart, hNo, hL, hR⟩ := balanced_split H Finset.univ S0 hbal
  have hd {U V : Finset (Fin m)} (hUV : Disjoint U V) : Disjoint (U.image f) (V.image f) := by
    apply Finset.disjoint_left.mpr
    intro v hvU hvV
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hvU
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hvV
    have hwu := f.injective he
    exact Finset.disjoint_left.mp hUV hu (hwu ▸ hw)
  have hpart' : IsPartition3 W (L0.image f) (S0.image f) (R0.image f) := by
    refine ⟨hd hpart.1, hd hpart.2.1, hd hpart.2.2.1, ?_⟩
    rw [← Finset.image_union, ← Finset.image_union, hpart.2.2.2, hW]
  have hNo' : NoEdge G (L0.image f) (R0.image f) := by
    intro u hu v hv hadj
    obtain ⟨u0, hu0, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v0, hv0, rfl⟩ := Finset.mem_image.mp hv
    exact hNo u0 hu0 v0 hv0 ((hAdj u0 v0).mpr hadj)
  have hcard (U : Finset (Fin m)) : (U.image f).card = U.card := Finset.card_image_of_injective U f.injective
  have hWcard : W.card = (Finset.univ : Finset (Fin m)).card := by rw [← hW, hcard]
  refine ⟨balanced_from_partition G W _ _ _ hpart' hNo' ?_ ?_, hcard S0⟩
  · simpa only [hcard, hWcard] using hL
  · simpa only [hcard, hWcard] using hR

end EdgeSublinearMWIS.Main.PartitionBridge
end

-- Solutions.ConditioningEntropy
noncomputable section

/- Adapted from Apache-2.0 Lax263307Proofs at paper-linked commit 68b2d26;
   all proofs included, no conceptual axioms imported. -/


/-!
---
title: Entropy and adjacency mass
type: definition
---
For a probability vector $\pi$ on $n$ vertices, its entropy in bits is
$$H(\pi)=-\sum_v\pi_v\log_2\pi_v,$$
with zero summands at zero probabilities. Its adjacency mass in a graph $G$ is
$$\sum_{u,v:\,uv\in E(G)}\pi_u\pi_v,$$
where ordered adjacent pairs are counted, so each edge contributes twice.

# Formalization notes

The auxiliary natural-log entropy differs by the positive factor $\ln2$.
Both definitions use mathlib's `negMulLog`, whose value at zero is zero.
The adjacency mass is an ordered sum, avoiding choices of edge orientations.
-/

namespace EdgeSublinearMWIS.Main.ConditioningEntropy

/-- A nonnegative vector with total mass one. -/
def IsProbability {n : ℕ} (π : Fin n → ℝ) : Prop :=
  (∀ v, 0 ≤ π v) ∧ (∑ v, π v) = 1

/-- Entropy measured with natural logarithms. -/
noncomputable def naturalEntropy {n : ℕ} (π : Fin n → ℝ) : ℝ :=
  ∑ v, Real.negMulLog (π v)

/-- Shannon entropy in bits. -/
noncomputable def entropy {n : ℕ} (π : Fin n → ℝ) : ℝ :=
  naturalEntropy π / Real.log 2

/-- Total product probability of ordered adjacent vertex pairs. -/
noncomputable def adjacencyMass {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (π : Fin n → ℝ) : ℝ :=
  ∑ u, ∑ v, if G.Adj u v then π u * π v else 0

/-- Sum of endpoint-cost products over unordered edges. -/
noncomputable def edgeCost {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (x : Fin n → ℝ) : ℝ :=
  adjacencyMass G x / 2

end EdgeSublinearMWIS.Main.ConditioningEntropy


namespace EdgeSublinearMWIS.Main.ConditioningEntropy.Algebra

open EdgeSublinearMWIS.Main.ConditioningEntropy

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at this ⊢
  exact this

theorem probability_entry_le_one {n : ℕ} (π : Fin n → ℝ) (hπ : IsProbability π)
    (v : Fin n) : π v ≤ 1 := by
  rw [← hπ.2]
  exact Finset.single_le_sum (fun u _ => hπ.1 u) (Finset.mem_univ v)

theorem scaled_negMulLog_div (a x : ℝ) (ha : 0 < a) :
    a * Real.negMulLog (x / a) = Real.negMulLog x + x * Real.log a := by
  by_cases hx : x = 0
  · simp [hx]
  · dsimp [Real.negMulLog]
    rw [Real.log_div hx (ne_of_gt ha)]
    field_simp
    ring

theorem relative_term_bound (x a b : ℝ) (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) :
    x - a * b ≤ -Real.negMulLog x - x * Real.log a - x * Real.log b := by
  have hab : 0 < a * b := mul_pos ha hb
  have h := Real.log_le_sub_one_of_pos (div_pos hab hx)
  rw [Real.log_div (ne_of_gt hab) (ne_of_gt hx),
    Real.log_mul (ne_of_gt ha) (ne_of_gt hb)] at h
  have hm := mul_le_mul_of_nonneg_left h hx.le
  simp_rw [mul_sub] at hm
  rw [mul_div_cancel₀ _ (ne_of_gt hx), mul_one] at hm
  dsimp [Real.negMulLog]
  nlinarith

theorem natural_entropy_nonneg {n : ℕ} (π : Fin n → ℝ) (hπ : IsProbability π) :
    0 ≤ naturalEntropy π :=
  Finset.sum_nonneg fun v _ => Real.negMulLog_nonneg (hπ.1 v) (probability_entry_le_one π hπ v)

theorem natural_entropy_le_log {n : ℕ} (π : Fin n → ℝ) (hπ : IsProbability π) :
    naturalEntropy π ≤ Real.log n := by
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    simpa using hπ.2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hw : (∑ _v : Fin n, (1 / (n : ℝ))) = 1 := by simp [hn0]
  have h := Real.concaveOn_negMulLog.le_map_sum
    (t := Finset.univ) (w := fun _ : Fin n => 1 / (n : ℝ)) (p := π)
    (fun _ _ => (one_div_pos.mpr hnR).le) hw (fun v _ => hπ.1 v)
  simp only [smul_eq_mul] at h
  simp_rw [← Finset.mul_sum] at h
  rw [hπ.2, mul_one] at h
  have hm := mul_le_mul_of_nonneg_left h hnR.le
  rw [← mul_assoc, mul_one_div_cancel hn0, one_mul] at hm
  have heq : (n : ℝ) * Real.negMulLog (1 / (n : ℝ)) = Real.log n := by
    simp [Real.negMulLog, hn0]
  exact hm.trans_eq heq

end EdgeSublinearMWIS.Main.ConditioningEntropy.Algebra


namespace EdgeSublinearMWIS.Main.ConditioningEntropy.Gap

open EdgeSublinearMWIS.Main.ConditioningEntropy EdgeSublinearMWIS.Main.ConditioningEntropy.Algebra

theorem joint_entry_le {n : ℕ} (π : Fin n → ℝ) (q : Fin n → Fin n → ℝ)
    (hq : ∀ u v, 0 ≤ q u v) (hm : ∀ v, (∑ u, q u v) = π v) (u v : Fin n) :
    q u v ≤ π v := by
  rw [← hm v]
  exact Finset.single_le_sum (fun i _ => hq i v) (Finset.mem_univ u)

theorem row_marginal {n : ℕ} (π : Fin n → ℝ) (q : Fin n → Fin n → ℝ)
    (hs : ∀ u v, q u v = q v u) (hm : ∀ v, (∑ u, q u v) = π v) (u : Fin n) :
    (∑ v, q u v) = π u := by
  simp_rw [hs u]
  exact hm u

theorem weighted_conditional_entropy {n : ℕ} (π : Fin n → ℝ) (q : Fin n → Fin n → ℝ)
    (hπ : IsProbability π) (hq : ∀ u v, 0 ≤ q u v)
    (hm : ∀ v, (∑ u, q u v) = π v) :
    (∑ v, π v * naturalEntropy (fun u => q u v / π v)) =
      (∑ v, ∑ u, Real.negMulLog (q u v)) - naturalEntropy π := by
  have hpoint (u v : Fin n) :
      π v * Real.negMulLog (q u v / π v) =
        Real.negMulLog (q u v) + q u v * Real.log (π v) := by
    rcases eq_or_lt_of_le (hπ.1 v) with hv | hv
    · have hzero : q u v = 0 := le_antisymm
        ((joint_entry_le π q hq hm u v).trans_eq hv.symm) (hq u v)
      simp [← hv, hzero]
    · exact scaled_negMulLog_div _ _ hv
  simp_rw [naturalEntropy, Finset.mul_sum, hpoint, Finset.sum_add_distrib,
    ← Finset.sum_mul, hm]
  simp [Real.negMulLog, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem natural_gap_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (π : Fin n → ℝ) (q : Fin n → Fin n → ℝ)
    (hπ : IsProbability π) (hq : ∀ u v, 0 ≤ q u v)
    (hs : ∀ u v, q u v = q v u) (hm : ∀ v, (∑ u, q u v) = π v)
    (he : ∀ u v, G.Adj u v → q u v = 0) :
    adjacencyMass G π ≤ naturalEntropy π -
      ∑ v, π v * naturalEntropy (fun u => q u v / π v) := by
  let cost := fun u v => -Real.negMulLog (q u v) -
    q u v * Real.log (π u) - q u v * Real.log (π v)
  have hpoint (u v : Fin n) :
      q u v - π u * π v + (if G.Adj u v then π u * π v else 0) ≤ cost u v := by
    by_cases hedge : G.Adj u v
    · simp [cost, hedge, he u v hedge]
    · simp only [if_neg hedge, add_zero]
      rcases eq_or_lt_of_le (hq u v) with hzero | hpos
      · simp only [← hzero, Real.negMulLog_zero, zero_mul, sub_zero, zero_sub, cost]
        simpa using neg_nonpos.mpr (mul_nonneg (hπ.1 u) (hπ.1 v))
      · have hv := lt_of_lt_of_le hpos (joint_entry_le π q hq hm u v)
        have hu := lt_of_lt_of_le (hpos.trans_eq (hs u v)) (joint_entry_le π q hq hm v u)
        exact relative_term_bound _ _ _ hpos hu hv
  have htotal : (∑ v, ∑ u, q u v) = 1 := by simp_rw [hm]; exact hπ.2
  have hproduct : (∑ v, ∑ u, π u * π v) = 1 := by
    simp_rw [← Finset.sum_mul, hπ.2, one_mul]
    exact hπ.2
  have hcrossV : (∑ v, ∑ u, q u v * Real.log (π v)) = -naturalEntropy π := by
    simp only [← Finset.sum_mul, hm, naturalEntropy, Real.negMulLog,
      neg_mul, Finset.sum_neg_distrib, neg_neg]
  have hcrossU : (∑ v, ∑ u, q u v * Real.log (π u)) = -naturalEntropy π := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, row_marginal π q hs hm, naturalEntropy,
      Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_neg]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun v _ =>
    Finset.sum_le_sum (s := Finset.univ) fun u _ => hpoint u v
  have hadj : (∑ v, ∑ u, if G.Adj u v then π u * π v else 0) = adjacencyMass G π := by
    rw [Finset.sum_comm]
    rfl
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, cost,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hsum
  rw [htotal, hproduct, hadj, hcrossU, hcrossV] at hsum
  rw [weighted_conditional_entropy π q hπ hq hm]
  linarith

/--
---
conclusion: EdgeSublinearMWIS.Main.ConditioningEntropyGap.average_entropy_gap
---
The expected entropy decrease is at least the product probability of
ordered adjacent pairs.

# Proof strategy

The entropy chain rule expresses the decrease as a relative-entropy sum.
The inequality `log x ≤ x - 1` bounds each positive-support term below
by joint mass minus product mass. Edge pairs have zero joint mass, so
their product mass contributes to the gap. Zero marginals are treated
explicitly. Divide by `log 2` to obtain the inequality in bits.
-/
theorem average_entropy_gap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (π : Fin n → ℝ) (q : Fin n → Fin n → ℝ)
    (probability : IsProbability π) (nonnegative : ∀ u v, 0 ≤ q u v)
    (symmetric : ∀ u v, q u v = q v u)
    (marginals : ∀ v, (∑ u, q u v) = π v)
    (edge_zero : ∀ u v, G.Adj u v → q u v = 0) :
    adjacencyMass G π ≤ entropy π - ∑ v, π v * entropy (fun u => q u v / π v) := by
  have hgap := natural_gap_bound G π q probability nonnegative symmetric marginals edge_zero
  have hmass : 0 ≤ adjacencyMass G π := by
    apply Finset.sum_nonneg
    intro u _
    apply Finset.sum_nonneg
    intro v _
    split_ifs
    · exact mul_nonneg (probability.1 u) (probability.1 v)
    · exact le_rfl
  have hm : adjacencyMass G π * Real.log 2 ≤ adjacencyMass G π := by
    nlinarith [log_two_le_one]
  simp_rw [entropy, ← mul_div_assoc, ← Finset.sum_div, ← sub_div]
  exact (le_div_iff₀ log_two_pos).2 (hm.trans hgap)

end EdgeSublinearMWIS.Main.ConditioningEntropy.Gap


namespace EdgeSublinearMWIS.Main.ConditioningEntropy.Bounds

open EdgeSublinearMWIS.Main.ConditioningEntropy EdgeSublinearMWIS.Main.ConditioningEntropy.Algebra

/--
---
conclusion: EdgeSublinearMWIS.Main.ConditioningEntropyBounds.entropy_bounds
---
The entropy of a probability vector lies between zero and the logarithm
of the number of vertices.

# Proof strategy

Each entropy summand is nonnegative. Jensen's inequality for the concave
function `negMulLog` bounds their sum by the entropy of the uniform vector.
Divide by the positive logarithm of two to obtain the bound in bits.
-/
theorem entropy_bounds {n : ℕ} (π : Fin n → ℝ) (probability : IsProbability π) :
    0 ≤ entropy π ∧ entropy π ≤ Real.logb 2 n := by
  constructor
  · exact div_nonneg (natural_entropy_nonneg π probability) log_two_pos.le
  · exact div_le_div_of_nonneg_right (natural_entropy_le_log π probability) log_two_pos.le

end EdgeSublinearMWIS.Main.ConditioningEntropy.Bounds
end

-- Solutions.ConditioningMoments
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.ConditioningMoments
open ConditioningEntropy

 def costs {n : ℕ} (y : Finset (Fin n) → ℝ) (A : Finset (Fin n)) (v : Fin n) := y (insert v A)/y A
 def marginal {n : ℕ} (y : Finset (Fin n) → ℝ) (A : Finset (Fin n)) (k : ℕ) (v : Fin n) := costs y A v/k
 def joint {n : ℕ} (y : Finset (Fin n) → ℝ) (A : Finset (Fin n)) (k : ℕ) (u v : Fin n) := y (insert u (insert v A))/((k:ℝ)^2*y A)

 theorem in_coordinates {n r : ℕ} (A : Finset (Fin n)) (hA : A.card≤ r+2) : A∈Coordinates Finset.univ r := by
  simp [Coordinates,hA]

 theorem invariants {n : ℕ} (G : SimpleGraph (Fin n)) (r k : ℕ) (y : Finset (Fin n) → ℝ)
    (hy : Relaxation G Finset.univ r k y) (A : Finset (Fin n)) (hA : A.card≤ r)
    (hpos : 0< y A) :
    (∀v,0≤ costs y A v ∧ costs y A v≤1) ∧ (∑ v,costs y A v)=(k:ℝ) ∧
    (∀v∈A,costs y A v=1) ∧ (∀v,0< costs y A v → 0< y (insert v A)) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro v
    have hn := (hy.2.1 _ (in_coordinates (insert v A) (by have := Finset.card_insert_le v A; omega))).1
    exact ⟨div_nonneg hn hpos.le,(div_le_one hpos).mpr (hy.2.2.1 A (Finset.subset_univ _) (by omega) v (Finset.mem_univ _))⟩
  · simp_rw [costs,← Finset.sum_div]
    have hm := hy.2.2.2.2 A (Finset.subset_univ _) (by omega)
    rw [hm,mul_div_cancel_right₀ _ hpos.ne']
  · intro v hv
    simp [costs,Finset.insert_eq_of_mem hv,hpos.ne']
  · intro v hv
    exact (div_pos_iff_of_pos_right hpos).mp hv

 theorem marginal_probability {n : ℕ} (G : SimpleGraph (Fin n)) (r k : ℕ) (y : Finset (Fin n) → ℝ)
    (hy : Relaxation G Finset.univ r k y) (A : Finset (Fin n)) (hA : A.card≤ r)
    (hpos : 0< y A) (hk : 0< k) : IsProbability (marginal y A k) := by
  have hkR : (0:ℝ)< k := by exact_mod_cast hk
  have hi := invariants G r k y hy A hA hpos
  refine ⟨fun v => div_nonneg (hi.1 v).1 hkR.le,?_⟩
  simp_rw [marginal,← Finset.sum_div]
  rw [hi.2.1,div_self hkR.ne']

 theorem distribution {n : ℕ} (G : SimpleGraph (Fin n)) (r k : ℕ) (y : Finset (Fin n) → ℝ)
    (hy : Relaxation G Finset.univ r k y) (A : Finset (Fin n)) (hA : A.card< r)
    (hpos : 0< y A) (hk : 0< k) :
    (∀u v,0≤ joint y A k u v) ∧ (∀u v,joint y A k u v=joint y A k v u) ∧
    (∀v,(∑ u,joint y A k u v)=marginal y A k v) ∧
    (∀u v,G.Adj u v → joint y A k u v=0) ∧
    (∀u v,0 < marginal y A k v → marginal y (insert v A) k u=joint y A k u v/marginal y A k v) := by
  have hkR : (0:ℝ)< k := by exact_mod_cast hk
  have hk0 := hkR.ne'
  have hA0 := hpos.ne'
  have hs (v : Fin n) : (insert v A).card≤ r+1 := by have := Finset.card_insert_le v A; omega
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro u v
    have hnn := (hy.2.1 _ (in_coordinates (insert u (insert v A)) (by have := Finset.card_insert_le u (insert v A); have := hs v; omega))).1
    exact div_nonneg hnn (mul_nonneg (sq_nonneg _) hpos.le)
  · intro u v; simp only [joint,Finset.insert_comm]
  · intro v
    simp_rw [joint,← Finset.sum_div]
    have hm := hy.2.2.2.2 (insert v A) (Finset.subset_univ _) (hs v)
    rw [hm]
    dsimp [marginal,costs]
    field_simp
  · intro u v huv
    have hnot : ¬ G.IsIndepSet (↑(insert u (insert v A)) : Set (Fin n)) := by
      intro hi
      exact hi (by simp) (by simp) huv.ne huv
    have hz := hy.2.2.2.1 (insert u (insert v A)) (in_coordinates _ (by have := Finset.card_insert_le u (insert v A); have := hs v; omega)) hnot
    simp [joint,hz]
  · intro u v hv
    have hcost : 0< costs y A v := (div_pos_iff_of_pos_right hkR).mp hv
    have hv0 := ((invariants G r k y hy A hA.le hpos).2.2.2 v hcost).ne'
    dsimp [marginal,costs,joint]
    field_simp

end EdgeSublinearMWIS.Main.ConditioningMoments
end

-- Solutions.ConditioningDecrease
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.ConditioningMoments
open ConditioningEntropy ConditioningEntropy.Algebra

 theorem adjacency_energy {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) :
    adjacencyMass G x = 2*edgeEnergy G x := by
  have he : edgeEnergy G x = ∑ u,∑ v,if u< v ∧ G.Adj u v then x u*x v else 0 := by
    unfold edgeEnergy
    rw [Finset.sum_filter,← Finset.univ_product_univ,Finset.sum_product]
  have point (u v : Fin n) : (if G.Adj u v then x u*x v else 0) =
      (if u< v ∧ G.Adj u v then x u*x v else 0)+(if v< u ∧ G.Adj u v then x u*x v else 0) := by
    by_cases ha : G.Adj u v
    · rcases lt_or_gt_of_ne (G.ne_of_adj ha) with h | h <;> simp [ha,h,not_lt_of_gt h]
    · simp [ha]
  unfold adjacencyMass
  simp_rw [point,Finset.sum_add_distrib]
  have hswap : (∑ u,∑ v,if v< u ∧ G.Adj u v then x u*x v else 0) = edgeEnergy G x := by
    rw [he,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    rw [G.adj_comm,mul_comm]
  rw [← he,hswap]
  ring

 theorem adjacency_div {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (k : ℝ) :
    adjacencyMass G (fun v => x v/k) = adjacencyMass G x/k^2 := by
  unfold adjacencyMass
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs <;> ring

 theorem entropy_decrease {n : ℕ} (G : SimpleGraph (Fin n)) (r k p : ℕ) (y : Finset (Fin n) → ℝ)
    (hy : Relaxation G Finset.univ r k y) (A : Finset (Fin n)) (hA : A.card< r)
    (hpos : 0< y A) (hk : 0< k) (hp : 0< p)
    (hexp : (k:ℝ)^2/p < edgeEnergy G (costs y A)) :
    ∃v : Fin n,0< y (insert v A) ∧
      entropy (marginal y (insert v A) k) < entropy (marginal y A k)-2/p := by
  have hkR : (0:ℝ)< k := by exact_mod_cast hk
  have hpR : (0:ℝ)< p := by exact_mod_cast hp
  have hi := invariants G r k y hy A hA.le hpos
  have hπ := marginal_probability G r k y hy A hA.le hpos hk
  obtain ⟨hq,hs,hm,he,hcond⟩ := distribution G r k y hy A hA hpos hk
  have hgap := ConditioningEntropy.Gap.average_entropy_gap G (marginal y A k) (joint y A k) hπ hq hs hm he
  have hmass : 2/(p:ℝ) < adjacencyMass G (marginal y A k) := by
    change 2/(p:ℝ) < adjacencyMass G (fun v => costs y A v/k)
    rw [adjacency_div,adjacency_energy]
    apply (div_lt_div_iff₀ hpR (sq_pos_of_pos hkR)).mpr
    have ht := (div_lt_iff₀ hpR).mp hexp
    nlinarith
  have havg : (∑ v,marginal y A k v*entropy (fun u => joint y A k u v/marginal y A k v)) < entropy (marginal y A k)-2/p := by linarith
  have hex : ∃v,0 < marginal y A k v ∧ entropy (fun u => joint y A k u v/marginal y A k v) < entropy (marginal y A k)-2/p := by
    by_contra hn
    push Not at hn
    have hm' := Finset.sum_le_sum (fun v (_ : v∈(Finset.univ : Finset (Fin n))) =>
      show marginal y A k v*(entropy (marginal y A k)-2/p) ≤ marginal y A k v*entropy (fun u => joint y A k u v/marginal y A k v) from by
        by_cases hv : 0 < marginal y A k v
        · exact mul_le_mul_of_nonneg_left (hn v hv) (hπ.1 v)
        · have hz : marginal y A k v=0 := le_antisymm (not_lt.mp hv) (hπ.1 v)
          simp [hz])
    rw [← Finset.sum_mul,hπ.2,one_mul] at hm'
    linarith
  obtain ⟨v,hv,hdrop⟩ := hex
  have hcost : 0< costs y A v := (div_pos_iff_of_pos_right hkR).mp hv
  refine ⟨v,hi.2.2.2 v hcost,?_⟩
  have heq : marginal y (insert v A) k=(fun u => joint y A k u v/marginal y A k v) := funext (fun u => hcond u v hv)
  rwa [heq]

end EdgeSublinearMWIS.Main.ConditioningMoments
end

-- Solutions.ActiveGraphTransport
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ActiveTransport
open ConditioningEntropy ConditioningEntropy.Algebra

 def activeMap {n : ℕ} (W : Finset (Fin n)) : Fin W.card ↪ Fin n := (W.orderEmbOfFin rfl).toEmbedding
 def activeGraph {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) : SimpleGraph (Fin W.card) := G.comap (activeMap W)
 theorem activeMap_image {n : ℕ} (W : Finset (Fin n)) : Finset.univ.image (activeMap W)=W :=
   Finset.image_orderEmbOfFin_univ W rfl
 theorem activeMap_mem {n : ℕ} (W : Finset (Fin n)) (v : Fin W.card) : activeMap W v∈W :=
   Finset.orderEmbOfFin_mem W rfl v
 theorem hereditary_active {n : ℕ} (C : GraphClass) (hC : Hereditary C) (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (hG : C n G) :
     C W.card (activeGraph G W) := hC G _ (activeMap W) hG (fun _ _ => Iff.rfl)
 theorem sum_image {n m : ℕ} (f : Fin m ↪ Fin n) (x : Fin n → ℝ) (S : Finset (Fin m)) :
     vertexSum x (S.image f)=vertexSum (fun v => x (f v)) S := by
   unfold vertexSum
   rw [Finset.sum_image]
   intro a ha b hb he
   exact f.injective he
 theorem sum_active {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (x : Fin n → ℝ) :
     vertexSum (fun v => x (activeMap W v)) Finset.univ=vertexSum x W := by
   calc
     _ = vertexSum x (Finset.univ.image (activeMap W)) := (sum_image (activeMap W) x Finset.univ).symm
     _ = vertexSum x W := by rw [activeMap_image]
 theorem lift_light {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m))
     (f : Fin m ↪ Fin n) (W : Finset (Fin n)) (S : Finset (Fin m)) (δ : ℝ) (x : Fin n → ℝ)
     (hW : Finset.univ.image f=W) (hAdj : ∀u v,H.Adj u v↔G.Adj (f u) (f v))
     (hLight : Light H Finset.univ S δ (fun v => x (f v))) : Light G W (S.image f) δ x := by
   obtain ⟨hbal,hcard⟩ := PartitionBridge.lift_balanced G H f W S hW hAdj hLight.1
   refine ⟨hbal,?_⟩
   rw [sum_image,← hW,sum_image]
   exact hLight.2
 theorem restricted_adjacency {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (x : Fin n → ℝ) :
     adjacencyMass G (fun v => if v∈W then x v else 0)=∑u∈W,∑v∈W,if G.Adj u v then x u*x v else 0 := by
   unfold adjacencyMass
   rw [← Finset.sum_subset (Finset.subset_univ W) (by
     intro u hu huW
     simp only [huW,if_false,zero_mul,ite_self,Finset.sum_const_zero])]
   apply Finset.sum_congr rfl
   intro u hu
   simp only [hu,if_true]
   rw [← Finset.sum_subset (Finset.subset_univ W) (by
     intro v hv hvW
     simp only [hvW,if_false,mul_zero,ite_self])]
   apply Finset.sum_congr rfl
   intro v hv
   simp only [hv,if_true]
 theorem energy_active {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (x : Fin n → ℝ) :
     edgeEnergy (activeGraph G W) (fun v => x (activeMap W v))=edgeEnergy G (fun v => if v∈W then x v else 0) := by
   have hm : adjacencyMass (activeGraph G W) (fun v => x (activeMap W v))=
       adjacencyMass G (fun v => if v∈W then x v else 0) := by
     rw [restricted_adjacency]
     have hmap : (Finset.univ : Finset (Fin W.card)).map (activeMap W)=W := by
       simpa only [Finset.map_eq_image] using activeMap_image W
     conv_rhs => rw [← hmap]
     simp only [Finset.sum_map]
     rfl
   rw [ConditioningMoments.adjacency_energy,ConditioningMoments.adjacency_energy] at hm
   linarith
end EdgeSublinearMWIS.Main.ActiveTransport
end

-- Solutions.ActiveVertexCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ActiveTransport

 theorem zipBitsFold_map_pair {α β : Type} [Coding β] (L : List α) (f : α → β) (g : α → Bool) (acc : List (β×Bool)) :
     (L.map f).foldl (fun s a => zipBitsStep (a,s)) (L.map g,acc)=([],(L.map (fun a => (f a,g a))).reverse++acc) := by
   induction L generalizing acc with
   | nil => rfl
   | cons a L ih =>
     rw [List.map_cons,List.map_cons,List.foldl_cons]
     change (L.map f).foldl (fun s a => zipBitsStep (a,s)) (L.map g,(f a,g a)::acc)=_
     rw [ih,List.map_cons,List.reverse_cons]
     simp only [List.append_assoc,List.singleton_append]
 theorem zipBits_map_pair {α β : Type} [Coding β] (L : List α) (f : α → β) (g : α → Bool) :
     zipBits (L.map f) (L.map g)=L.map (fun a => (f a,g a)) := by
   rw [zipBits,zipBitsFold_map_pair]
   simp
 def activeVertices (n : ℕ) (bits : List Bool) : List ℕ := selectTrue (zipBits (List.range n) bits)
 def activeVerticesRealizer : Realizer (fun s : ℕ×List Bool => activeVertices s.1 s.2) :=
   (((Realizer.fst.comp Realizer.range).pair Realizer.snd).comp zipBitsRealizer).comp selectTrueRealizer
 theorem activeVertices_polynomial : PolyBound activeVerticesRealizer :=
   polynomial_comp (polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) range_polynomial)
     (linear_polynomial linear_snd)) zipBits_polynomial) selectTrue_polynomial
 theorem activeVertices_mask {n : ℕ} (W : Finset (Fin n)) : activeVertices n (mask W)=(W.sort (·≤·)).map Fin.val := by
   have hf : ((List.finRange n).filter (fun v => decide (v∈W)))=W.sort (·≤·) := by
     exact (((List.sortedLT_finRange n).pairwise.filter _).sortedLT).eq_of_mem_iff W.sortedLT_sort (by intro v; simp)
   unfold activeVertices
   rw [← finRange_val n]
   have hm : mask W=(List.finRange n).map (fun v => decide (v∈W)) := by simp only [mask,List.finRange,List.map_ofFn]; rfl
   rw [hm,zipBits_map_pair]
   simp only [selectTrue,List.filter_map,List.map_map,Function.comp_def]
   rw [hf]
 theorem sortedOwners_ofFn {n : ℕ} (W : Finset (Fin n)) :
     (W.sort (·≤·)).map Fin.val=List.ofFn (fun v : Fin W.card => (activeMap W v).val) := by
   rw [← W.listMap_orderEmbOfFin_finRange rfl,List.map_map,List.finRange,List.map_ofFn]
   rfl
 theorem activeVertices_lookup {n : ℕ} (W : Finset (Fin n)) (i : Fin W.card) :
     ((activeVertices n (mask W)).drop i.val).headD 0=(activeMap W i).val := by
   rw [activeVertices_mask,sortedOwners_ofFn,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn]
   simp only [i.isLt,dif_pos,Option.getD_some]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ActiveGraphCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ActiveTransport

 def activeOwnerList : Realizer (fun s : GraphRoundingInput => s.2.2) := Realizer.snd.comp Realizer.snd
 def activeOrder : Realizer (fun s : GraphRoundingInput => s.2.2.length) := activeOwnerList.comp listLength
 def activeEnvironment : Realizer (fun s : GraphRoundingInput => (s.2.2,zipBits (vertexPairs s.1) s.2.1)) := activeOwnerList.pair originalTable
 def activeBits (s : GraphRoundingInput) : List Bool :=
   (vertexPairs s.2.2.length).map (fun p => roundedQuery (p,(s.2.2,zipBits (vertexPairs s.1) s.2.1)))
 def activeBitsRealizer : Realizer activeBits :=
   (((activeOrder.comp vertexPairsRealizer).pair activeEnvironment).comp (mapEnvironment roundedQueryRealizer))
 def activeGraphBits (s : GraphRoundingInput) : List Bool := encodeNat s.2.2.length++activeBits s
 def activeGraphRealizer : Realizer activeGraphBits := ((activeOrder.comp naturalCodeRealizer).pair activeBitsRealizer).comp appendBits
 theorem activeOrder_polynomial : PolyBound activeOrder := polynomial_comp (linear_polynomial (linear_comp linear_snd linear_snd)) listLength_polynomial
 theorem activeEnvironment_polynomial : PolyBound activeEnvironment := polynomial_pair
   (linear_polynomial (linear_comp linear_snd linear_snd)) originalTable_polynomial
 theorem activeBits_polynomial : PolyBound activeBitsRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp activeOrder_polynomial vertexPairs_polynomial) activeEnvironment_polynomial)
   (polynomial_mapEnvironment roundedQuery_polynomial)
 theorem activeGraph_polynomial : PolyBound activeGraphRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp activeOrder_polynomial naturalCode_polynomial) activeBits_polynomial) appendBits_polynomial
 theorem activeQuery_correct {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (i j : Fin W.card) :
     roundedQuery ((i.val,j.val),(activeVertices n (mask W),zipBits (vertexPairs n) (adjacencyBits G)))=
       decide ((activeGraph G W).Adj i j) := by
   dsimp only [roundedQuery]
   rw [activeVertices_lookup,activeVertices_lookup,table_original_any]
   rfl
 theorem activeGraph_correct {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) :
     activeGraphBits (n,(adjacencyBits G,activeVertices n (mask W)))=graphBits (activeGraph G W) := by
   have hl : (activeVertices n (mask W)).length=W.card := by rw [activeVertices_mask]; simp
   unfold activeGraphBits activeBits
   rw [hl,graphBits_eq,adjacencyBits_table (activeGraph G W)]
   apply congrArg (List.append (encodeNat W.card))
   apply List.map_congr_left
   intro p hp
   obtain ⟨hu,hv⟩ := vertexPairs_bounds W.card p hp
   rw [show adjacencyNat (activeGraph G W) p=decide ((activeGraph G W).Adj ⟨p.1,hu⟩ ⟨p.2,hv⟩) from
     adjacencyNat_fin (activeGraph G W) ⟨p.1,hu⟩ ⟨p.2,hv⟩]
   exact activeQuery_correct G W ⟨p.1,hu⟩ ⟨p.2,hv⟩
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ProjectionSemantics
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open WeightedHelpers

 noncomputable def natMask {N : ℕ} (J : Finset (Fin N)) (i : ℕ) : Bool :=
   if hi : i< N then decide ((⟨i,hi⟩ : Fin N)∈J) else false
 theorem mask_range {N : ℕ} (J : Finset (Fin N)) : mask J=(List.range N).map (natMask J) := by
   rw [map_range_ofFn]
   unfold mask
   apply congrArg List.ofFn
   funext i
   simp only [natMask,dif_pos i.isLt]
 theorem selectedCopies_eq {n : ℕ} (t : Fin n → ℕ) (J : Finset (Fin (totalCopies t))) (rest : List Bool) :
     selectedCopies (ownerIndices (List.ofFn t)) (mask J++rest)=(List.range (totalCopies t)).filter (natMask J) := by
   rw [selectedCopies,ownerIndices_length,mask_range,zipBits_map_append]
   simp only [selectTrue,List.filter_map,List.map_map,Function.comp_def,List.map_id]
   change ((List.range (totalCopies t)).filter (natMask J)).map id=_
   rw [List.map_id]
 theorem selectedCopies_mem {n : ℕ} (t : Fin n → ℕ) (J : Finset (Fin (totalCopies t))) (rest : List Bool) (k : ℕ) :
     k∈selectedCopies (ownerIndices (List.ofFn t)) (mask J++rest) ↔ ∃j∈J,j.val=k := by
   rw [selectedCopies_eq]
   simp only [List.mem_filter,List.mem_range]
   constructor
   · rintro ⟨hk,hm⟩
     refine ⟨⟨k,hk⟩,?_,rfl⟩
     simpa only [natMask,dif_pos hk,decide_eq_true_eq] using hm
   · rintro ⟨j,hj,rfl⟩
     exact ⟨j.isLt,by simpa only [natMask,dif_pos j.isLt,decide_eq_true_eq] using hj⟩
 theorem selectedOwners_mem {n : ℕ} (t : Fin n → ℕ) (J : Finset (Fin (totalCopies t))) (rest : List Bool) (v : Fin n) :
     v.val∈selectedOwners (ownerIndices (List.ofFn t)) (mask J++rest) ↔ v∈originalVertices t J := by
   rw [selectedOwners]
   simp only [List.mem_map,originalVertices,Finset.mem_filter,Finset.mem_univ,true_and]
   constructor
   · rintro ⟨k,hk,hv⟩
     obtain ⟨j,hj,hjk⟩ := (selectedCopies_mem t J rest k).mp hk
     subst k
     rw [ownerIndices_lookup] at hv
     have he : owner t j=v := Fin.ext hv
     exact ⟨j,hj,he ▸ owner_spec t j⟩
   · rintro ⟨j,hj,hv⟩
     refine ⟨j.val,(selectedCopies_mem t J rest j.val).mpr ⟨j,hj,rfl⟩,?_⟩
     rw [ownerIndices_lookup]
     exact congrArg Fin.val ((owner_eq_iff t j v).mpr hv)
 theorem containsOwner_true (xs : List ℕ) (v : ℕ) : containsOwner (v,xs)=true ↔ v∈xs := by
   dsimp only [containsOwner]
   simp
 theorem projectMask_correct {n : ℕ} (t : Fin n → ℕ) (J : Finset (Fin (totalCopies t))) (rest : List Bool) :
     projectMask n (List.ofFn t) (mask J++rest)=mask (originalVertices t J) := by
   rw [projectMask,map_range_ofFn]
   change List.ofFn (fun v : Fin n => containsOwner (v.val,selectedOwners (ownerIndices (List.ofFn t)) (mask J++rest)))=
     List.ofFn (fun v : Fin n => decide (v∈originalVertices t J))
   apply congrArg List.ofFn
   funext v
   apply Bool.eq_iff_iff.mpr
   simp only [decide_eq_true_eq,containsOwner_true,selectedOwners_mem]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ActiveProjection
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ActiveTransport

 theorem selectedCopies_list {m : ℕ} (owners : List ℕ) (hm : owners.length=m) (S : Finset (Fin m)) (rest : List Bool) :
     selectedCopies owners (mask S++rest)=(List.range m).filter (natMask S) := by
   rw [selectedCopies,hm,mask_range,zipBits_map_append]
   simp only [selectTrue,List.filter_map,List.map_map,Function.comp_def,List.map_id]
   change ((List.range m).filter (natMask S)).map id=_
   rw [List.map_id]
 theorem selectedCopies_list_mem {m : ℕ} (owners : List ℕ) (hm : owners.length=m) (S : Finset (Fin m)) (rest : List Bool) (v : ℕ) :
     v∈selectedCopies owners (mask S++rest) ↔ ∃i∈S,i.val=v := by
   rw [selectedCopies_list owners hm]
   simp only [List.mem_filter,List.mem_range]
   constructor
   · rintro ⟨hv,hs⟩
     exact ⟨⟨v,hv⟩,by simpa only [natMask,dif_pos hv,decide_eq_true_eq] using hs,rfl⟩
   · rintro ⟨i,hi,rfl⟩
     exact ⟨i.isLt,by simpa only [natMask,dif_pos i.isLt,decide_eq_true_eq] using hi⟩
 theorem activeSelected_mem {n : ℕ} (W : Finset (Fin n)) (S : Finset (Fin W.card)) (rest : List Bool) (v : Fin n) :
     v.val∈selectedOwners (activeVertices n (mask W)) (mask S++rest) ↔ v∈S.image (activeMap W) := by
   have hl : (activeVertices n (mask W)).length=W.card := by rw [activeVertices_mask]; simp
   unfold selectedOwners
   simp only [List.mem_map,Finset.mem_image]
   constructor
   · rintro ⟨k,hk,he⟩
     obtain ⟨i,hi,hek⟩ := (selectedCopies_list_mem _ hl S rest k).mp hk
     subst k
     rw [activeVertices_lookup] at he
     exact ⟨i,hi,Fin.ext he⟩
   · rintro ⟨i,hi,he⟩
     refine ⟨i.val,(selectedCopies_list_mem _ hl S rest i.val).mpr ⟨i,hi,rfl⟩,?_⟩
     rw [activeVertices_lookup,he]
 def projectOwnerMask (s : ℕ×(List ℕ×List Bool)) : List Bool :=
   (List.range s.1).map (fun v => containsOwner (v,selectedOwners s.2.1 s.2.2))
 def projectOwnerMaskRealizer : Realizer projectOwnerMask :=
   ((Realizer.fst.comp Realizer.range).pair (Realizer.snd.comp selectedOwnersRealizer)).comp (mapEnvironment containsOwnerRealizer)
 theorem projectOwnerMask_polynomial : PolyBound projectOwnerMaskRealizer :=
   polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) range_polynomial)
     (polynomial_comp (linear_polynomial linear_snd) selectedOwners_polynomial)) (polynomial_mapEnvironment containsOwner_polynomial)
 theorem projectOwnerMask_correct {n : ℕ} (W : Finset (Fin n)) (S : Finset (Fin W.card)) (rest : List Bool) :
     projectOwnerMask (n,(activeVertices n (mask W),mask S++rest))=mask (S.image (activeMap W)) := by
   rw [projectOwnerMask,map_range_ofFn]
   apply congrArg List.ofFn
   funext v
   apply Bool.eq_iff_iff.mpr
   simp only [decide_eq_true_eq,containsOwner_true,activeSelected_mem]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.WeightedParser
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev WeightedRaw := ℕ×(List Bool×(List SignedWords×SignedWords))
 def weightStreamRealizer : Realizer (fun L : List Bool => readMany (graphStart L).1 (graphStart L).2.2) :=
   (((graphStartRealizer.comp Realizer.fst).pair ((graphStartRealizer.comp Realizer.snd).comp Realizer.snd)).comp readManyRealizer)
 def weightedParse (L : List Bool) : WeightedRaw :=
   let g := graphStart L
   let w := readMany g.1 g.2.2
   (g.1,(g.2.1,(w.1,(readRational w.2).1)))
 def weightedParseRealizer : Realizer weightedParse :=
   (graphStartRealizer.comp Realizer.fst).pair
     (((graphStartRealizer.comp Realizer.snd).comp Realizer.fst).pair
       ((weightStreamRealizer.comp Realizer.fst).pair (((weightStreamRealizer.comp Realizer.snd).comp readRationalRealizer).comp Realizer.fst)))
 theorem weightStream_polynomial : PolyBound weightStreamRealizer :=
   polynomial_comp (polynomial_pair (polynomial_comp graphStart_polynomial (linear_polynomial linear_fst))
     (polynomial_comp (polynomial_comp graphStart_polynomial (linear_polynomial linear_snd)) (linear_polynomial linear_snd))) readMany_polynomial
 theorem weightedParse_polynomial : PolyBound weightedParseRealizer :=
   polynomial_pair (polynomial_comp graphStart_polynomial (linear_polynomial linear_fst))
     (polynomial_pair (polynomial_comp (polynomial_comp graphStart_polynomial (linear_polynomial linear_snd)) (linear_polynomial linear_fst))
       (polynomial_pair (polynomial_comp weightStream_polynomial (linear_polynomial linear_fst))
         (polynomial_comp (polynomial_comp (polynomial_comp weightStream_polynomial (linear_polynomial linear_snd)) readRational_polynomial)
           (linear_polynomial linear_fst))))
 theorem weightedParse_correct {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode) :
     weightedParse (weightedInput G w ε)=(n,(adjacencyBits G,((List.ofFn w).map codeWords,codeWords ε))) := by
   have he : rationalData w ε=(List.ofFn w).flatMap RationalCode.bits++ε.bits := by
     simp only [rationalData,List.flatMap_def,List.map_ofFn,Function.comp_def]
   dsimp only [weightedParse]
   rw [graphStart_weighted,he]
   have hm := readMany_codes (List.ofFn w) ε.bits
   simp only [List.length_ofFn] at hm
   rw [hm]
   have hr := readRational_code ε []
   simp only [List.append_nil] at hr
   rw [hr]
   rfl

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.DirectWeightedProgram
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def nonnegativeInput : Realizer (fun s : SignedWords => !s.1) := Realizer.fst.comp Realizer.not
 def weightsProjection : Realizer (fun x : WeightedRaw => x.2.2.1) := (Realizer.snd.comp Realizer.snd).comp Realizer.fst
 def directMaskRealizer : Realizer (fun L : List Bool => ((weightedParse L).2.2.1).map (fun s => !s.1)) :=
   (weightedParseRealizer.comp weightsProjection).comp (mapList nonnegativeInput)
 theorem directMask_polynomial : PolyBound directMaskRealizer :=
   polynomial_comp (polynomial_comp weightedParse_polynomial
     (linear_polynomial (linear_comp (linear_comp linear_snd linear_snd) linear_fst)))
     (polynomial_mapList (linear_polynomial (linear_comp linear_fst linear_not)))

 theorem code_nonnegative (q : RationalCode) : (!(codeWords q).1)=decide (0≤ q.value) := by
   have hd : (0 : ℚ)< q.denominator := by exact_mod_cast q.positive
   have hn : (0 : ℚ)≤ q.value ↔ (0 : ℤ)≤ q.numerator := by
     dsimp only [RationalCode.value]
     rw [le_div_iff₀ hd]
     simp
   by_cases hz : (0 : ℤ)≤ q.numerator
   · have hh : ¬q.numerator<0 := by omega
     simp [codeWords,hn,hz,hh]
   · have hh : q.numerator<0 := by omega
     simp [codeWords,hn,hz,hh]
 theorem directMask_correct {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode) :
     ((weightedParse (weightedInput G w ε)).2.2.1).map (fun s => !s.1)=mask (directVertices w) := by
   rw [weightedParse_correct]
   simp only [List.map_map,List.map_ofFn,Function.comp_def]
   change (List.ofFn (fun v => !(codeWords (w v)).1))=mask (directVertices w)
   simp only [mask,directVertices,Finset.mem_filter,Finset.mem_univ,true_and]
   apply congrArg List.ofFn
   funext v
   exact code_nonnegative (w v)

 theorem direct_mask_program : ∃ (P : EdgeSublinearMWIS.Main.Program) (K q : ℕ),0< K ∧ 0< q ∧
     ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode),
       Runs P (weightedInput G w ε) (mask (directVertices w)) (K*((weightedInput G w ε).length+1)^q) := by
   obtain ⟨P,K,q,hK,hq,hR⟩ := TreeToTM2.realizer_poly_program directMaskRealizer directMask_polynomial
   refine ⟨P,K,q,hK,hq,?_⟩
   intro n G w ε
   have hr := hR (weightedInput G w ε)
   rw [directMask_correct] at hr
   exact hr

 theorem rational_normalization_program : ∃ (P : EdgeSublinearMWIS.Main.Program) (K q : ℕ),0< K ∧ 0< q ∧
     ∀ c : RationalCode, Runs P c.bits (encodeRat c.value) (K*(c.bits.length+1)^q) := by
   obtain ⟨P,K,q,hK,hq,hR⟩ := TreeToTM2.realizer_poly_program normalizeInputRealizer normalizeInput_polynomial
   refine ⟨P,K,q,hK,hq,?_⟩
   intro c
   have hr := hR c.bits
   rw [normalizeInput_correct] at hr
   exact hr

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MultiplyRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem multiply_prefix_volume (A B : List Bool) (j : ℕ) (hj : j≤ B.length) :
     volume ((B.take j).foldl (fun s b => multiplyStep (b,s)) (A,[]))≤12*(A.length+B.length+1) := by
   let s := (B.take j).foldl (fun s b => multiplyStep (b,s)) (A,[])
   have hfirst := multiply_first_length A (B.take j) []
   have hsecond := multiply_prefix_length A B j
   have htake : (B.take j).length≤ B.length := by simpa only [List.length_take] using Nat.min_le_right j B.length
   have hvA := BinaryAdder.volume_bits s.1
   have hvB := BinaryAdder.volume_bits s.2
   change s.1.length=A.length+(B.take j).length at hfirst
   change s.2.length≤ A.length+B.length at hsecond
   change volume (s.1,s.2)≤ _
   simp only [volume_pair]
   omega

 theorem multiply_fold_time : ∃ C q : ℕ,0< C ∧ ∀ A B : List Bool,
     multiplyStepRealizer.fold.time (B,(A,[]))≤ C*(A.length+B.length+1)^q := by
   obtain ⟨C,q,hC,hpoly⟩ := multiplyStep_polynomial
   refine ⟨C*17^q+2000,q+2,by positivity,?_⟩
   intro A B
   let z := A.length+B.length+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hvB : volume B≤5*z := by have hh := BinaryAdder.volume_bits B; dsimp [z]; omega
   have hvA : volume A≤5*z := by have hh := BinaryAdder.volume_bits A; dsimp [z]; omega
   have hvol := multiply_prefix_volume A B
   have htime (j : ℕ) (hj : j< B.length) :
       multiplyStepRealizer.time (B[j],(B.take j).foldl (fun s b => multiplyStep (b,s)) (A,[]))≤ C*17^q*z^q := by
     have hh := (hpoly (B[j],(B.take j).foldl (fun s b => multiplyStep (b,s)) (A,[]))).1
     have hb := volume_bool B[j]
     have hs := hvol j hj.le
     have hv : volume (B[j],(B.take j).foldl (fun s b => multiplyStep (b,s)) (A,[]))+1≤17*z := by
       simp only [volume_pair]
       change _≤17*z
       change _≤12*z at hs
       omega
     have hp := Nat.pow_le_pow_left hv q
     have ht := hh.trans (Nat.mul_le_mul_left C hp)
     simpa only [mul_pow,Nat.mul_assoc] using ht
   have hf := fold_prefix_bound multiplyStepRealizer B (A,[]) (C*17^q*z^q) (12*z) hvol htime
   have hBL : B.length≤ z := by dsimp [z]; omega
   have hq1 : z^(q+1)≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hq2 : z^2≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hzgrow : z≤ z^2 := by nlinarith
   have hmul : B.length*(C*17^q*z^q+20*(volume B+2*(12*z)+1))≤ z*(C*17^q*z^q+600*z) := by
     apply Nat.mul_le_mul hBL
     omega
   have hqprod : z*(C*17^q*z^q)=C*17^q*z^(q+1) := by rw [pow_succ]; ring
   have hf' : Realizer.foldTime multiplyStepRealizer (A,[]) B≤(C*17^q+1000)*z^(q+2) := by
     have ht := Nat.mul_le_mul_left (C*17^q) hq1
     have hc := Nat.mul_le_mul_left 1000 hq2
     simp only [Nat.mul_add,hqprod] at hmul
     nlinarith only [hf,hmul,ht,hc,hzgrow,hz]
   rw [Realizer.time_fold]
   simp only [volume_pair,volume_nil]
   change _≤(C*17^q+2000)*z^(q+2)
   have hpow : z≤ z^(q+2) := hzgrow.trans hq2
   nlinarith only [hf',hvA,hvB,hpow,hz]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MultiplyTotalRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem multiplyInitial_linear : Linear multiplyInitial := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : List Bool×List Bool => ([] : List Bool))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   exact linear_pair linear_snd (linear_pair linear_fst hn)

 theorem multiply_time : ∃ C q : ℕ,0< C ∧ ∀ A B : List Bool,
     multiplyRealizer.time (A,B)≤ C*(A.length+B.length+1)^q := by
   obtain ⟨C,q,hC,hfold⟩ := multiply_fold_time
   obtain ⟨I,hI,hinit⟩ := multiplyInitial_linear
   let post := (Realizer.snd : Realizer (Prod.snd : List Bool×List Bool → List Bool)).comp trimRealizer
   have hp : PolyBound post := polynomial_comp (linear_polynomial linear_snd) trim_polynomial
   obtain ⟨D,r,hD,hpost⟩ := hp
   let e := q+r+2
   refine ⟨5*I+C+D*13^r+1000,e,by positivity,?_⟩
   intro A B
   let z := A.length+B.length+1
   let initial : List Bool×(List Bool×List Bool) := (B,(A,[]))
   let final := B.foldl (fun s b => multiplyStep (b,s)) (A,[])
   have hz : 1≤ z := by dsimp [z]; omega
   have he1 : 1≤ e := by dsimp [e]; omega
   have hq : z^q≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hr : z^r≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hze : z≤ z^e := by simpa only [pow_one] using Nat.pow_le_pow_right hz he1
   have hA := BinaryAdder.volume_bits A
   have hB := BinaryAdder.volume_bits B
   have hvx : volume (A,B)≤4*z := by simp only [volume_pair]; dsimp [z]; omega
   have hvi : volume initial≤6*z := by dsimp [initial]; simp only [volume_pair,volume_nil]; dsimp [z]; omega
   have hvf : volume final≤12*z := by
     have hh := multiply_prefix_volume A B B.length le_rfl
     simpa only [List.take_length] using hh
   have hi : multiplyInitial.time (A,B)≤5*I*z^e := by
     have hh := (hinit (A,B)).1
     have hh' := hh.trans (Nat.mul_le_mul_left I (show volume (A,B)+1≤5*z by omega))
     exact hh'.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left (5*I) hze)
   have hf : multiplyStepRealizer.fold.time initial≤ C*z^e := (hfold A B).trans (Nat.mul_le_mul_left C hq)
   have ho : post.time final≤ D*13^r*z^e := by
     have hh := (hpost final).1
     have hbase : volume final+1≤13*z := by omega
     have hh' := hh.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hbase r))
     simp only [mul_pow] at hh'
     exact hh'.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*13^r) hr)
   have hcopy : 10*(volume initial+1)+10*(volume final+1)≤1000*z^e := by omega
   have heq : multiplyRealizer.time (A,B)=multiplyInitial.time (A,B)+multiplyStepRealizer.fold.time initial+
       10*(volume initial+1)+post.time final+10*(volume final+1) := by
     dsimp only [multiplyRealizer,multiply]
     simp only [Realizer.time_congr,Realizer.time_comp,Function.comp_apply]
     dsimp only [post,initial,final]
     rw [Realizer.time_comp]
     ring
   rw [heq]
   change _≤(5*I+C+D*13^r+1000)*z^e
   nlinarith only [hi,hf,ho,hcopy]

 theorem multiply_polynomial : PolyBound multiplyRealizer := by
   obtain ⟨C,q,hC,hT⟩ := multiply_time
   refine ⟨C+5,q+1,by omega,?_⟩
   rintro ⟨A,B⟩
   let z := volume (A,B)+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hA := bits_length_volume A
   have hB := bits_length_volume B
   have hbase : A.length+B.length+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hp : (A.length+B.length+1)^q≤ z^(q+1) := (Nat.pow_le_pow_left hbase q).trans (Nat.pow_le_pow_right hz (by omega))
   have ht := (hT A B).trans (Nat.mul_le_mul_left C hp)
   have hv := BinaryAdder.volume_bits (multiply A B)
   have hlen := multiply_length A B
   have hpow : z≤ z^(q+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+1)
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (multiply A B)≤ _
     have hv' : volume (multiply A B)≤5*z^(q+1) := by omega
     exact hv'.trans (Nat.mul_le_mul_right _ (by omega))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.WeightedExecutionMath
noncomputable section

open scoped BigOperators Classical
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.WeightedHelpers
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.WeightedExecutionMath

 theorem clipped_value (w : RationalCode) : (clippedCode w).value = max w.value 0 := by
  have hd : (0 : ℚ) < w.denominator := by exact_mod_cast w.positive
  unfold clippedCode RationalCode.value
  push_cast
  rw [← max_div_div_right (le_of_lt hd)]
  simp

 theorem clipped_nonneg {n : ℕ} (w : Fin n → RationalCode) (v : Fin n) : 0 ≤ clippedValues w v := by
  simp only [clippedValues, clipped_value]
  exact le_max_right _ _

 theorem half_value (ε : RationalCode) : (halfAccuracy ε).value = ε.value / 2 := by
  unfold halfAccuracy RationalCode.value
  push_cast
  ring

 theorem clipped_alpha {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) :
    weightedAlpha G (clippedValues w) = weightedAlpha G (fun v => (w v).value) := by
  unfold weightedAlpha weightedAlphaOn
  apply csSup_eq_csSup_of_forall_exists_le
  · rintro x ⟨I, hI, hi, rfl⟩
    let J := I.filter (fun v => 0 ≤ (w v).value)
    refine ⟨∑ v ∈ J, ((w v).value : ℝ), ⟨J, Finset.subset_univ _, hi.mono (by intro v hv; exact (Finset.mem_filter.mp hv).1), rfl⟩, ?_⟩
    have heq : (∑ v ∈ I, (clippedValues w v : ℝ)) = ∑ v ∈ J, ((w v).value : ℝ) := by
      dsimp [J]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro v hv
      simp only [clippedValues, clipped_value]
      split_ifs with h
      · rw [max_eq_left h]
      · rw [max_eq_right (le_of_not_ge h)]
        simp
    exact heq.le
  · rintro x ⟨I, hI, hi, rfl⟩
    refine ⟨∑ v ∈ I, (clippedValues w v : ℝ), ⟨I, hI, hi, rfl⟩, ?_⟩
    apply Finset.sum_le_sum
    intro v hv
    simp only [clippedValues, clipped_value]
    exact_mod_cast (le_max_left (w v).value 0)

 theorem nonpositive_alpha {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (hw : ∀ v, w v ≤ 0) : weightedAlpha G w = 0 := by
  apply le_antisymm
  · apply csSup_le
    · exact ⟨0, ∅, Finset.empty_subset _, by simp, by simp⟩
    · rintro x ⟨I, hI, hi, rfl⟩
      exact Finset.sum_nonpos (fun v hv => by exact_mod_cast hw v)
  · have h := weightedAlpha_member G Finset.univ w ∅ (Finset.empty_subset _) (by simp)
    simpa [weightedAlpha] using h

 theorem alpha_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ) : 0 ≤ weightedAlpha G w := by
  have h := weightedAlpha_member G Finset.univ w ∅ (Finset.empty_subset _) (by simp)
  simpa [weightedAlpha] using h

 theorem direct_correct {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode)
    (hn : n ≤ 1) : G.IsIndepSet (directVertices w : Set (Fin n)) ∧
      weightedAlpha G (fun v => (w v).value) = ∑ v ∈ directVertices w, ((w v).value : ℝ) := by
  have hind : G.IsIndepSet (directVertices w : Set (Fin n)) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro u hu v hv hne
    have hu' := u.isLt
    have hv' := v.isLt
    have heq : u = v := Fin.ext (by omega)
    exact False.elim (hne heq)
  refine ⟨hind, le_antisymm ?_ ?_⟩
  · apply csSup_le
    · exact ⟨0, ∅, Finset.empty_subset _, by simp, by simp⟩
    · rintro x ⟨I, hI, hi, rfl⟩
      have hsum1 : (∑ v ∈ I, ((w v).value : ℝ)) ≤ ∑ v ∈ I, (clippedValues w v : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        simp only [clippedValues, clipped_value]
        exact_mod_cast (le_max_left (w v).value 0)
      have hsum2 : (∑ v ∈ I, (clippedValues w v : ℝ)) ≤ ∑ v : Fin n, (clippedValues w v : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v hv hnot => by exact_mod_cast clipped_nonneg w v)
      have heq : (∑ v : Fin n, (clippedValues w v : ℝ)) = ∑ v ∈ directVertices w, ((w v).value : ℝ) := by
        unfold directVertices
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro v hv
        simp only [clippedValues, clipped_value]
        split_ifs with h
        · rw [max_eq_left h]
        · rw [max_eq_right (le_of_not_ge h)]
          simp
      exact hsum1.trans (hsum2.trans heq.le)
  · exact weightedAlpha_member G Finset.univ _ (directVertices w) (Finset.subset_univ _) hind

 theorem projection_original_weights {n : ℕ} (w : Fin n → RationalCode) (τ : ℚ) (t : Fin n → ℕ)
    (ht : ∀ v, t v = ⌊clippedValues w v / τ⌋₊) (J : Finset (Fin (totalCopies t))) :
    (∑ v ∈ originalVertices t J, (clippedValues w v : ℝ)) =
      ∑ v ∈ originalVertices t J, ((w v).value : ℝ) := by
  apply Finset.sum_congr rfl
  intro v hv
  have hnon : 0 ≤ (w v).value := by
    by_contra hh
    have hneg : (w v).value ≤ 0 := le_of_lt (lt_of_not_ge hh)
    have hz : clippedValues w v = 0 := by simp [clippedValues, clipped_value, max_eq_right hneg]
    have htv : t v = 0 := by rw [ht v, hz]; simp
    obtain ⟨j, hj, howner⟩ := (Finset.mem_filter.mp hv).2
    have hown := (owner_eq_iff t j v).mpr howner
    have hp := owner_positive t j
    rw [hown, htv] at hp
    omega
  simp only [clippedValues, clipped_value, max_eq_left hnon]

 theorem rounding_large {n : ℕ} (w : Fin n → ℚ) (ε τ : ℚ) (t : Fin n → ℕ)
    (hn : 2 ≤ n) (hmax : 0 < maximumWeight w) (he : 0 < ε) (he1 : ε < 1)
    (hτ : 0 < τ) (hscale : τ = ε * maximumWeight w / (2 * (n : ℚ)))
    (ht : ∀ v, t v = ⌊w v / τ⌋₊) : 2 ≤ totalCopies t := by
  obtain ⟨v, hv⟩ := max_weight_attained w hmax
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (n : ℚ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hnq)
  have hscaled : τ * (2 * (n : ℚ)) = ε * maximumWeight w := by rw [hscale]; field_simp
  have hmul : ε * maximumWeight w < maximumWeight w := by nlinarith
  have h2τ : 2 * τ ≤ w v := by rw [← hv]; nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr hnq)]
  have htwo : 2 ≤ t v := by
    rw [ht]
    apply Nat.le_floor
    exact (le_div_iff₀ hτ).mpr (by simpa [mul_comm] using h2τ)
  apply htwo.trans
  exact Finset.single_le_sum (fun v hv => Nat.zero_le _) (Finset.mem_univ _)

end EdgeSublinearMWIS.Main.WeightedExecutionMath
end

-- Solutions.BinaryFractions
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev FractionWords := List Bool×List Bool
 def fractionValue (s : FractionWords) : ℚ := (value s.1 : ℚ)/(value s.2 : ℚ)
 def clipWords (s : SignedWords) : FractionWords := (if s.1 then [] else s.2.1,s.2.2)
 def clipWordsRealizer : Realizer clipWords :=
   ((Realizer.fst.pair Realizer.id).comp ((Realizer.nil.choose (Realizer.snd.comp Realizer.fst)))).pair
     ((Realizer.snd.comp Realizer.snd))
 theorem clipWords_polynomial : PolyBound clipWordsRealizer := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : SignedWords => ([] : List Bool))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   exact polynomial_pair
     (polynomial_comp (polynomial_pair (linear_polynomial linear_fst) (linear_polynomial linear_id))
       (polynomial_choose (linear_polynomial hn) (linear_polynomial (linear_comp linear_snd linear_fst))))
     (linear_polynomial (linear_comp linear_snd linear_snd))
 theorem fractionValue_code (q : RationalCode) : fractionValue (clipWords (codeWords q))=(clippedCode q).value := by
   dsimp only [fractionValue,clipWords,codeWords]
   simp only [value_natBits]
   by_cases h : q.numerator<0
   · simp [h,value,RationalCode.value,clippedCode,max_eq_right (by omega : q.numerator≤0)]
   · have hn : (0 : ℤ)≤ q.numerator := by omega
     have hc : (q.numerator.natAbs : ℚ)=(q.numerator : ℚ) := by
       have hz : (q.numerator.natAbs : ℤ)=q.numerator := by rw [Int.natCast_natAbs,abs_of_nonneg hn]
       simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hz
     simp [h,RationalCode.value,clippedCode,max_eq_left hn,value_natBits,hc]


 def fractionMul (s : FractionWords×FractionWords) : FractionWords :=
   (multiply s.1.1 s.2.1,multiply s.1.2 s.2.2)
 def fractionMulRealizer : Realizer fractionMul :=
   ((((Realizer.fst.comp Realizer.fst).pair (Realizer.snd.comp Realizer.fst)).comp multiplyRealizer).pair
     (((Realizer.fst.comp Realizer.snd).pair (Realizer.snd.comp Realizer.snd)).comp multiplyRealizer))
 theorem fractionMul_polynomial : PolyBound fractionMulRealizer :=
   polynomial_pair
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst linear_fst) (linear_comp linear_snd linear_fst))) multiply_polynomial)
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst linear_snd) (linear_comp linear_snd linear_snd))) multiply_polynomial)
 theorem fractionMul_value (s t : FractionWords) : fractionValue (fractionMul (s,t))=fractionValue s*fractionValue t := by
   dsimp only [fractionMul,fractionValue]
   rw [multiply_value,multiply_value]
   push_cast
   ring

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FractionAddition
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def sumWords (A B : List Bool) : List Bool := trim (BinaryAdder.word A B)
 theorem sumWords_value (A B : List Bool) : value (sumWords A B)=value A+value B := by
   rw [sumWords,trim_value,BinaryAdder.word_value]
 theorem sumWords_length (A B : List Bool) : (sumWords A B).length≤ max A.length B.length+1 := by
   unfold sumWords
   apply trim_length_of_lt
   rw [BinaryAdder.word_value,pow_succ]
   have hA := (value_lt A).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.le_max_left A.length B.length))
   have hB := (value_lt B).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.le_max_right A.length B.length))
   omega
 def sumWordsRealizer : Realizer (fun s : List Bool×List Bool => sumWords s.1 s.2) :=
   BinaryAdder.wordRealizer.comp trimRealizer
 theorem sumWords_polynomial : PolyBound sumWordsRealizer := polynomial_comp word_polynomial trim_polynomial

 def fractionAdd (s : FractionWords×FractionWords) : FractionWords :=
   (sumWords (multiply s.1.1 s.2.2) (multiply s.2.1 s.1.2),multiply s.1.2 s.2.2)
 theorem fractionAdd_value (s t : FractionWords) (hs : value s.2≠0) (ht : value t.2≠0) :
     fractionValue (fractionAdd (s,t))=fractionValue s+fractionValue t := by
   dsimp only [fractionValue,fractionAdd]
   rw [sumWords_value,multiply_value,multiply_value,multiply_value]
   push_cast
   have hsQ : (value s.2 : ℚ)≠0 := by exact_mod_cast hs
   have htQ : (value t.2 : ℚ)≠0 := by exact_mod_cast ht
   field_simp

 def fractionAddLeft : Realizer (fun s : FractionWords×FractionWords => multiply s.1.1 s.2.2) :=
   ((Realizer.fst.comp Realizer.fst).pair (Realizer.snd.comp Realizer.snd)).comp multiplyRealizer
 def fractionAddRight : Realizer (fun s : FractionWords×FractionWords => multiply s.2.1 s.1.2) :=
   ((Realizer.snd.comp Realizer.fst).pair (Realizer.fst.comp Realizer.snd)).comp multiplyRealizer
 def fractionAddDen : Realizer (fun s : FractionWords×FractionWords => multiply s.1.2 s.2.2) :=
   ((Realizer.fst.comp Realizer.snd).pair (Realizer.snd.comp Realizer.snd)).comp multiplyRealizer
 def fractionAddRealizer : Realizer fractionAdd :=
   ((fractionAddLeft.pair fractionAddRight).comp sumWordsRealizer).pair fractionAddDen
 theorem fractionAdd_polynomial : PolyBound fractionAddRealizer := by
   have h1 : PolyBound fractionAddLeft := polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst linear_fst) (linear_comp linear_snd linear_snd))) multiply_polynomial
   have h2 : PolyBound fractionAddRight := polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) (linear_comp linear_fst linear_snd))) multiply_polynomial
   have h3 : PolyBound fractionAddDen := polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst linear_snd) (linear_comp linear_snd linear_snd))) multiply_polynomial
   exact polynomial_pair (polynomial_comp (polynomial_pair h1 h2) sumWords_polynomial) h3

 def fractionWidth (s : FractionWords) : ℕ := max s.1.length s.2.length+1
 theorem fractionAdd_width (s t : FractionWords) :
     fractionWidth (fractionAdd (s,t))≤ fractionWidth s+fractionWidth t := by
   have hn := sumWords_length (multiply s.1 t.2) (multiply t.1 s.2)
   have h1 := multiply_length s.1 t.2
   have h2 := multiply_length t.1 s.2
   have hd := multiply_length s.2 t.2
   dsimp only [fractionWidth,fractionAdd]
   omega
 theorem fractionWidth_le_volume (s : FractionWords) : fractionWidth s≤ volume s := by
   have ha := bits_length_volume s.1
   have hb := bits_length_volume s.2
   change fractionWidth s≤ volume (s.1,s.2)
   simp only [fractionWidth,volume_pair]
   omega
 theorem fractionVolume_le_width (s : FractionWords) : volume s≤10*fractionWidth s := by
   have ha := BinaryAdder.volume_bits s.1
   have hb := BinaryAdder.volume_bits s.2
   change volume (s.1,s.2)≤10*fractionWidth s
   simp only [volume_pair,fractionWidth]
   omega

 theorem fractionAdd_fold_width (xs : List FractionWords) (s : FractionWords) :
     fractionWidth (xs.foldl (fun s a => fractionAdd (a,s)) s)≤ fractionWidth s+(xs.map fractionWidth).sum := by
   induction xs generalizing s with
   | nil => simp
   | cons a xs ih =>
     rw [List.foldl_cons]
     have hh := ih (fractionAdd (a,s))
     have ha := fractionAdd_width a s
     simp only [List.map_cons,List.sum_cons]
     omega
 theorem fractionWidths_sum (xs : List FractionWords) : (xs.map fractionWidth).sum≤ volume xs := by
   induction xs with
   | nil => simp
   | cons a xs ih =>
     simp only [List.map_cons,List.sum_cons,volume_cons]
     have hh := fractionWidth_le_volume a
     omega
 theorem fractionAdd_fold_polynomial : PolyBound fractionAddRealizer.fold := by
   apply polynomial_fold_bounded fractionAdd_polynomial 10
   intro xs s j hj
   have hv := fractionVolume_le_width ((xs.take j).foldl (fun s a => fractionAdd (a,s)) s)
   have hw := fractionAdd_fold_width (xs.take j) s
   have hs := fractionWidth_le_volume s
   have hx := fractionWidths_sum (xs.take j)
   have ht : volume (xs.take j)≤ volume xs := by
     have hh := volume_append (xs.take j) (xs.drop j)
     rw [List.take_append_drop] at hh
     have hp := volume_pos (xs.drop j)
     omega
   simp only [volume_pair]
   nlinarith
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryCeiling
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem natCeil_ratio (n d : ℕ) (hd : 0< d) : ⌈(n:ℚ)/(d:ℚ)⌉₊=(n+d-1)/d := by
   rw [← Nat.ceilDiv_eq_add_pred_div]
   have hdQ : (0:ℚ)< d := by exact_mod_cast hd
   apply le_antisymm
   · apply Nat.ceil_le.mpr
     rw [div_le_iff₀ hdQ]
     have hh : n≤(n⌈/⌉d)*d := by
       simpa only [Nat.mul_comm] using (ceilDiv_le_iff_le_mul hd).mp (le_refl (n⌈/⌉d))
     exact_mod_cast hh
   · apply (ceilDiv_le_iff_le_mul hd).mpr
     have hh := Nat.le_ceil ((n:ℚ)/(d:ℚ))
     rw [div_le_iff₀ hdQ] at hh
     have hhNat : n≤⌈(n:ℚ)/(d:ℚ)⌉₊*d := by exact_mod_cast hh
     simpa only [Nat.mul_comm] using hhNat
 def ceilFraction (s : FractionWords) : List Bool :=
   (divide (sumWords s.1 (BinarySubtract.difference s.2 [true])) s.2).1
 def ceilFractionRealizer : Realizer ceilFraction :=
   ((((Realizer.fst.pair ((Realizer.snd.pair (Realizer.constant [true])).comp BinarySubtract.differenceRealizer)).comp sumWordsRealizer).pair Realizer.snd).comp divideRealizer).comp Realizer.fst
 theorem ceilFraction_polynomial : PolyBound ceilFractionRealizer :=
   polynomial_comp (polynomial_comp (polynomial_pair (polynomial_comp
     (polynomial_pair (linear_polynomial linear_fst) (polynomial_comp
       (linear_polynomial (linear_pair linear_snd (linear_constant _))) BinarySubtract.difference_polynomial)) sumWords_polynomial)
     (linear_polynomial linear_snd)) divide_polynomial) (linear_polynomial linear_fst)
 theorem ceilFraction_value (s : FractionWords) (hs : 0< value s.2) : value (ceilFraction s)=⌈fractionValue s⌉₊ := by
   rw [ceilFraction,(divide_value _ _ hs).1,sumWords_value,BinarySubtract.difference_value]
   simp only [value,Bool.toNat_true,Nat.mul_zero,Nat.add_zero]
   rw [fractionValue,natCeil_ratio _ _ hs]
   congr 1
   omega
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryHeight
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds HeightMath

 abbrev HeightState := ℕ×(List Bool×(List Bool×Bool))
 def heightDone (s : HeightState) : Bool := s.2.2.2 || !BinarySubtract.less s.2.2.1 s.2.1
 def heightStep (s : HeightState) : HeightState :=
   if heightDone s then (s.1,(s.2.1,(s.2.2.1,true)))
   else (s.1+1,(false::s.2.1,(multiply s.2.2.1 [true,true],false)))
 def heightInitial (n : ℕ) : HeightState := (0,(natBits n,([true],false)))
 def heightRun (n j : ℕ) : HeightState := heightStep^[j] (heightInitial n)
 theorem heightRun_succ (n j : ℕ) : heightRun n (j+1)=heightStep (heightRun n j) := by
   unfold heightRun
   rw [Function.iterate_succ_apply']
 theorem heightDone_false (s : HeightState) (hs : s.2.2.2=false) (h : value s.2.2.1< value s.2.1) : heightDone s=false := by
   have hh := (BinarySubtract.less_iff _ _).mpr h
   simp only [heightDone,hs,hh,Bool.not_true,Bool.false_or]
 theorem heightDone_true (s : HeightState) (h : value s.2.1≤ value s.2.2.1) : heightDone s=true := by
   have hh : BinarySubtract.less s.2.2.1 s.2.1=false := by
     apply Bool.eq_false_iff.mpr
     intro hc
     have hc' := (BinarySubtract.less_iff _ _).mp hc
     omega
   simp only [heightDone,hh,Bool.not_false,Bool.or_true]
 theorem height_before (n j : ℕ) (hj : j≤ height n) :
     (heightRun n j).1=j ∧ (heightRun n j).2.2.2=false ∧
       value (heightRun n j).2.1=2^j*n ∧ value (heightRun n j).2.2.1=3^j := by
   induction j with
   | zero => simp [heightRun,heightInitial,value_natBits,value]
   | succ j ih =>
     obtain ⟨hi,hd,hA,hB⟩ := ih (by omega)
     have hbad := height_minimal n j (by omega)
     have hval : value (heightRun n j).2.2.1< value (heightRun n j).2.1 := by rw [hA,hB]; omega
     have hs := heightDone_false (heightRun n j) hd hval
     rw [heightRun_succ]
     simp only [heightStep,hs,Bool.false_eq_true,if_false,hi,value,multiply_value,hA,hB,pow_succ]
     norm_num
     ring
 theorem heightStep_fixed (s : HeightState) (hs : s.2.2.2=true) : heightStep s=s := by
   have hh : heightDone s=true := by simp [heightDone,hs]
   simp only [heightStep,hh,if_true]
   rcases s with ⟨i,A,B,d⟩
   dsimp only at hs ⊢
   rw [hs]
 theorem height_after (n : ℕ) :
     (heightRun n (height n+1)).1=height n ∧ (heightRun n (height n+1)).2.2.2=true := by
   obtain ⟨hi,hd,hA,hB⟩ := height_before n (height n) le_rfl
   have hc : value (heightRun n (height n)).2.1≤ value (heightRun n (height n)).2.2.1 := by rw [hA,hB]; exact height_spec n
   have hh := heightDone_true (heightRun n (height n)) hc
   rw [heightRun_succ]
   simp only [heightStep,hh,if_true,hi,and_self]
 theorem height_computed (n : ℕ) : (heightRun n (2*n+1)).1=height n := by
   obtain ⟨hi,hd⟩ := height_after n
   have hfixed := heightStep_fixed (heightRun n (height n+1)) hd
   have hle : height n+1≤2*n+1 := by have := height_le_twice n; omega
   obtain ⟨d,he⟩ := Nat.exists_eq_add_of_le hle
   have he' : 2*n+1=d+(height n+1) := by omega
   rw [he']
   unfold heightRun
   rw [Function.iterate_add_apply]
   have hfd : heightStep^[d] (heightRun n (height n+1))=heightRun n (height n+1) := Function.iterate_fixed hfixed d
   exact (congrArg Prod.fst hfd).trans hi
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryHeightCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def heightA : Realizer (fun s : HeightState => s.2.1) := Realizer.snd.comp Realizer.fst
 def heightB : Realizer (fun s : HeightState => s.2.2.1) := (Realizer.snd.comp Realizer.snd).comp Realizer.fst
 def heightFlag : Realizer (fun s : HeightState => s.2.2.2) := (Realizer.snd.comp Realizer.snd).comp Realizer.snd
 theorem heightA_linear : Linear heightA := linear_comp linear_snd linear_fst
 theorem heightB_linear : Linear heightB := linear_comp (linear_comp linear_snd linear_snd) linear_fst
 theorem heightFlag_linear : Linear heightFlag := linear_comp (linear_comp linear_snd linear_snd) linear_snd
 def heightDoneRealizer : Realizer heightDone :=
   (heightFlag.pair (((heightB.pair heightA).comp BinarySubtract.lessRealizer).comp Realizer.not)).comp Realizer.or
 theorem heightDone_polynomial : PolyBound heightDoneRealizer :=
   polynomial_comp (polynomial_pair (linear_polynomial heightFlag_linear)
     (polynomial_comp (polynomial_comp (linear_polynomial (linear_pair heightB_linear heightA_linear)) BinarySubtract.less_polynomial)
       (linear_polynomial linear_not))) (linear_polynomial linear_or)
 def heightStay : Realizer (fun s : HeightState => (s.1,(s.2.1,(s.2.2.1,true)))) :=
   Realizer.fst.pair (heightA.pair (heightB.pair (Realizer.constant true)))
 def heightAdvance : Realizer (fun s : HeightState => (s.1+1,(false::s.2.1,(multiply s.2.2.1 [true,true],false)))) :=
   (Realizer.fst.comp Realizer.succ).pair
     (((Realizer.constant false).pair heightA).comp Realizer.cons |>.pair
       (((heightB.pair (Realizer.constant [true,true])).comp multiplyRealizer).pair (Realizer.constant false)))
 def heightStepRealizer : Realizer heightStep := (heightDoneRealizer.pair Realizer.id).comp (heightStay.choose heightAdvance)
 theorem heightStep_polynomial : PolyBound heightStepRealizer := by
   have hs : Linear heightStay := linear_pair linear_fst (linear_pair heightA_linear (linear_pair heightB_linear (linear_constant true)))
   have ha : PolyBound heightAdvance := polynomial_pair
     (linear_polynomial (linear_comp linear_fst succ_linear))
     (polynomial_pair (linear_polynomial (linear_comp (linear_pair (linear_constant false) heightA_linear) linear_cons))
       (polynomial_pair (polynomial_comp (linear_polynomial (linear_pair heightB_linear (linear_constant _))) multiply_polynomial)
         (linear_polynomial (linear_constant false))))
   exact polynomial_comp (polynomial_pair heightDone_polynomial (linear_polynomial linear_id))
     (polynomial_choose (linear_polynomial hs) ha)
 theorem heightStep_sizes (s : HeightState) :
     (heightStep s).1≤ s.1+1 ∧ (heightStep s).2.1.length≤ s.2.1.length+1 ∧
       (heightStep s).2.2.1.length≤ s.2.2.1.length+2 := by
   unfold heightStep
   split_ifs
   · simp
   · simp only [List.length_cons]
     have hh := multiply_length s.2.2.1 [true,true]
     simpa only [List.length_cons,List.length_nil] using And.intro (le_refl (s.1+1)) (And.intro (le_refl (s.2.1.length+1)) hh)
 theorem heightIter_sizes (s : HeightState) (j : ℕ) :
     (heightStep^[j] s).1≤ s.1+j ∧ (heightStep^[j] s).2.1.length≤ s.2.1.length+j ∧
       (heightStep^[j] s).2.2.1.length≤ s.2.2.1.length+2*j := by
   induction j with
   | zero => simp
   | succ j ih =>
     rw [Function.iterate_succ_apply']
     have hh := heightStep_sizes (heightStep^[j] s)
     omega
 theorem heightIter_volume (s : HeightState) (j : ℕ) : volume (heightStep^[j] s)≤20*(volume s+j+1)^1 := by
   have hs := heightIter_sizes s j
   have hA := BinaryAdder.volume_bits (heightStep^[j] s).2.1
   have hB := BinaryAdder.volume_bits (heightStep^[j] s).2.2.1
   have hd := volume_bool (heightStep^[j] s).2.2.2
   have hAs := bits_length_volume s.2.1
   have hBs := bits_length_volume s.2.2.1
   have he : volume (heightStep^[j] s)=volume ((heightStep^[j] s).1,((heightStep^[j] s).2.1,((heightStep^[j] s).2.2.1,(heightStep^[j] s).2.2.2))) := rfl
   rw [he]
   change _≤20*(volume (s.1,(s.2.1,(s.2.2.1,s.2.2.2)))+j+1)^1
   simp only [volume_pair,volume_nat,pow_one]
   omega
 theorem heightIterator_polynomial : PolyBound heightStepRealizer.iterate :=
   polynomial_iterate_growth heightStep_polynomial 20 1 heightIter_volume
 def heightInitialRealizer : Realizer heightInitial :=
   (Realizer.constant 0).pair (naturalWordRealizer.pair ((Realizer.constant [true]).pair (Realizer.constant false)))
 theorem heightInitial_polynomial : PolyBound heightInitialRealizer :=
   polynomial_pair (linear_polynomial (linear_constant 0))
     (polynomial_pair naturalWord_polynomial (linear_polynomial (linear_pair (linear_constant _) (linear_constant false))))
 def heightBudget : Realizer (fun n : ℕ => 2*n+1) :=
   (((Realizer.id.pair Realizer.id).comp Realizer.add).comp Realizer.succ).congr (fun n => by simp only [Function.comp_apply,id_eq]; omega)
 theorem heightBudget_polynomial : PolyBound heightBudget := by
   unfold heightBudget
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp (linear_polynomial (linear_pair linear_id linear_id)) BinaryGcd.nat_add_polynomial) (linear_polynomial succ_linear)
 def heightRealizer : Realizer height :=
   (((heightBudget.pair heightInitialRealizer).comp heightStepRealizer.iterate).comp Realizer.fst).congr (fun n => height_computed n)
 theorem height_polynomial : PolyBound heightRealizer := by
   unfold heightRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp (polynomial_pair heightBudget_polynomial heightInitial_polynomial) heightIterator_polynomial)
     (linear_polynomial linear_fst)
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialFoldSelect
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

 theorem fold_select_mem (f : α×α → α) (h : ∀a b,f (a,b)=a ∨ f (a,b)=b) (xs : List α) (b : α) :
     xs.foldl (fun b a => f (a,b)) b=b ∨ xs.foldl (fun b a => f (a,b)) b∈xs := by
   induction xs generalizing b with
   | nil => exact Or.inl rfl
   | cons a xs ih =>
     rw [List.foldl_cons]
     rcases ih (f (a,b)) with he|hm
     · rw [he]
       rcases h a b with ha|hb
       · exact Or.inr (by simp [ha])
       · exact Or.inl hb
     · exact Or.inr (List.mem_cons_of_mem a hm)

 theorem polynomial_fold_select {f : α×α → α} {R : Realizer f} (hR : PolyBound R)
     (hf : ∀a b,f (a,b)=a ∨ f (a,b)=b) : PolyBound R.fold := by
   obtain ⟨C,q,hC,hR⟩ := hR
   refine ⟨C*3^q+1000,q+2,by positivity,?_⟩
   rintro ⟨xs,b⟩
   let z := volume (xs,b)+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hlen : xs.length≤ z := by have hh := length_volume xs; dsimp [z]; simp only [volume_pair]; omega
   have hbase : volume xs+volume b+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hv (j : ℕ) (_hj : j≤ xs.length) : volume ((xs.take j).foldl (fun b a => f (a,b)) b)≤ z := by
     rcases fold_select_mem f hf (xs.take j) b with he|hm
     · rw [he]; omega
     · have hm' : (xs.take j).foldl (fun b a => f (a,b)) b∈xs := List.mem_of_mem_take hm
       exact (volume_mem_le hm').trans (by omega)
   have ht (j : ℕ) (hj : j< xs.length) :
       R.time (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)≤ C*3^q*z^q := by
     have ha := volume_mem_le (List.getElem_mem hj)
     have hb := hv j hj.le
     have he : volume (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)+1≤3*z := by simp only [volume_pair]; omega
     have hh := ((hR _).1).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left he q))
     simpa only [mul_pow,Nat.mul_assoc] using hh
   have hh := fold_prefix_bound R xs b (C*3^q*z^q) z hv ht
   have hp1 : z^(q+1)≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hp2 : z^2≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hp : z≤ z^(q+2) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+2)
   change volume (xs,b)+1≤ z^(q+2) at hp
   have hm := Nat.mul_le_mul hlen (show C*3^q*z^q+20*(volume xs+2*z+1)≤ C*3^q*z^q+100*z by omega)
   have he : z*(C*3^q*z^q+100*z)=C*3^q*z^(q+1)+100*z^2 := by rw [pow_succ]; ring
   rw [he] at hm
   have htime := Nat.mul_le_mul_left (C*3^q) hp1
   have hcopy := Nat.mul_le_mul_left 100 hp2
   constructor
   · rw [Realizer.time_fold]
     change 2*volume (xs,b)+6+Realizer.foldTime R b xs≤(C*3^q+1000)*z^(q+2)
     nlinarith only [hh,hm,htime,hcopy,hp,hz]
   · change volume (xs.foldl (fun b a => f (a,b)) b)≤ _
     have hv' := hv xs.length le_rfl
     rw [List.take_length] at hv'
     exact hv'.trans (hp.trans (Nat.le_mul_of_pos_left _ (by positivity)))

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.FiniteArrayCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem fold_reverse_head {α : Type} (L : List α) (a : α) :
     L.reverse.foldl (fun _ b => b) a=L.headD a := by
   cases L with
   | nil => rfl
   | cons b L => rw [List.reverse_cons,List.foldl_append]; rfl
 def headList {α : Type} [Coding α] (a : α) : Realizer (fun L : List α => L.headD a) :=
   ((Realizer.reverse.pair (Realizer.constant a)).comp Realizer.fst.fold).congr (fun L => fold_reverse_head L a)
 theorem headList_polynomial {α : Type} [Coding α] (a : α) : PolyBound (headList a) := by
   unfold headList
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair reverse_polynomial_generic (linear_polynomial (linear_constant a)))
     (polynomial_fold_select (linear_polynomial linear_fst) (fun _ _ => Or.inl rfl))

 def equalWord (s : List Bool×List Bool) : Bool := !(BinarySubtract.less s.1 s.2 || BinarySubtract.less s.2 s.1)
 def equalWordRealizer : Realizer equalWord :=
   ((BinarySubtract.lessRealizer.pair (((Realizer.snd.pair Realizer.fst).comp BinarySubtract.lessRealizer))).comp Realizer.or).comp Realizer.not
 theorem equalWord_polynomial : PolyBound equalWordRealizer :=
   polynomial_comp (polynomial_comp (polynomial_pair BinarySubtract.less_polynomial
     (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) BinarySubtract.less_polynomial))
     (linear_polynomial linear_or)) (linear_polynomial linear_not)
 theorem equalWord_iff (A B : List Bool) : equalWord (A,B)=true ↔ value A=value B := by
   have hA : BinarySubtract.less A B=decide (value A< value B) := by
     apply Bool.eq_iff_iff.mpr
     simpa only [decide_eq_true_eq] using BinarySubtract.less_iff A B
   have hB : BinarySubtract.less B A=decide (value B< value A) := by
     apply Bool.eq_iff_iff.mpr
     simpa only [decide_eq_true_eq] using BinarySubtract.less_iff B A
   by_cases h : value A=value B
   · simp [equalWord,hA,hB,h]
   · rcases lt_or_gt_of_ne h with hlt|hgt
     · simp [equalWord,hA,hB,hlt,h]
     · simp [equalWord,hA,hB,hgt,h]
 theorem value_injective_length (A B : List Bool) (hl : A.length=B.length) (hv : value A=value B) : A=B := by
   induction A generalizing B with
   | nil => cases B <;> simp_all
   | cons a A ih =>
     cases B with
     | nil => simp_all
     | cons b B =>
       have hab : a=b ∧ value A=value B := by cases a <;> cases b <;> simp only [value,Bool.toNat_false,Bool.toNat_true] at hv ⊢ <;> first | omega | (refine ⟨trivial, ?_⟩; omega)
       simp only [List.length_cons,Nat.add_right_cancel_iff] at hl
       rw [hab.1,ih B hl hab.2]
 theorem equalWord_same_length (A B : List Bool) (hl : A.length=B.length) : equalWord (A,B)=true ↔ A=B := by
   rw [equalWord_iff]
   exact ⟨value_injective_length A B hl,fun h => congrArg value h⟩

 def subsetMask (n : ℕ) (A : List ℕ) : List Bool := (List.range n).map (fun v => containsOwner (v,A))
 def subsetMaskRealizer : Realizer (fun s : ℕ×List ℕ => subsetMask s.1 s.2) :=
   ((Realizer.fst.comp Realizer.range).pair Realizer.snd).comp (mapEnvironment containsOwnerRealizer)
 theorem subsetMask_polynomial : PolyBound subsetMaskRealizer :=
   polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) range_polynomial)
     (linear_polynomial linear_snd)) (polynomial_mapEnvironment containsOwner_polynomial)
 theorem subsetMask_length (n : ℕ) (A : List ℕ) : (subsetMask n A).length=n := by simp [subsetMask]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FractionCompare
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def fractionLE (x : FractionWords×FractionWords) : Bool :=
   !BinarySubtract.less (multiply x.2.1 x.1.2) (multiply x.1.1 x.2.2)
 def crossLeft : Realizer (fun x : FractionWords×FractionWords => multiply x.1.1 x.2.2) :=
   ((Realizer.fst.comp Realizer.fst).pair (Realizer.snd.comp Realizer.snd)).comp multiplyRealizer
 def crossRight : Realizer (fun x : FractionWords×FractionWords => multiply x.2.1 x.1.2) :=
   ((Realizer.snd.comp Realizer.fst).pair (Realizer.fst.comp Realizer.snd)).comp multiplyRealizer
 def fractionLERealizer : Realizer fractionLE :=
   (((crossRight.pair crossLeft).comp BinarySubtract.lessRealizer).comp Realizer.not)
 theorem fractionLE_polynomial : PolyBound fractionLERealizer :=
   polynomial_comp (polynomial_comp (polynomial_pair
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) (linear_comp linear_fst linear_snd))) multiply_polynomial)
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst linear_fst) (linear_comp linear_snd linear_snd))) multiply_polynomial))
       BinarySubtract.less_polynomial) (linear_polynomial linear_not)

 theorem fractionLE_correct (s t : FractionWords) (hs : 0< value s.2) (ht : 0< value t.2) :
     fractionLE (s,t)=true ↔ fractionValue s≤ fractionValue t := by
   have hdiv : fractionValue s≤ fractionValue t ↔ value s.1*value t.2≤ value t.1*value s.2 := by
     dsimp only [fractionValue]
     rw [div_le_div_iff₀ (by exact_mod_cast hs : (0 : ℚ)< value s.2) (by exact_mod_cast ht : (0 : ℚ)< value t.2)]
     norm_cast
   have hc := BinarySubtract.less_iff (multiply t.1 s.2) (multiply s.1 t.2)
   rw [multiply_value,multiply_value] at hc
   rw [hdiv]
   dsimp only [fractionLE]
   cases h : BinarySubtract.less (multiply t.1 s.2) (multiply s.1 t.2) <;> simp_all <;> omega

 def fractionFloor (s : FractionWords) : List Bool := (divide s.1 s.2).1
 def fractionFloorRealizer : Realizer fractionFloor := divideRealizer.comp Realizer.fst
 theorem fractionFloor_polynomial : PolyBound fractionFloorRealizer := polynomial_comp divide_polynomial (linear_polynomial linear_fst)
 theorem fractionFloor_correct (s : FractionWords) (hs : 0< value s.2) :
     value (fractionFloor s)=⌊fractionValue s⌋₊ := by
   rw [fractionFloor,(divide_value _ _ hs).1,fractionValue,Nat.floor_div_natCast,Nat.floor_natCast]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FractionMaximum
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def maxFractionStep (s : FractionWords×FractionWords) : FractionWords := if fractionLE s then s.2 else s.1
 def maxFractionStepRealizer : Realizer maxFractionStep :=
   (fractionLERealizer.pair Realizer.id).comp (Realizer.snd.choose Realizer.fst)
 theorem maxFractionStep_polynomial : PolyBound maxFractionStepRealizer :=
   polynomial_comp (polynomial_pair fractionLE_polynomial (linear_polynomial linear_id))
     (polynomial_choose (linear_polynomial linear_snd) (linear_polynomial linear_fst))
 theorem maxFractionStep_select (a b : FractionWords) : maxFractionStep (a,b)=a ∨ maxFractionStep (a,b)=b := by
   unfold maxFractionStep
   split_ifs <;> simp
 theorem maxFractionStep_den (a b : FractionWords) (ha : 0< value a.2) (hb : 0< value b.2) :
     0< value (maxFractionStep (a,b)).2 := by
   rcases maxFractionStep_select a b with h|h <;> rw [h] <;> assumption
 theorem maxFractionStep_value (a b : FractionWords) (ha : 0< value a.2) (hb : 0< value b.2) :
     fractionValue (maxFractionStep (a,b))=max (fractionValue a) (fractionValue b) := by
   unfold maxFractionStep
   by_cases h : fractionLE (a,b)=true
   · rw [if_pos h,max_eq_right ((fractionLE_correct a b ha hb).mp h)]
   · rw [if_neg h,max_eq_left (le_of_not_ge (fun hh => h ((fractionLE_correct a b ha hb).mpr hh)))]
 theorem maxFraction_fold (xs : List FractionWords) (b : FractionWords)
     (hxs : ∀a∈xs,0< value a.2) (hb : 0< value b.2) :
     0< value (xs.foldl (fun b a => maxFractionStep (a,b)) b).2 ∧
     fractionValue (xs.foldl (fun b a => maxFractionStep (a,b)) b)=
       (xs.map fractionValue).foldl max (fractionValue b) := by
   induction xs generalizing b with
   | nil => exact ⟨hb,rfl⟩
   | cons a xs ih =>
     have ha := hxs a (by simp)
     have ht := ih (maxFractionStep (a,b)) (fun a ha => hxs a (by simp [ha])) (maxFractionStep_den a b ha hb)
     simp only [List.foldl_cons,List.map_cons]
     refine ⟨ht.1,?_⟩
     rw [ht.2,maxFractionStep_value a b ha hb,max_comm (fractionValue a) (fractionValue b)]

 def zeroFraction : FractionWords := ([],[true])
 def maximumFraction (xs : List FractionWords) : FractionWords := xs.foldl (fun b a => maxFractionStep (a,b)) zeroFraction
 def maximumFractionRealizer : Realizer maximumFraction := (Realizer.id.pair (Realizer.constant zeroFraction)).comp maxFractionStepRealizer.fold
 theorem maximumFraction_polynomial : PolyBound maximumFractionRealizer :=
   polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial (linear_constant zeroFraction)))
     (polynomial_fold_select maxFractionStep_polynomial maxFractionStep_select)
 theorem maximumFraction_value (xs : List FractionWords) (hxs : ∀a∈xs,0< value a.2) :
     0< value (maximumFraction xs).2 ∧ fractionValue (maximumFraction xs)=(xs.map fractionValue).foldl max 0 := by
   simpa [maximumFraction,zeroFraction,fractionValue,value] using maxFraction_fold xs zeroFraction hxs (by decide)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.CoordinateArrayCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def lookupList {α : Type} [Coding α] (a : α) : Realizer (fun s : List α×ℕ => (s.1.drop s.2).headD a) :=
   dropList.comp (headList a)
 theorem lookupList_polynomial {α : Type} [Coding α] (a : α) : PolyBound (lookupList a) :=
   polynomial_comp dropList_polynomial (headList_polynomial a)
 abbrev CoordinateTable := List (List Bool×FractionWords)
 def coordinatePair : Realizer (fun s : ℕ×(List (List Bool)×List FractionWords) =>
     ((s.2.1.drop s.1).headD [],(s.2.2.drop s.1).headD zeroFraction)) :=
   ((((Realizer.snd.comp Realizer.fst).pair Realizer.fst).comp (lookupList [])).pair
     (((Realizer.snd.comp Realizer.snd).pair Realizer.fst).comp (lookupList zeroFraction)))
 theorem coordinatePair_polynomial : PolyBound coordinatePair :=
   polynomial_pair
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) linear_fst)) (lookupList_polynomial []))
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd linear_snd) linear_fst)) (lookupList_polynomial zeroFraction))
 def coordinateTable (keys : List (List Bool)) (vals : List FractionWords) : CoordinateTable :=
   (List.range keys.length).map (fun i => ((keys.drop i).headD [],(vals.drop i).headD zeroFraction))
 def coordinateTableRealizer : Realizer (fun s : List (List Bool)×List FractionWords => coordinateTable s.1 s.2) :=
   (((Realizer.fst.comp listLength).comp Realizer.range).pair Realizer.id).comp (mapEnvironment coordinatePair)
 theorem coordinateTable_polynomial : PolyBound coordinateTableRealizer :=
   polynomial_comp (polynomial_pair
     (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) listLength_polynomial) range_polynomial)
     (linear_polynomial linear_id)) (polynomial_mapEnvironment coordinatePair_polynomial)
 def coordinateMatches : Realizer (fun s : (List Bool×FractionWords)×List Bool => equalWord (s.1.1,s.2)) :=
   ((Realizer.fst.comp Realizer.fst).pair Realizer.snd).comp equalWordRealizer
 def coordinateLookup (tab : CoordinateTable) (key : List Bool) : FractionWords :=
   ((tab.filter (fun e => equalWord (e.1,key))).map Prod.snd).headD zeroFraction
 def coordinateLookupRealizer : Realizer (fun s : CoordinateTable×List Bool => coordinateLookup s.1 s.2) :=
   (((filterEnvironment coordinateMatches).comp (mapList Realizer.snd)).comp (headList zeroFraction))
 theorem coordinateLookup_polynomial : PolyBound coordinateLookupRealizer :=
   polynomial_comp (polynomial_comp (filterEnvironment_polynomial
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst linear_fst) linear_snd)) equalWord_polynomial))
     (polynomial_mapList (linear_polynomial linear_snd))) (headList_polynomial zeroFraction)

 theorem coordinateTable_map (keys : List (List Bool)) (f : List Bool → FractionWords) :
     coordinateTable keys (keys.map f)=keys.map (fun key => (key,f key)) := by
   apply List.ext_getElem
   · simp [coordinateTable]
   · intro i hi hj
     simp only [coordinateTable,List.getElem_map,List.getElem_range]
     have hi' : i< keys.length := by simpa [coordinateTable] using hi
     have hkey : (keys.drop i).headD []=keys[i] := by
       rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi']
       rfl
     have hval : ((keys.map f).drop i).headD zeroFraction=f keys[i] := by
       rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem (by simpa using hi')]
       simp only [Option.getD_some,List.getElem_map]
     rw [hkey,hval]
end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 theorem coordinateLookup_map (keys : List (List Bool)) (f : List Bool → FractionWords)
     (key : List Bool) (hlen : ∀a∈keys,a.length=key.length) (hkey : key∈keys) :
     coordinateLookup (keys.map (fun a => (a,f a))) key=f key := by
   induction keys with
   | nil => simp at hkey
   | cons a keys ih =>
     by_cases ha : a=key
     · subst a
       have he : equalWord (key,key)=true := (equalWord_iff _ _).mpr rfl
       simp [coordinateLookup,he]
     · have he : equalWord (a,key)=false := by
         apply Bool.eq_false_iff.mpr
         intro hh
         exact ha ((equalWord_same_length _ _ (hlen a (by simp))).mp hh)
       have hh := ih (fun b hb => hlen b (List.mem_cons_of_mem a hb)) (by rcases List.mem_cons.mp hkey with hh|hh; exact False.elim (ha hh.symm); exact hh)
       simpa [coordinateLookup,he] using hh
end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 theorem coordinateTable_map_pair {α : Type} (xs : List α) (key : α → List Bool) (val : α → FractionWords) :
     coordinateTable (xs.map key) (xs.map val)=xs.map (fun a => (key a,val a)) := by
   apply List.ext_getElem
   · simp [coordinateTable]
   · intro i hi hj
     have hi' : i< xs.length := by simpa [coordinateTable] using hi
     simp only [coordinateTable,List.getElem_map,List.getElem_range]
     rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem (by simpa using hi'),
       List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem (by simpa using hi')]
     simp only [Option.getD_some,List.getElem_map]
 theorem coordinateLookup_spec (tab : CoordinateTable) (key : List Bool) (v : FractionWords)
     (hex : (key,v)∈tab) (hall : ∀e∈tab,e.1.length=key.length ∧ (e.1=key → e.2=v)) :
     coordinateLookup tab key=v := by
   induction tab with
   | nil => simp at hex
   | cons e tab ih =>
     have he := hall e (by simp)
     by_cases hk : e.1=key
     · have hb : equalWord (e.1,key)=true := (equalWord_same_length _ _ he.1).mpr hk
       simp [coordinateLookup,hb,he.2 hk]
     · have hb : equalWord (e.1,key)=false := by
         apply Bool.eq_false_iff.mpr
         intro hh
         exact hk ((equalWord_same_length _ _ he.1).mp hh)
       have hm : (key,v)∈tab := by
         rcases List.mem_cons.mp hex with hh|hh
         · exact False.elim (hk (congrArg Prod.fst hh).symm)
         · exact hh
       have hh := ih hm (fun a ha => hall a (List.mem_cons_of_mem e ha))
       simpa [coordinateLookup,hb] using hh
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BoundedSublists
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def boundedSublists {α : Type} (L : List α) (k : ℕ) : List (List α) := L.sublists.filter (fun A => A.length≤ k)
 theorem boundedSublists_nil {α : Type} (k : ℕ) : boundedSublists ([] : List α) k=[[]] := by simp [boundedSublists]
 theorem boundedSublists_concat {α : Type} (L : List α) (k : ℕ) (a : α) :
     boundedSublists (L++[a]) k=boundedSublists L k++
       ((boundedSublists L k).filter (fun A => A.length< k)).map (fun A => A++[a]) := by
   simp only [boundedSublists,List.sublists_concat,List.filter_append,List.filter_map,List.length_append,List.length_singleton,List.filter_filter]
   congr 2
   apply congrArg (fun p : List α → Bool => L.sublists.filter p)
   funext A
   simp only [← Bool.decide_and]
   apply decide_eq_decide.mpr
   simp only [List.length_append,List.length_singleton]
   omega

 def subsetStep (x : ℕ×(ℕ×List (List ℕ))) : ℕ×List (List ℕ) :=
   (x.2.1,x.2.2++((x.2.2.filter (fun A => A.length< x.2.1)).map (fun A => A++[x.1])))
 def appendVertexRealizer : Realizer (fun x : List ℕ×ℕ => x.1++[x.2]) :=
   (Realizer.fst.pair ((Realizer.snd.pair Realizer.nil).comp Realizer.cons)).comp appendList
 def subsetLengthTest : Realizer (fun x : List ℕ×ℕ => decide (x.1.length< x.2)) :=
   ((Realizer.fst.comp listLength).pair Realizer.snd).comp ltNatRealizer
 def subsetCandidates : Realizer (fun x : ℕ×(ℕ×List (List ℕ)) => x.2.2.filter (fun A => A.length< x.2.1)) :=
   ((Realizer.snd.comp Realizer.snd).pair (Realizer.snd.comp Realizer.fst)).comp (filterEnvironment subsetLengthTest)
 def subsetNew : Realizer (fun x : ℕ×(ℕ×List (List ℕ)) =>
     ((x.2.2.filter (fun A => A.length< x.2.1)).map (fun A => A++[x.1]))) :=
   (subsetCandidates.pair Realizer.fst).comp (mapEnvironment appendVertexRealizer)
 def subsetStepRealizer : Realizer subsetStep :=
   (Realizer.snd.comp Realizer.fst).pair (((Realizer.snd.comp Realizer.snd).pair subsetNew).comp appendList)
 theorem subsetStep_polynomial : PolyBound subsetStepRealizer := by
   have ha : PolyBound appendVertexRealizer := by
     have hn : Linear (Realizer.nil : Realizer (fun _ : List ℕ×ℕ => ([] : List ℕ))) :=
       linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
     exact polynomial_comp (linear_polynomial (linear_pair linear_fst (linear_comp (linear_pair linear_snd hn) linear_cons))) appendList_polynomial
   have hl : PolyBound subsetLengthTest := polynomial_comp
     (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) listLength_polynomial) (linear_polynomial linear_snd)) ltNat_polynomial
   have hc : PolyBound subsetCandidates := polynomial_comp
     (linear_polynomial (linear_pair (linear_comp linear_snd linear_snd) (linear_comp linear_snd linear_fst)))
     (filterEnvironment_polynomial hl)
   have hn : PolyBound subsetNew := polynomial_comp (polynomial_pair hc (linear_polynomial linear_fst)) (polynomial_mapEnvironment ha)
   exact polynomial_pair (linear_polynomial (linear_comp linear_snd linear_fst))
     (polynomial_comp (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_snd)) hn) appendList_polynomial)
 theorem subsetStep_correct (L : List ℕ) (k a : ℕ) :
     subsetStep (a,(k,boundedSublists L k))=(k,boundedSublists (L++[a]) k) := by
   rw [boundedSublists_concat]
   rfl
 theorem subsetFold_correct (L baseList : List ℕ) (k : ℕ) :
     L.foldl (fun s a => subsetStep (a,s)) (k,boundedSublists baseList k)=(k,boundedSublists (baseList++L) k) := by
   induction L generalizing baseList with
   | nil => simp
   | cons a L ih => rw [List.foldl_cons,subsetStep_correct,ih]; simp [List.append_assoc]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BoundedCoordinateMath
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 theorem coordinateList_bounded {n : ℕ} (W : Finset (Fin n)) (r : ℕ) :
     coordinateList W r=(boundedSublists (W.sort (·≤·)) (r+2)).map List.toFinset := by
   unfold coordinateList boundedSublists
   rw [List.filter_map]
   apply congrArg (List.map List.toFinset)
   apply List.filter_congr
   intro A hA
   have hsub := List.mem_sublists.mp hA
   have hn := (Finset.sort_nodup W (·≤·)).sublist hsub
   simp only [Function.comp_apply,List.toFinset_card_of_nodup hn]

 theorem coordinateList_length {n : ℕ} (W : Finset (Fin n)) (r : ℕ) :
     (coordinateList W r).length=(boundedSublists (W.sort (·≤·)) (r+2)).length := by
   rw [coordinateList_bounded,List.length_map]

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 theorem boundedSublists_map {α β : Type} (f : α → β) (L : List α) (k : ℕ) :
     (boundedSublists L k).map (List.map f)=boundedSublists (L.map f) k := by
   simp only [boundedSublists,List.sublists_map,List.filter_map,Function.comp_def,List.length_map]

 theorem boundedFinRange_val (n k : ℕ) :
     (boundedSublists (List.finRange n) k).map (List.map Fin.val)=boundedSublists (List.range n) k := by
   rw [boundedSublists_map,OAI.ThreeMachine.StackCompiler.finRange_val]

 theorem encodeRat_nonempty (q : ℚ) : 1≤(encodeRat q).length := by
   simp only [encodeRat,encodeInt,List.length_append,List.length_singleton]
   omega

 theorem coordinateCount_le_input {n : ℕ} (W : Finset (Fin n)) (r : ℕ) (y : Finset (Fin n) → ℚ) :
     (coordinateList W r).length≤(encodePoint W r y).length := by
   change (coordinateList W r).length≤((coordinateList W r).flatMap (fun A => encodeRat (y A))).length
   generalize coordinateList W r=L
   induction L with
   | nil => simp
   | cons A L ih =>
     simp only [List.flatMap_cons,List.length_append,List.length_cons]
     have hh := encodeRat_nonempty (y A)
     omega
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ConditioningExistence
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.ConditioningMoments
open ConditioningEntropy

 theorem low_energy {n : ℕ} (G : SimpleGraph (Fin n)) (r k p : ℕ) (y : Finset (Fin n) → ℝ)
    (hy : Relaxation G Finset.univ r k y) (hr : 1≤ r) (hk : 1≤ k) (hp : 1≤ p)
    (budget : 2*p*logTwo n ≤ (r:ℝ)) :
    ∃ A : Finset (Fin n),A.card≤ r ∧ 0< y A ∧
      (∀v,0≤ costs y A v ∧ costs y A v≤1) ∧ (∑v,costs y A v)=(k:ℝ) ∧
      edgeEnergy G (costs y A) ≤ (k:ℝ)^2/p := by
  have hk0 : 0< k := by omega
  have hp0 : 0< p := by omega
  have hpR : (0:ℝ)< p := by exact_mod_cast hp0
  have hy0 : y (∅ : Finset (Fin n))=1 := hy.1
  have hprob0 := marginal_probability G r k y hy ∅ (by simp) (by rw [hy0]; norm_num) hk0
  have hbounds0 := ConditioningEntropy.Bounds.entropy_bounds _ hprob0
  have hlogeq : Real.logb 2 n=logTwo n := by rw [Real.logb,logTwo]
  rw [hlogeq] at hbounds0
  suffices hgood : ∃ A : Finset (Fin n),A.card≤ r ∧ 0< y A ∧ edgeEnergy G (costs y A) ≤ (k:ℝ)^2/p by
    obtain ⟨A,hA,hpos,he⟩ := hgood
    have hi := invariants G r k y hy A hA hpos
    exact ⟨A,hA,hpos,hi.1,hi.2.1,he⟩
  by_contra hn
  push Not at hn
  have hstep : ∀t : ℕ,t≤ r → ∃ A : Finset (Fin n),A.card≤ t ∧ 0< y A ∧
      entropy (marginal y A k) ≤ entropy (marginal y ∅ k)-(t:ℝ)/p ∧
      (0< t → entropy (marginal y A k) < entropy (marginal y ∅ k)-(t:ℝ)/p) := by
    intro t
    induction t with
    | zero =>
      intro ht
      exact ⟨∅,by simp,by rw [hy0]; norm_num,by simp,by simp⟩
    | succ t ih =>
      intro ht
      obtain ⟨A,hA,hpos,hH,_⟩ := ih (by omega)
      obtain ⟨v,hnext,hdrop⟩ := entropy_decrease G r k p y hy A (by omega) hpos hk0 hp0 (hn A (by omega) hpos)
      have htwo : (2:ℝ)/p=2*(1/p) := by ring
      rw [htwo] at hdrop
      have hstrict : entropy (marginal y (insert v A) k) < entropy (marginal y ∅ k)-((t+1:ℕ):ℝ)/p := by
        push_cast
        have hfrac : 0<1/(p:ℝ) := one_div_pos.mpr hpR
        rw [add_div]
        linarith
      exact ⟨insert v A,(Finset.card_insert_le v A).trans (by omega),hnext,hstrict.le,fun _ => hstrict⟩
  obtain ⟨A,hA,hpos,_,hstrict⟩ := hstep r le_rfl
  have hnonneg := (ConditioningEntropy.Bounds.entropy_bounds _ (marginal_probability G r k y hy A hA hpos hk0)).1
  have hlog : 0≤ logTwo n := by linarith [hbounds0.1,hbounds0.2]
  have hbudget : logTwo n ≤ (r:ℝ)/p := (le_div_iff₀ hpR).mpr (by nlinarith)
  have hf := hstrict (by omega)
  linarith

end EdgeSublinearMWIS.Main.ConditioningMoments
end

-- Solutions.ConditioningChoice
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.ConditioningMoments

 theorem coordinate_mem {n : ℕ} (W A : Finset (Fin n)) (r : ℕ)
    (hAW : A⊆W) (hA : A.card≤ r+2) : A∈coordinateList W r := by
  let l := (W.sort (·≤·)).filter (fun v => decide (v∈A))
  have hsub : l.Sublist (W.sort (·≤·)) := List.filter_sublist
  have heq : l.toFinset=A := by ext v; simp [l]; exact fun h => hAW h
  apply List.mem_filter.mpr
  refine ⟨List.mem_map.mpr ⟨l,List.mem_sublists.mpr hsub,heq⟩,by simpa using hA⟩

 theorem energy_div {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) (k : ℝ) :
    edgeEnergy G (fun v => x v/k)=edgeEnergy G x/k^2 := by
  unfold edgeEnergy
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  ring

 def passes {n : ℕ} (G : SimpleGraph (Fin n)) (r k p : ℕ) (y : Finset (Fin n) → ℚ) (A : Finset (Fin n)) : Prop :=
  A.card≤ r ∧ 0< y A ∧ (p:ℚ)*(∑ e∈((Finset.univ : Finset (Fin n×Fin n)).filter (fun e => e.1< e.2 ∧ G.Adj e.1 e.2)),y (insert e.1 A)*y (insert e.2 A)) ≤ (k:ℚ)^2*y A^2

 theorem passes_iff {n : ℕ} (G : SimpleGraph (Fin n)) (r k p : ℕ) (y : Finset (Fin n) → ℚ) (A : Finset (Fin n)) (hp : 1≤ p) :
    passes G r k p y A ↔ A.card≤ r ∧ 0<(y A:ℝ) ∧ edgeEnergy G (costs (fun A => (y A:ℝ)) A) ≤ (k:ℝ)^2/p := by
  have hpR : (0:ℝ)< p := by exact_mod_cast (by omega : 0< p)
  have hnum : edgeEnergy G (fun v => (y (insert v A):ℝ)) =
    ((∑ e∈((Finset.univ : Finset (Fin n×Fin n)).filter (fun e => e.1< e.2 ∧ G.Adj e.1 e.2)),y (insert e.1 A)*y (insert e.2 A)):ℚ) := by
    unfold edgeEnergy
    push_cast
    rfl
  have hform : edgeEnergy G (costs (fun A => (y A:ℝ)) A)=edgeEnergy G (fun v => (y (insert v A):ℝ))/(y A:ℝ)^2 := energy_div G _ _
  constructor
  · rintro ⟨hA,hpos,hineq⟩
    have hposR : (0:ℝ)< y A := by exact_mod_cast hpos
    refine ⟨hA,hposR,?_⟩
    rw [hform]
    apply (div_le_div_iff₀ (sq_pos_of_pos hposR) hpR).mpr
    rw [hnum]
    exact_mod_cast (show (∑ e∈((Finset.univ : Finset (Fin n×Fin n)).filter (fun e => e.1< e.2 ∧ G.Adj e.1 e.2)),y (insert e.1 A)*y (insert e.2 A))*(p:ℚ) ≤ (k:ℚ)^2*y A^2 by nlinarith only [hineq])
  · rintro ⟨hA,hpos,hineq⟩
    refine ⟨hA,by exact_mod_cast hpos,?_⟩
    rw [hform] at hineq
    have hh := (div_le_div_iff₀ (sq_pos_of_pos hpos) hpR).mp hineq
    rw [hnum] at hh
    have hh' : (p:ℝ)*((∑ e∈((Finset.univ : Finset (Fin n×Fin n)).filter (fun e => e.1< e.2 ∧ G.Adj e.1 e.2)),y (insert e.1 A)*y (insert e.2 A)):ℚ) ≤ (k:ℝ)^2*(y A:ℝ)^2 := by nlinarith only [hh]
    exact_mod_cast hh'

 theorem choice_eq_find {n : ℕ} (G : SimpleGraph (Fin n)) (r k p : ℕ) (y : Finset (Fin n) → ℚ) :
    conditioningChoice G Finset.univ r k p y=(coordinateList Finset.univ r).find? (fun A => decide (passes G r k p y A)) := by
  unfold conditioningChoice
  dsimp only
  have he : ((Finset.univ : Finset (Fin n×Fin n)).filter (fun e => e.1∈(Finset.univ : Finset (Fin n)) ∧ e.2∈(Finset.univ : Finset (Fin n)) ∧ e.1< e.2 ∧ G.Adj e.1 e.2)) = Finset.univ.filter (fun e => e.1< e.2 ∧ G.Adj e.1 e.2) := by ext e; simp
  rw [he]
  apply List.find?_congr
  intro A hA
  exact decide_eq_decide.mpr Iff.rfl

 theorem choice_exists {n : ℕ} (G : SimpleGraph (Fin n)) (r k p : ℕ) (y : Finset (Fin n) → ℚ)
    (hy : Relaxation G Finset.univ r k (fun A => (y A:ℝ))) (hr : 1≤ r) (hk : 1≤ k) (hp : 1≤ p)
    (budget : 2*p*logTwo n≤(r:ℝ)) : ∃ A,conditioningChoice G Finset.univ r k p y=some A ∧ passes G r k p y A := by
  obtain ⟨A,hA,hpos,_,_,he⟩ := low_energy G r k p _ hy hr hk hp budget
  have hpass := (passes_iff G r k p y A hp).mpr ⟨hA,hpos,he⟩
  have hmem := coordinate_mem Finset.univ A r (Finset.subset_univ _) (by omega)
  rw [choice_eq_find]
  have hn : (coordinateList (Finset.univ : Finset (Fin n)) r).find? (fun A => decide (passes G r k p y A)) ≠ none := by
    intro hh
    have hbad := List.find?_eq_none.mp hh A hmem
    exact hbad (by simp only [decide_eq_true_eq]; exact hpass)
  obtain ⟨B,hB⟩ := Option.ne_none_iff_exists'.mp hn
  exact ⟨B,hB,by simpa only [decide_eq_true_eq] using List.find?_some hB⟩

end EdgeSublinearMWIS.Main.ConditioningMoments

namespace EdgeSublinearMWIS.Main.ConditioningMoments
 theorem choice_spec {n : ℕ} (G : SimpleGraph (Fin n)) (r k p : ℕ) (y : Finset (Fin n) → ℚ)
    (hy : Relaxation G Finset.univ r k (fun A => (y A:ℝ))) (hr : 1≤ r) (hk : 1≤ k) (hp : 1≤ p)
    (budget : 2*p*logTwo n≤(r:ℝ)) :
    ∃ A,conditioningChoice G Finset.univ r k p y=some A ∧ A.card≤ r ∧ 0< y A ∧
      (∀v,0≤ queryCosts y A v ∧ queryCosts y A v≤1) ∧ (∑v,queryCosts y A v)=(k:ℚ) ∧
      edgeEnergy G (fun v => (queryCosts y A v:ℝ)) ≤ (k:ℝ)^2/p := by
  obtain ⟨A,hchoice,hpass⟩ := choice_exists G r k p y hy hr hk hp budget
  obtain ⟨hA,hpos,he⟩ := (passes_iff G r k p y A hp).mp hpass
  have hi := invariants G r k (fun A => (y A:ℝ)) hy A hA hpos
  have hcast (v : Fin n) : (queryCosts y A v:ℝ)=costs (fun A => (y A:ℝ)) A v := by simp [queryCosts,costs]
  refine ⟨A,hchoice,hA,by exact_mod_cast hpos,?_,?_,?_⟩
  · intro v
    have hv := hi.1 v
    rw [← hcast v] at hv
    exact_mod_cast hv
  · have hsum := hi.2.1
    simp_rw [← hcast] at hsum
    exact_mod_cast hsum
  · simpa only [hcast] using he
end EdgeSublinearMWIS.Main.ConditioningMoments
end

-- Solutions.PointArraySemantics
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def ratCode (q : ℚ) : RationalCode := ⟨q.num,q.den,q.den_pos⟩
 theorem ratCode_bits (q : ℚ) : (ratCode q).bits=encodeRat q := rfl
 theorem ratCode_value (q : ℚ) : (ratCode q).value=q := by
   exact Rat.num_div_den q
 theorem containsOwner_eq (v : ℕ) (A : List ℕ) : containsOwner (v,A)=decide (v∈A) := by
   induction A with
   | nil => simp [containsOwner]
   | cons a A ih =>
     by_cases ha : a=v
     · subst a; simp [containsOwner]
     · simpa [containsOwner,ha,Ne.symm ha] using ih
 theorem subsetMask_finList {n : ℕ} (L : List (Fin n)) :
     subsetMask n (L.map Fin.val)=mask L.toFinset := by
   unfold subsetMask mask
   rw [← finRange_val n,List.map_map,List.finRange,List.map_ofFn]
   apply congrArg List.ofFn
   funext v
   dsimp only [Function.comp_apply]
   rw [containsOwner_eq]
   apply decide_eq_decide.mpr
   simp only [List.mem_map,List.mem_toFinset]
   constructor
   · rintro ⟨a,ha,he⟩
     have hav : a=v := Fin.ext he
     simpa only [hav] using ha
   · intro hv
     exact ⟨v,hv,rfl⟩
 theorem subsetMask_sorted {n : ℕ} (A : Finset (Fin n)) :
     subsetMask n ((A.sort (·≤·)).map Fin.val)=mask A := by
   rw [subsetMask_finList,Finset.sort_toFinset]

 theorem boundedRange_count_order (n r : ℕ) : n≤(boundedSublists (List.range n) (r+2)).length := by
   let L := boundedSublists (List.range n) (r+2)
   have hmem (v : Fin n) : [v.val]∈L := by
     apply List.mem_filter.mpr
     refine ⟨List.mem_sublists.mpr ?_,by simp⟩
     exact List.singleton_sublist.mpr (List.mem_range.mpr v.isLt)
   have hinj : Function.Injective (fun v : Fin n => ([v.val] : List ℕ)) := by
     intro a b h
     apply Fin.ext
     simpa using h
   have hcard := Finset.card_le_card (show Finset.univ.image (fun v : Fin n => ([v.val] : List ℕ))⊆L.toFinset by
     intro A hA
     obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hA
     exact List.mem_toFinset.mpr (hmem v))
   rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin] at hcard
   exact hcard.trans (List.toFinset_card_le L)
end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 theorem mask_injective {n : ℕ} {A B : Finset (Fin n)} (h : mask A=mask B) : A=B := by
   ext v
   have hv := congrArg (fun L : List Bool => (L[v.val]?).getD false) h
   have he : decide (v∈A)=decide (v∈B) := by simpa [mask,v.isLt] using hv
   exact decide_eq_decide.mp he
 theorem coordinateMasks (n r : ℕ) :
     (boundedSublists (List.range n) (r+2)).map (subsetMask n)=(coordinateList (Finset.univ : Finset (Fin n)) r).map mask := by
   rw [← boundedFinRange_val n (r+2),List.map_map,coordinateList_bounded,Fin.sort_univ,List.map_map]
   apply List.map_congr_left
   intro L hL
   exact subsetMask_finList L
 theorem coordinateCount_nat (n r : ℕ) :
     (boundedSublists (List.range n) (r+2)).length=(coordinateList (Finset.univ : Finset (Fin n)) r).length := by
   have hh := congrArg List.length (coordinateMasks n r)
   simpa only [List.length_map] using hh
 theorem pointRead (n r : ℕ) (y : Finset (Fin n) → ℚ) :
     (readMany (coordinateList (Finset.univ : Finset (Fin n)) r).length (encodePoint Finset.univ r y)).1=
       (coordinateList Finset.univ r).map (fun A => codeWords (ratCode (y A))) := by
   let cs := coordinateList (Finset.univ : Finset (Fin n)) r
   have hh := readMany_codes (cs.map (fun A => ratCode (y A))) []
   simp only [List.length_map,List.flatMap_map,ratCode_bits,List.append_nil,List.map_map] at hh
   exact congrArg Prod.fst hh
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PathScaleCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds HeightMath

 def pathScaleFraction (L : ℕ) (s : ℕ×SignedWords) : FractionWords :=
   (multiply (multiply (natBits L) (natBits (height s.1))) s.2.2.2,s.2.2.1)
 def scaleNumerator (L : ℕ) : Realizer (fun s : ℕ×SignedWords =>
     multiply (multiply (natBits L) (natBits (height s.1))) s.2.2.2) :=
   (((((Realizer.constant (natBits L)).pair ((Realizer.fst.comp heightRealizer).comp naturalWordRealizer)).comp multiplyRealizer).pair
     ((Realizer.snd.comp Realizer.snd).comp Realizer.snd)).comp multiplyRealizer)
 def pathScaleFractionRealizer (L : ℕ) : Realizer (pathScaleFraction L) :=
   (scaleNumerator L).pair ((Realizer.snd.comp Realizer.snd).comp Realizer.fst)
 theorem pathScaleFraction_polynomial (L : ℕ) : PolyBound (pathScaleFractionRealizer L) := by
   have hn : PolyBound (scaleNumerator L) := polynomial_comp (polynomial_pair
     (polynomial_comp (polynomial_pair (linear_polynomial (linear_constant _))
       (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) height_polynomial) naturalWord_polynomial)) multiply_polynomial)
     (linear_polynomial (linear_comp (linear_comp linear_snd linear_snd) linear_snd))) multiply_polynomial
   exact polynomial_pair hn (linear_polynomial (linear_comp (linear_comp linear_snd linear_snd) linear_fst))
 def pathScaleWords (L : ℕ) (s : ℕ×SignedWords) : List Bool := ceilFraction (pathScaleFraction L s)
 def pathScaleWordsRealizer (L : ℕ) : Realizer (pathScaleWords L) := (pathScaleFractionRealizer L).comp ceilFractionRealizer
 theorem pathScaleWords_polynomial (L : ℕ) : PolyBound (pathScaleWordsRealizer L) :=
   polynomial_comp (pathScaleFraction_polynomial L) ceilFraction_polynomial
 theorem pathScaleWords_canonical (L : ℕ) (s : ℕ×SignedWords) : trim (pathScaleWords L s)=pathScaleWords L s := by
   unfold pathScaleWords ceilFraction
   dsimp only [divide]
   exact trim_idem _
 theorem pathScaleFraction_value (L n : ℕ) (δ : ℚ) (hd : 0<δ) :
     fractionValue (pathScaleFraction L (n,codeWords (ratCode δ)))=(L:ℚ)*(height n:ℚ)/δ := by
   have hnum : 0<δ.num := Rat.num_pos.mpr hd
   have habs : (δ.num.natAbs:ℚ)=(δ.num:ℚ) := by
     have hh : (δ.num.natAbs:ℤ)=δ.num := Int.natAbs_of_nonneg hnum.le
     simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ)) hh
   dsimp only [fractionValue,pathScaleFraction,codeWords,ratCode]
   rw [multiply_value,multiply_value,value_natBits,value_natBits,value_natBits,value_natBits]
   push_cast
   rw [habs]
   conv_rhs => rw [← Rat.num_div_den δ]
   have hnQ : (δ.num:ℚ)≠0 := by exact_mod_cast (ne_of_gt hnum)
   have hdQ : (δ.den:ℚ)≠0 := by exact_mod_cast (ne_of_gt δ.den_pos)
   field_simp [hnQ,hdQ]
 theorem pathScaleWords_value (L n : ℕ) (δ : ℚ) (hd : 0<δ) :
     value (pathScaleWords L (n,codeWords (ratCode δ)))=pathScale L n δ := by
   have hs : 0< value (pathScaleFraction L (n,codeWords (ratCode δ))).2 := by
     change 0< value (natBits δ.num.natAbs)
     rw [value_natBits]
     exact Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hd))
   rw [pathScaleWords,ceilFraction_value _ hs,pathScaleFraction_value L n δ hd]
   rfl
 def pathScaleCodeRealizer (L : ℕ) : Realizer (fun s : ℕ×SignedWords => prefixBits (pathScaleWords L s)) :=
   (pathScaleWordsRealizer L).comp prefixRealizer
 theorem pathScaleCode_polynomial (L : ℕ) : PolyBound (pathScaleCodeRealizer L) :=
   polynomial_comp (pathScaleWords_polynomial L) prefix_polynomial
 theorem pathScaleCode_correct (L n : ℕ) (δ : ℚ) (hd : 0<δ) :
     prefixBits (pathScaleWords L (n,codeWords (ratCode δ)))=encodeNat (pathScale L n δ) := by
   rw [canonical_eq_natBits _ (pathScaleWords_canonical L _),prefix_natBits,pathScaleWords_value L n δ hd]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ExpandedBounds
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 def Expanded {f : α → β} (R : Realizer f) (N : α → ℕ) : Prop :=
   ∃ C q : ℕ,0< C ∧ ∀x,R.time x≤ C*(volume x+N x+1)^q ∧ volume (f x)≤ C*(volume x+N x+1)^q
 theorem polynomial_expanded {f : α → β} {R : Realizer f} (hR : PolyBound R) (N : α → ℕ) : Expanded R N := by
   obtain ⟨C,q,hC,hR⟩ := hR
   refine ⟨C,q,hC,?_⟩
   intro x
   have hp := Nat.pow_le_pow_left (show volume x+1≤ volume x+N x+1 by omega) q
   exact ⟨(hR x).1.trans (Nat.mul_le_mul_left C hp),(hR x).2.trans (Nat.mul_le_mul_left C hp)⟩
 theorem expanded_comp {f : α → β} {g : β → γ} {R : Realizer f} {S : Realizer g} {N : α → ℕ}
     (hR : Expanded R N) (hS : PolyBound S) : Expanded (R.comp S) N := by
   obtain ⟨C,q,hC,hR⟩ := hR
   obtain ⟨D,r,hD,hS⟩ := hS
   refine ⟨C+D*(C+1)^r+10*(C+1),q+q*r,by positivity,?_⟩
   intro x
   let z := volume x+N x+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hp : 1≤ z^q := one_le_pow₀ hz
   have h1 := hR x
   change R.time x≤ C*z^q ∧ volume (f x)≤ C*z^q at h1
   have h2 := hS (f x)
   have hv : volume (f x)+1≤(C+1)*z^q := by nlinarith
   have hVp := Nat.pow_le_pow_left hv r
   rw [mul_pow,← pow_mul] at hVp
   have hq := Nat.pow_le_pow_right hz (show q≤ q+q*r by omega)
   have hr := Nat.pow_le_pow_right hz (show q*r≤ q+q*r by omega)
   have ht1 := h1.1.trans (Nat.mul_le_mul_left C hq)
   have ht2 := h2.1.trans (Nat.mul_le_mul_left D hVp)
   have ht2 := ht2.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+1)^r) hr)
   have hc := (Nat.mul_le_mul_left 10 hv).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (10*(C+1)) hq)
   have ho := h2.2.trans (Nat.mul_le_mul_left D hVp)
   have ho := ho.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+1)^r) hr)
   constructor
   · rw [Realizer.time_comp]
     change _≤(C+D*(C+1)^r+10*(C+1))*z^(q+q*r)
     nlinarith only [ht1,ht2,hc]
   · change volume (g (f x))≤(C+D*(C+1)^r+10*(C+1))*z^(q+q*r)
     have hcoef : D*(C+1)^r≤ C+D*(C+1)^r+10*(C+1) := by omega
     exact ho.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (z^(q+q*r)) hcoef)
 theorem polynomial_comp_expanded {f : α → β} {g : β → γ} {R : Realizer f} {S : Realizer g} {N : β → ℕ}
     (hR : PolyBound R) (hS : Expanded S N) : Expanded (R.comp S) (N ∘ f) := by
   obtain ⟨C,q,hC,hR⟩ := hR
   obtain ⟨D,r,hD,hS⟩ := hS
   let e := q+(q+1)*r+1
   refine ⟨C+D*(C+2)^r+10*(C+1),e,by positivity,?_⟩
   intro x
   let z := volume x+N (f x)+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hN : N (f x)≤ z := by dsimp [z]; omega
   have hp := Nat.pow_le_pow_left (show volume x+1≤ z by dsimp [z]; omega) q
   have h1 := hR x
   have ht : R.time x≤ C*z^q := h1.1.trans (Nat.mul_le_mul_left C hp)
   have hv : volume (f x)≤ C*z^q := h1.2.trans (Nat.mul_le_mul_left C hp)
   have hq : z^q≤ z^(q+1) := Nat.pow_le_pow_right hz (by omega)
   have hze : z≤ z^(q+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+1)
   have hv' := hv.trans (Nat.mul_le_mul_left C hq)
   have hbase : volume (f x)+N (f x)+1≤(C+2)*z^(q+1) := by nlinarith
   have h2 := hS (f x)
   have hbp := Nat.pow_le_pow_left hbase r
   rw [mul_pow,← pow_mul] at hbp
   have hqe : z^q≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hre : z^((q+1)*r)≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have ht1 := ht.trans (Nat.mul_le_mul_left C hqe)
   have ht2 := h2.1.trans (Nat.mul_le_mul_left D hbp)
   have ht2 := ht2.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+2)^r) hre)
   have ho := h2.2.trans (Nat.mul_le_mul_left D hbp)
   have ho := ho.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+2)^r) hre)
   have hv1 : volume (f x)+1≤(C+1)*z^q := by have hh := one_le_pow₀ hz (n:=q); nlinarith
   have hc := (Nat.mul_le_mul_left 10 hv1).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (10*(C+1)) hqe)
   constructor
   · rw [Realizer.time_comp]
     change _≤(C+D*(C+2)^r+10*(C+1))*z^e
     nlinarith only [ht1,ht2,hc]
   · change volume (g (f x))≤(C+D*(C+2)^r+10*(C+1))*z^e
     have hcoef : D*(C+2)^r≤ C+D*(C+2)^r+10*(C+1) := by omega
     exact ho.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (z^e) hcoef)

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.ExpandedPair
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
 theorem expanded_pair {f : α → β} {g : α → γ} {R : Realizer f} {S : Realizer g} {N : α → ℕ}
     (hR : Expanded R N) (hS : Expanded S N) : Expanded (R.pair S) N := by
   obtain ⟨C,q,hC,hR⟩ := hR
   obtain ⟨D,r,hD,hS⟩ := hS
   refine ⟨21*C+21*D+40,q+r+1,by positivity,?_⟩
   intro x
   let z := volume x+N x+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hq : z^q≤ z^(q+r+1) := Nat.pow_le_pow_right hz (by omega)
   have hr : z^r≤ z^(q+r+1) := Nat.pow_le_pow_right hz (by omega)
   have hv : volume x+1≤ z^(q+r+1) := (show volume x+1≤ z by dsimp [z]; omega).trans
     (by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+r+1))
   have h1 := hR x
   have h2 := hS x
   change R.time x≤ C*z^q ∧ volume (f x)≤ C*z^q at h1
   change S.time x≤ D*z^r ∧ volume (g x)≤ D*z^r at h2
   have ht1 := h1.1.trans (Nat.mul_le_mul_left C hq)
   have ht2 := h2.1.trans (Nat.mul_le_mul_left D hr)
   have ho1 := h1.2.trans (Nat.mul_le_mul_left C hq)
   have ho2 := h2.2.trans (Nat.mul_le_mul_left D hr)
   constructor
   · rw [Realizer.time_pair]
     change _≤(21*C+21*D+40)*z^(q+r+1)
     nlinarith only [ht1,ht2,ho1,ho2,hv]
   · change volume (f x,g x)≤(21*C+21*D+40)*z^(q+r+1)
     rw [volume_pair]
     nlinarith only [ho1,ho2,hv]
end EdgeSublinearMWIS.Main.RealizerBounds

namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
 theorem expanded_comp_expanded {f : α → β} {g : β → γ} {R : Realizer f} {S : Realizer g}
     {N : α → ℕ} {M : β → ℕ} (hR : Expanded R N) (hS : Expanded S M) :
     Expanded (R.comp S) (fun x => N x+M (f x)) := by
   obtain ⟨C,q,hC,hR⟩ := hR
   obtain ⟨D,r,hD,hS⟩ := hS
   let e := q+(q+1)*r+1
   refine ⟨C+D*(C+2)^r+10*(C+1),e,by positivity,?_⟩
   intro x
   let z := volume x+(N x+M (f x))+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hM : M (f x)≤ z := by dsimp [z]; omega
   have hp := Nat.pow_le_pow_left (show volume x+N x+1≤ z by dsimp [z]; omega) q
   have h1 := hR x
   have ht : R.time x≤ C*z^q := h1.1.trans (Nat.mul_le_mul_left C hp)
   have hv : volume (f x)≤ C*z^q := h1.2.trans (Nat.mul_le_mul_left C hp)
   have hq : z^q≤ z^(q+1) := Nat.pow_le_pow_right hz (by omega)
   have hze : z≤ z^(q+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+1)
   have hv' := hv.trans (Nat.mul_le_mul_left C hq)
   have hbase : volume (f x)+M (f x)+1≤(C+2)*z^(q+1) := by nlinarith
   have h2 := hS (f x)
   have hbp := Nat.pow_le_pow_left hbase r
   rw [mul_pow,← pow_mul] at hbp
   have hqe : z^q≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hre : z^((q+1)*r)≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have ht1 := ht.trans (Nat.mul_le_mul_left C hqe)
   have ht2 := h2.1.trans (Nat.mul_le_mul_left D hbp)
   have ht2 := ht2.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+2)^r) hre)
   have ho := h2.2.trans (Nat.mul_le_mul_left D hbp)
   have ho := ho.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+2)^r) hre)
   have hv1 : volume (f x)+1≤(C+1)*z^q := by have hh := one_le_pow₀ hz (n:=q); nlinarith
   have hc := (Nat.mul_le_mul_left 10 hv1).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (10*(C+1)) hqe)
   constructor
   · rw [Realizer.time_comp]
     change _≤(C+D*(C+2)^r+10*(C+1))*z^e
     nlinarith only [ht1,ht2,hc]
   · change volume (g (f x))≤(C+D*(C+2)^r+10*(C+1))*z^e
     exact ho.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (z^e) (show D*(C+2)^r≤ C+D*(C+2)^r+10*(C+1) by omega))
end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.ReadUnboundedNatural
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem value_expanded : Expanded valueRealizer value := by
   obtain ⟨C,q,hC,hT⟩ := value_time
   refine ⟨C+3,q+1,by omega,?_⟩
   intro A
   let z := volume A+value A+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hl := bits_length_volume A
   have hbase : value A+A.length+1≤ z := by dsimp [z]; omega
   have hp : z^q≤ z^(q+1) := Nat.pow_le_pow_right hz (by omega)
   have ht := (hT A).trans ((Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q)).trans (Nat.mul_le_mul_left C hp))
   have hv : value A+1≤ z^(q+1) := (show value A+1≤ z by dsimp [z]; omega).trans
     (by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+1))
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (value A)≤(C+3)*z^(q+1)
     rw [volume_nat]
     nlinarith
 def readUnboundedNatural (L : List Bool) : ℕ×List Bool := (value (readWord L).1,(readWord L).2)
 def readUnboundedNaturalRealizer : Realizer readUnboundedNatural :=
   readWordRealizer.comp ((Realizer.fst.comp valueRealizer).pair Realizer.snd)
 theorem readUnboundedNatural_expanded : Expanded readUnboundedNaturalRealizer (fun L => value (readWord L).1) :=
   polynomial_comp_expanded readWord_polynomial (expanded_pair
     (polynomial_comp_expanded (linear_polynomial linear_fst) value_expanded)
     (polynomial_expanded (linear_polynomial linear_snd) (fun s : List Bool×List Bool => value s.1)))
 theorem readUnboundedNatural_encoded (n : ℕ) (rest : List Bool) : readUnboundedNatural (encodeNat n++rest)=(n,rest) := by
   simp only [readUnboundedNatural,readWord_encoded,value_natBits]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BoundedSubsetSize
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem boundedRange_length_mono (j n k : ℕ) (h : j≤ n) :
     (boundedSublists (List.range j) k).length≤(boundedSublists (List.range n) k).length := by
   obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
   induction d with
   | zero => simp
   | succ d ih =>
     rw [Nat.add_succ,List.range_succ,boundedSublists_concat,List.length_append]
     omega

 theorem boundedRange_member_volume (n k : ℕ) (A : List ℕ)
     (hA : A∈boundedSublists (List.range n) k) : volume A≤3*(n+1)^2 := by
   have hsub : A.Sublist (List.range n) := List.mem_sublists.mp (List.mem_filter.mp hA).1
   have hlen : A.length≤ n := by simpa using hsub.length_le
   have he (a : ℕ) (ha : a∈A) : volume a≤2*n+1 := by
     have hh : a< n := List.mem_range.mp (hsub.subset ha)
     rw [volume_nat]
     omega
   have hv := volume_list_le A (2*n+1) he
   have hm := Nat.mul_le_mul_right (2*n+2) hlen
   nlinarith

 theorem boundedRange_volume (j n k : ℕ) (h : j≤ n) :
     volume (boundedSublists (List.range j) k)≤
       (3*(n+1)^2+1)*(boundedSublists (List.range n) k).length+1 := by
   have hv := volume_list_le (boundedSublists (List.range j) k) (3*(n+1)^2) (by
     intro A hA
     have hh := boundedRange_member_volume j k A hA
     have hp := Nat.pow_le_pow_left (show j+1≤ n+1 by omega) 2
     exact hh.trans (Nat.mul_le_mul_left 3 hp))
   rw [Nat.mul_comm] at hv
   have hl := Nat.mul_le_mul_left (3*(n+1)^2+1) (boundedRange_length_mono j n k h)
   omega

 theorem subsetFold_range (n k : ℕ) :
     (List.range n).foldl (fun s a => subsetStep (a,s)) (k,[[]])=(k,boundedSublists (List.range n) k) := by
   simpa only [boundedSublists_nil,List.nil_append] using subsetFold_correct (List.range n) [] k

 theorem subsetFold_prefix_volume (n k j : ℕ) (hj : j≤ n) :
     volume (((List.range n).take j).foldl (fun s a => subsetStep (a,s)) (k,[[]]))≤
       10*(n+k+(boundedSublists (List.range n) k).length+1)^3 := by
   rw [List.take_range,Nat.min_eq_left hj,subsetFold_range,volume_pair,volume_nat]
   let z := n+k+(boundedSublists (List.range n) k).length+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hn : n+1≤ z := by dsimp [z]; omega
   have hk : k≤ z := by dsimp [z]; omega
   have hl : (boundedSublists (List.range n) k).length≤ z := by dsimp [z]; omega
   have hv := boundedRange_volume j n k hj
   have hp := Nat.pow_le_pow_left hn 2
   have hm := Nat.mul_le_mul (show 3*(n+1)^2+1≤3*z^2+1 by omega) hl
   have h2 : z≤ z^3 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤3)
   change 2*k+1+volume (boundedSublists (List.range j) k)+1≤10*z^3
   nlinarith [show z*z^2=z^3 by ring]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BoundedSubsetRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem boundedSubsetFold_time : ∃ C q : ℕ,0< C ∧ ∀n k,
     subsetStepRealizer.fold.time (List.range n,(k,([[]] : List (List ℕ))))≤
       C*(n+k+(boundedSublists (List.range n) k).length+1)^q := by
   obtain ⟨C,q,hC,hR⟩ := subsetStep_polynomial
   let F := C*15^q
   refine ⟨F+1000,3*q+4,by dsimp [F]; positivity,?_⟩
   intro n k
   let z := n+k+(boundedSublists (List.range n) k).length+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hn : n≤ z := by dsimp [z]; omega
   have hk : k≤ z := by dsimp [z]; omega
   have hV (j : ℕ) (hj : j≤(List.range n).length) :
       volume (((List.range n).take j).foldl (fun s a => subsetStep (a,s)) (k,([[]] : List (List ℕ))))≤10*z^3 :=
     subsetFold_prefix_volume n k j (by simpa using hj)
   have hxs : volume (List.range n)≤3*z^2 := by
     have hh := volume_list_le (List.range n) (2*n+1) (by intro a ha; rw [volume_nat]; have := List.mem_range.mp ha; omega)
     simp only [List.length_range] at hh
     have hv : volume (List.range n)≤3*(n+1)^2 := by nlinarith
     exact hv.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (by dsimp [z]; omega : n+1≤ z) 2))
   have hT (j : ℕ) (hj : j<(List.range n).length) :
       subsetStepRealizer.time ((List.range n)[j],((List.range n).take j).foldl (fun s a => subsetStep (a,s)) (k,([[]] : List (List ℕ))))≤ F*z^(3*q) := by
     have hv := hV j hj.le
     have hentry : volume ((List.range n)[j])≤2*z+1 := by rw [volume_nat,List.getElem_range]; simp only [List.length_range] at hj; omega
     have hzp : z≤ z^3 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤3)
     have hbase : volume ((List.range n)[j],((List.range n).take j).foldl (fun s a => subsetStep (a,s)) (k,([[]] : List (List ℕ))))+1≤15*z^3 := by
       simp only [volume_pair]
       nlinarith
     have hh := ((hR _).1).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
     simpa only [F,mul_pow,← pow_mul,Nat.mul_assoc] using hh
   have ht := fold_prefix_bound subsetStepRealizer (List.range n) (k,([[]] : List (List ℕ))) (F*z^(3*q)) (10*z^3) hV hT
   simp only [List.length_range] at ht
   have hpq : z^(3*q+1)≤ z^(3*q+4) := Nat.pow_le_pow_right hz (by omega)
   have hp4 : z^4≤ z^(3*q+4) := Nat.pow_le_pow_right hz (by omega)
   have hp2 : z^2≤ z^(3*q+4) := Nat.pow_le_pow_right hz (by omega)
   have hp3 : z^3≤ z^(3*q+4) := Nat.pow_le_pow_right hz (by omega)
   have hinit : volume (List.range n,(k,([[]] : List (List ℕ))))≤3*z^2+2*z+6 := by
     simp only [volume_pair,volume_nat,volume_cons,volume_nil]
     omega
   have hi : volume (List.range n,(k,([[]] : List (List ℕ))))≤12*z^2 := by
     have h1 : 1≤ z^2 := one_le_pow₀ hz
     have h2 : z≤ z^2 := by nlinarith
     nlinarith only [hinit,h1,h2]
   have hm := Nat.mul_le_mul hn (show F*z^(3*q)+20*(volume (List.range n)+2*(10*z^3)+1)≤ F*z^(3*q)+500*z^3 by
     have h23 : z^2≤ z^3 := Nat.pow_le_pow_right hz (by omega)
     have h1 : 1≤ z^3 := one_le_pow₀ hz
     nlinarith)
   have he : z*(F*z^(3*q)+500*z^3)=F*z^(3*q+1)+500*z^4 := by rw [pow_succ]; ring
   rw [he] at hm
   have hpF := Nat.mul_le_mul_left F hpq
   have hp500 := Nat.mul_le_mul_left 500 hp4
   rw [Realizer.time_fold]
   change 2*volume (List.range n,(k,([[]] : List (List ℕ))))+6+Realizer.foldTime subsetStepRealizer (k,([[]] : List (List ℕ))) (List.range n)≤(F+1000)*z^(3*q+4)
   have hone : 1≤ z^(3*q+4) := one_le_pow₀ hz
   nlinarith only [ht,hm,hpF,hp500,hi,hp2,hone]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BoundedSubsetCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def subsetInitialize : Realizer (fun x : ℕ×ℕ => (List.range x.1,(x.2,([[]] : List (List ℕ))))) :=
   (Realizer.fst.comp Realizer.range).pair (Realizer.snd.pair (Realizer.constant [[]]))
 def boundedSubsetRealizer : Realizer (fun x : ℕ×ℕ => boundedSublists (List.range x.1) x.2) :=
   ((subsetInitialize.comp subsetStepRealizer.fold).comp Realizer.snd).congr (by
     rintro ⟨n,k⟩
     change ((List.range n).foldl (fun s a => subsetStep (a,s)) (k,([[]] : List (List ℕ)))).2=_
     rw [subsetFold_range])
 theorem subsetInitialize_polynomial : PolyBound subsetInitialize :=
   polynomial_pair (polynomial_comp (linear_polynomial linear_fst) range_polynomial)
     (linear_polynomial (linear_pair linear_snd (linear_constant _)))

 theorem boundedSubset_time : ∃ C q : ℕ,0< C ∧ ∀n k,
     boundedSubsetRealizer.time (n,k)≤ C*(n+k+(boundedSublists (List.range n) k).length+1)^q ∧
     volume (boundedSublists (List.range n) k)≤ C*(n+k+(boundedSublists (List.range n) k).length+1)^q := by
   obtain ⟨A,p,hA,hInit⟩ := subsetInitialize_polynomial
   obtain ⟨B,q,hB,hFold⟩ := boundedSubsetFold_time
   let e := p+q+4
   refine ⟨A*4^p+B+500,e,by positivity,?_⟩
   intro n k
   let z := n+k+(boundedSublists (List.range n) k).length+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hbase : volume (n,k)+1≤4*z := by simp only [volume_pair,volume_nat]; dsimp [z]; omega
   have hp := Nat.pow_le_pow_left hbase p
   rw [mul_pow] at hp
   have hpe : z^p≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hqe : z^q≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have h3e : z^3≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have h2e : z^2≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hinit := (hInit (n,k)).1.trans (Nat.mul_le_mul_left A hp)
   have hinit := hinit.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (A*4^p) hpe)
   have hfold := (hFold n k).trans (Nat.mul_le_mul_left B hqe)
   have hstate := subsetFold_prefix_volume n k n le_rfl
   rw [List.take_range,Nat.min_self,subsetFold_range] at hstate
   change volume (k,boundedSublists (List.range n) k)≤10*z^3 at hstate
   have hinput : volume (List.range n,(k,([[]] : List (List ℕ))))≤12*z^2 := by
     have hh := volume_list_le (List.range n) (2*n+1) (by intro a ha; rw [volume_nat]; have := List.mem_range.mp ha; omega)
     simp only [List.length_range] at hh
     simp only [volume_pair,volume_nat,volume_cons,volume_nil]
     have hn : n+k+1≤ z := by dsimp [z]; omega
     nlinarith
   have hvout : volume (boundedSublists (List.range n) k)≤10*z^3 := by
     rw [volume_pair] at hstate
     omega
   constructor
   · dsimp only [boundedSubsetRealizer]
     rw [Realizer.time_congr,Realizer.time_comp,Realizer.time_comp,Realizer.time_snd]
     dsimp only [Function.comp_apply]
     rw [subsetFold_range]
     change subsetInitialize.time (n,k)+subsetStepRealizer.fold.time (List.range n,(k,([[]] : List (List ℕ))))+
       10*(volume (List.range n,(k,([[]] : List (List ℕ))))+1)+
       (volume (k,boundedSublists (List.range n) k)+2)+10*(volume (k,boundedSublists (List.range n) k)+1)≤(A*4^p+B+500)*z^e
     have hmul2 := Nat.mul_le_mul_left 120 h2e
     have hmul3 := Nat.mul_le_mul_left 110 h3e
     have hone : 1≤ z^e := one_le_pow₀ hz
     nlinarith only [hinit,hfold,hinput,hstate,hmul2,hmul3,hone]
   · exact (hvout.trans (Nat.mul_le_mul_left 10 h3e)).trans (Nat.mul_le_mul_right _ (by omega))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ConditioningEnergyCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev PointContext := ℕ×CoordinateTable
 def pointQuery (s : List ℕ×PointContext) : FractionWords := coordinateLookup s.2.2 (subsetMask s.2.1 s.1)
 def pointQueryRealizer : Realizer pointQuery :=
   (Realizer.snd.comp Realizer.snd).pair ((((Realizer.snd.comp Realizer.fst).pair Realizer.fst).comp subsetMaskRealizer)) |>.comp coordinateLookupRealizer
 theorem pointQuery_polynomial : PolyBound pointQueryRealizer :=
   polynomial_comp (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_snd))
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) linear_fst)) subsetMask_polynomial)) coordinateLookup_polynomial
 def extendedQuery (s : ℕ×(List ℕ×PointContext)) : FractionWords := pointQuery (s.2.1++[s.1],s.2.2)
 def extendedQueryRealizer : Realizer extendedQuery :=
   (((((Realizer.snd.comp Realizer.fst).pair Realizer.fst).comp appendVertexRealizer).pair (Realizer.snd.comp Realizer.snd)).comp pointQueryRealizer)
 theorem extendedQuery_polynomial : PolyBound extendedQueryRealizer := by
   have ha : PolyBound appendVertexRealizer := by
     have hn : Linear (Realizer.nil : Realizer (fun _ : List ℕ×ℕ => ([] : List ℕ))) :=
       linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
     exact polynomial_comp (linear_polynomial (linear_pair linear_fst
       (linear_comp (linear_pair linear_snd hn) linear_cons))) appendList_polynomial
   exact polynomial_comp (polynomial_pair
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) linear_fst)) ha)
     (linear_polynomial (linear_comp linear_snd linear_snd))) pointQuery_polynomial
 def edgeMoment (s : (ℕ×ℕ)×(List ℕ×PointContext)) : FractionWords :=
   fractionMul (extendedQuery (s.1.1,s.2),extendedQuery (s.1.2,s.2))
 def edgeMomentRealizer : Realizer edgeMoment :=
   (((((Realizer.fst.comp Realizer.fst).pair Realizer.snd).comp extendedQueryRealizer).pair
     (((Realizer.fst.comp Realizer.snd).pair Realizer.snd).comp extendedQueryRealizer)).comp fractionMulRealizer)
 theorem edgeMoment_polynomial : PolyBound edgeMomentRealizer :=
   polynomial_comp (polynomial_pair
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst linear_fst) linear_snd)) extendedQuery_polynomial)
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst linear_snd) linear_snd)) extendedQuery_polynomial)) fractionMul_polynomial
 def sumFractions (xs : List FractionWords) : FractionWords := xs.foldl (fun s a => fractionAdd (a,s)) zeroFraction
 def sumFractionsRealizer : Realizer sumFractions := (Realizer.id.pair (Realizer.constant zeroFraction)).comp fractionAddRealizer.fold
 theorem sumFractions_polynomial : PolyBound sumFractionsRealizer :=
   polynomial_comp (linear_polynomial (linear_pair linear_id (linear_constant zeroFraction))) fractionAdd_fold_polynomial
 def momentSum (s : List (ℕ×ℕ)×(List ℕ×PointContext)) : FractionWords :=
   sumFractions (s.1.map (fun e => edgeMoment (e,s.2)))
 def momentSumRealizer : Realizer momentSum := (mapEnvironment edgeMomentRealizer).comp sumFractionsRealizer
 theorem momentSum_polynomial : PolyBound momentSumRealizer :=
   polynomial_comp (polynomial_mapEnvironment edgeMoment_polynomial) sumFractions_polynomial
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ConditioningTestCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev ConditioningEnv := ℕ×(List Bool×(List Bool×(PointContext×List (ℕ×ℕ))))
 abbrev ConditioningInput := List ℕ×ConditioningEnv
 def candidateR : Realizer (fun s : ConditioningInput => s.2.1) := Realizer.snd.comp Realizer.fst
 def candidateK : Realizer (fun s : ConditioningInput => s.2.2.1) := (Realizer.snd.comp Realizer.snd).comp Realizer.fst
 def candidateP : Realizer (fun s : ConditioningInput => s.2.2.2.1) := ((Realizer.snd.comp Realizer.snd).comp Realizer.snd).comp Realizer.fst
 def candidateCtx : Realizer (fun s : ConditioningInput => s.2.2.2.2.1) := (((Realizer.snd.comp Realizer.snd).comp Realizer.snd).comp Realizer.snd).comp Realizer.fst
 def candidateEdges : Realizer (fun s : ConditioningInput => s.2.2.2.2.2) := (((Realizer.snd.comp Realizer.snd).comp Realizer.snd).comp Realizer.snd).comp Realizer.snd
 theorem candidateR_linear : Linear candidateR := linear_comp linear_snd linear_fst
 theorem candidateK_linear : Linear candidateK := linear_comp (linear_comp linear_snd linear_snd) linear_fst
 theorem candidateP_linear : Linear candidateP := linear_comp (linear_comp (linear_comp linear_snd linear_snd) linear_snd) linear_fst
 theorem candidateCtx_linear : Linear candidateCtx := linear_comp (linear_comp (linear_comp (linear_comp linear_snd linear_snd) linear_snd) linear_snd) linear_fst
 theorem candidateEdges_linear : Linear candidateEdges := linear_comp (linear_comp (linear_comp (linear_comp linear_snd linear_snd) linear_snd) linear_snd) linear_snd
 def candidateQuery := (Realizer.fst.pair candidateCtx).comp pointQueryRealizer
 theorem candidateQuery_polynomial : PolyBound candidateQuery :=
   polynomial_comp (linear_polynomial (linear_pair linear_fst candidateCtx_linear)) pointQuery_polynomial
 def candidateEnergy := (candidateEdges.pair (Realizer.fst.pair candidateCtx)).comp momentSumRealizer
 theorem candidateEnergy_polynomial : PolyBound candidateEnergy :=
   polynomial_comp (linear_polynomial (linear_pair candidateEdges_linear (linear_pair linear_fst candidateCtx_linear))) momentSum_polynomial
 def candidatePFraction := candidateP.pair (Realizer.constant ([true] : List Bool))
 def candidateKFraction := candidateK.pair (Realizer.constant ([true] : List Bool))
 theorem candidatePFraction_polynomial : PolyBound candidatePFraction := linear_polynomial (linear_pair candidateP_linear (linear_constant _))
 theorem candidateKFraction_polynomial : PolyBound candidateKFraction := linear_polynomial (linear_pair candidateK_linear (linear_constant _))
 def candidateLeft := (candidatePFraction.pair candidateEnergy).comp fractionMulRealizer
 def candidateScaled := (candidateKFraction.pair candidateQuery).comp fractionMulRealizer
 def candidateRight := (candidateScaled.pair candidateScaled).comp fractionMulRealizer
 theorem candidateLeft_polynomial : PolyBound candidateLeft :=
   polynomial_comp (polynomial_pair candidatePFraction_polynomial candidateEnergy_polynomial) fractionMul_polynomial
 theorem candidateScaled_polynomial : PolyBound candidateScaled :=
   polynomial_comp (polynomial_pair candidateKFraction_polynomial candidateQuery_polynomial) fractionMul_polynomial
 theorem candidateRight_polynomial : PolyBound candidateRight :=
   polynomial_comp (polynomial_pair candidateScaled_polynomial candidateScaled_polynomial) fractionMul_polynomial
 def candidateCard := (candidateR.pair (Realizer.fst.comp listLength)).comp ltNatRealizer |>.comp Realizer.not
 def candidatePositive := ((Realizer.constant ([] : List Bool)).pair (candidateQuery.comp Realizer.fst)).comp BinarySubtract.lessRealizer
 def candidateCompare := (candidateLeft.pair candidateRight).comp fractionLERealizer
 def conditioningPass (s : ConditioningInput) : Bool :=
   let A := pointQuery (s.1,s.2.2.2.2.1)
   let E := momentSum (s.2.2.2.2.2,(s.1,s.2.2.2.2.1))
   let kx := fractionMul ((s.2.2.1,[true]),A)
   ((!decide (s.2.1< s.1.length)) && BinarySubtract.less [] A.1) &&
     fractionLE (fractionMul ((s.2.2.2.1,[true]),E),fractionMul (kx,kx))
 def conditioningTestRealizer : Realizer conditioningPass := ((candidateCard.pair candidatePositive).comp Realizer.and).pair candidateCompare |>.comp Realizer.and
 theorem conditioningTest_polynomial : PolyBound conditioningTestRealizer := by
   have hc : PolyBound candidateCard := polynomial_comp (polynomial_comp
     (polynomial_pair (linear_polynomial candidateR_linear) (polynomial_comp (linear_polynomial linear_fst) listLength_polynomial))
       ltNat_polynomial) (linear_polynomial linear_not)
   have hp : PolyBound candidatePositive := polynomial_comp (polynomial_pair (linear_polynomial (linear_constant _))
     (polynomial_comp candidateQuery_polynomial (linear_polynomial linear_fst))) BinarySubtract.less_polynomial
   have he : PolyBound candidateCompare := polynomial_comp (polynomial_pair candidateLeft_polynomial candidateRight_polynomial) fractionLE_polynomial
   exact polynomial_comp (polynomial_pair (polynomial_comp (polynomial_pair hc hp) (linear_polynomial linear_and)) he) (linear_polynomial linear_and)
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ConditioningParser
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def conditioningTail (L : List Bool) : List Bool×(List Bool×List Bool) :=
   ((readWord L).1,readWord (readWord L).2)
 def conditioningTailRealizer : Realizer conditioningTail :=
   (readWordRealizer.comp Realizer.fst).pair ((readWordRealizer.comp Realizer.snd).comp readWordRealizer)
 theorem conditioningTail_polynomial : PolyBound conditioningTailRealizer :=
   polynomial_pair (polynomial_comp readWord_polynomial (linear_polynomial linear_fst))
     (polynomial_comp (polynomial_comp readWord_polynomial (linear_polynomial linear_snd)) readWord_polynomial)
 def conditioningPrefix (L : List Bool) : ℕ×(List Bool×(List Bool×List Bool)) :=
   ((readUnboundedNatural L).1,conditioningTail (readUnboundedNatural L).2)
 def conditioningPrefixRealizer : Realizer conditioningPrefix :=
   readUnboundedNaturalRealizer.comp (Realizer.fst.pair (Realizer.snd.comp conditioningTailRealizer))
 theorem conditioningPrefix_expanded : Expanded conditioningPrefixRealizer (fun L => value (readWord L).1) :=
   expanded_comp readUnboundedNatural_expanded
     (polynomial_pair (linear_polynomial linear_fst) (polynomial_comp (linear_polynomial linear_snd) conditioningTail_polynomial))
 abbrev ConditioningParsed := ℕ×(List Bool×(ℕ×(List Bool×(List Bool×List Bool))))
 def conditioningGraph (s : ℕ×(List Bool×List Bool)) : ConditioningParsed :=
   (s.1,(s.2.1,conditioningPrefix s.2.2))
 def conditioningGraphRealizer : Realizer conditioningGraph :=
   Realizer.fst.pair ((Realizer.snd.comp Realizer.fst).pair ((Realizer.snd.comp Realizer.snd).comp conditioningPrefixRealizer))
 theorem conditioningGraph_expanded : Expanded conditioningGraphRealizer (fun s => value (readWord s.2.2).1) := by
   unfold conditioningGraphRealizer
   apply expanded_pair
   · exact polynomial_expanded (linear_polynomial linear_fst) _
   · apply expanded_pair
     · exact polynomial_expanded (linear_polynomial (linear_comp linear_snd linear_fst)) _
     · exact polynomial_comp_expanded (linear_polynomial (linear_comp linear_snd linear_snd)) conditioningPrefix_expanded
 def conditioningParse (L : List Bool) : ConditioningParsed := conditioningGraph (graphStart L)
 def conditioningParseRealizer : Realizer conditioningParse := graphStartRealizer.comp conditioningGraphRealizer
 theorem conditioningParse_expanded : Expanded conditioningParseRealizer (fun L => value (readWord (graphStart L).2.2).1) :=
   polynomial_comp_expanded (N:=fun s : ℕ×(List Bool×List Bool) => value (readWord s.2.2).1)
     graphStart_polynomial conditioningGraph_expanded
 theorem graphStart_append {n : ℕ} (G : SimpleGraph (Fin n)) (rest : List Bool) :
     graphStart (graphBits G++rest)=(n,(adjacencyBits G,rest)) := by
   have he : graphBits G++rest=encodeNat n++(adjacencyBits G++rest) := by rw [graphBits_eq,List.append_assoc]
   have hb : n≤(encodeNat n++(adjacencyBits G++rest)).length+1 := by
     have hh := graph_order_bound G
     rw [← he]
     simp only [List.length_append]
     omega
   dsimp only [graphStart]
   rw [he,readNatural_encoded n _ hb,← adjacencyBits_length G]
   simp only [splitWord,List.take_left,List.drop_left]
 theorem conditioningParse_encoded {n : ℕ} (G : SimpleGraph (Fin n)) (r k p : ℕ) (rest : List Bool) :
     conditioningParse (graphBits G++encodeNat r++encodeNat k++encodeNat p++rest)=
       (n,(adjacencyBits G,(r,(natBits k,(natBits p,rest))))) := by
   simp only [List.append_assoc,conditioningParse,graphStart_append,conditioningGraph,conditioningPrefix,
     readUnboundedNatural_encoded,conditioningTail,readWord_encoded]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SeparatorParser
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev SeparatorRaw := ℕ×(List Bool×(List Bool×(SignedWords×List Bool)))
 def separatorMaskPart : Realizer (fun s : ℕ×(List Bool×List Bool) => splitWord s.2.2 s.1) :=
   ((Realizer.snd.comp Realizer.snd).pair Realizer.fst).comp splitWordRealizer
 theorem separatorMaskPart_polynomial : PolyBound separatorMaskPart := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp linear_snd linear_snd) linear_fst)) splitWord_polynomial
 def separatorAccuracyPart := (separatorMaskPart.comp Realizer.snd).comp readRationalRealizer
 theorem separatorAccuracyPart_polynomial : PolyBound separatorAccuracyPart := polynomial_comp
   (polynomial_comp separatorMaskPart_polynomial (linear_polynomial linear_snd)) readRational_polynomial
 def separatorBody (s : ℕ×(List Bool×List Bool)) : SeparatorRaw :=
   (s.1,(s.2.1,((splitWord s.2.2 s.1).1,readRational (splitWord s.2.2 s.1).2)))
 def separatorBodyRealizer : Realizer separatorBody :=
   Realizer.fst.pair ((Realizer.snd.comp Realizer.fst).pair ((separatorMaskPart.comp Realizer.fst).pair separatorAccuracyPart))
 theorem separatorBody_polynomial : PolyBound separatorBodyRealizer := polynomial_pair (linear_polynomial linear_fst)
   (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_fst))
     (polynomial_pair (polynomial_comp separatorMaskPart_polynomial (linear_polynomial linear_fst)) separatorAccuracyPart_polynomial))
 def separatorParse (L : List Bool) : SeparatorRaw := separatorBody (graphStart L)
 def separatorParseRealizer : Realizer separatorParse := graphStartRealizer.comp separatorBodyRealizer
 theorem separatorParse_polynomial : PolyBound separatorParseRealizer := polynomial_comp graphStart_polynomial separatorBody_polynomial
 theorem separatorParse_correct {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (δ : ℚ) (x : Fin n → ℚ) :
     separatorParse (separatorInput G W δ x)=
       (n,(adjacencyBits G,(mask W,(codeWords (ratCode δ),(W.sort (·≤·)).flatMap (fun v => encodeRat (x v)))))) := by
   have hm : (mask W).length=n := by simp [mask]
   unfold separatorParse separatorInput
   rw [List.append_assoc,List.append_assoc,graphStart_append]
   dsimp only [separatorBody]
   have hs (rest : List Bool) : splitWord (mask W++rest) n=(mask W,rest) := by
     simpa only [hm] using (show splitWord (mask W++rest) (mask W).length=(mask W,rest) from
       by simp only [splitWord,List.take_left,List.drop_left])
   rw [hs]
   rw [show encodeRat δ=(ratCode δ).bits from rfl,readRational_code]
   rfl
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RawRationalSerializer
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
 def rawRationalBits (s : SignedWords) : List Bool := s.1::(prefixBits s.2.1++prefixBits s.2.2)
 def rawRationalBitsRealizer : Realizer rawRationalBits :=
   (Realizer.fst.pair (((Realizer.snd.comp Realizer.fst).comp prefixRealizer).pair
     ((Realizer.snd.comp Realizer.snd).comp prefixRealizer) |>.comp appendBits)).comp Realizer.cons
 theorem rawRationalBits_polynomial : PolyBound rawRationalBitsRealizer :=
   polynomial_comp (polynomial_pair (linear_polynomial linear_fst)
     (polynomial_comp (polynomial_pair
       (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_fst)) prefix_polynomial)
       (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_snd)) prefix_polynomial)) appendBits_polynomial))
     (linear_polynomial linear_cons)
 theorem rawRationalBits_code (q : RationalCode) : rawRationalBits (codeWords q)=q.bits := by
   simp only [rawRationalBits,codeWords,prefix_natBits,RationalCode.bits,encodeInt,List.singleton_append,List.cons_append,List.nil_append]


end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SeparatorPreprocess
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def separatorOrder : Realizer (fun s : SeparatorRaw => s.1) := Realizer.fst
 def separatorAdj : Realizer (fun s : SeparatorRaw => s.2.1) := Realizer.snd.comp Realizer.fst
 def separatorMask : Realizer (fun s : SeparatorRaw => s.2.2.1) := (Realizer.snd.comp Realizer.snd).comp Realizer.fst
 def separatorDelta : Realizer (fun s : SeparatorRaw => s.2.2.2.1) := ((Realizer.snd.comp Realizer.snd).comp Realizer.snd).comp Realizer.fst
 def separatorCosts : Realizer (fun s : SeparatorRaw => s.2.2.2.2) := ((Realizer.snd.comp Realizer.snd).comp Realizer.snd).comp Realizer.snd
 theorem separatorOrder_linear : Linear separatorOrder := linear_fst
 theorem separatorAdj_linear : Linear separatorAdj := linear_comp linear_snd linear_fst
 theorem separatorMask_linear : Linear separatorMask := linear_comp (linear_comp linear_snd linear_snd) linear_fst
 theorem separatorDelta_linear : Linear separatorDelta := linear_comp (linear_comp (linear_comp linear_snd linear_snd) linear_snd) linear_fst
 theorem separatorCosts_linear : Linear separatorCosts := linear_comp (linear_comp (linear_comp linear_snd linear_snd) linear_snd) linear_snd
 def separatorOwners := (separatorOrder.pair separatorMask).comp activeVerticesRealizer
 theorem separatorOwners_polynomial : PolyBound separatorOwners :=
   polynomial_comp (linear_polynomial (linear_pair separatorOrder_linear separatorMask_linear)) activeVertices_polynomial
 def separatorActiveOrder := separatorOwners.comp listLength
 theorem separatorActiveOrder_polynomial : PolyBound separatorActiveOrder := polynomial_comp separatorOwners_polynomial listLength_polynomial
 def separatorGraph := (separatorOrder.pair (separatorAdj.pair separatorOwners)).comp activeGraphRealizer
 theorem separatorGraph_polynomial : PolyBound separatorGraph := polynomial_comp
   (polynomial_pair (linear_polynomial separatorOrder_linear) (polynomial_pair (linear_polynomial separatorAdj_linear) separatorOwners_polynomial)) activeGraph_polynomial
 def separatorAccuracy := separatorDelta.comp rawRationalBitsRealizer
 theorem separatorAccuracy_polynomial : PolyBound separatorAccuracy :=
   polynomial_comp (linear_polynomial separatorDelta_linear) rawRationalBits_polynomial
 def separatorPathCode (L : ℕ) := (separatorActiveOrder.pair separatorDelta).comp (pathScaleCodeRealizer L)
 theorem separatorPathCode_polynomial (L : ℕ) : PolyBound (separatorPathCode L) :=
   polynomial_comp (polynomial_pair separatorActiveOrder_polynomial (linear_polynomial separatorDelta_linear)) (pathScaleCode_polynomial L)
 def separatorContext (s : SeparatorRaw) : List Bool := encodeNat s.1++s.2.2.1
 def separatorContextRealizer : Realizer separatorContext :=
   ((separatorOrder.comp naturalCodeRealizer).pair separatorMask).comp appendBits
 theorem separatorContext_polynomial : PolyBound separatorContextRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial separatorOrder_linear) naturalCode_polynomial) (linear_polynomial separatorMask_linear)) appendBits_polynomial
 def separatorPayload (L : ℕ) (s : SeparatorRaw) : List Bool :=
   activeGraphBits (s.1,(s.2.1,activeVertices s.1 s.2.2.1))++s.2.2.2.2++rawRationalBits s.2.2.2.1++
     prefixBits (pathScaleWords L ((activeVertices s.1 s.2.2.1).length,s.2.2.2.1))
 def separatorPayloadRealizer (L : ℕ) : Realizer (separatorPayload L) :=
   (((((separatorGraph.pair separatorCosts).comp appendBits).pair separatorAccuracy).comp appendBits).pair (separatorPathCode L)).comp appendBits
 theorem separatorPayload_polynomial (L : ℕ) : PolyBound (separatorPayloadRealizer L) := polynomial_comp
   (polynomial_pair (polynomial_comp (polynomial_pair (polynomial_comp
     (polynomial_pair separatorGraph_polynomial (linear_polynomial separatorCosts_linear)) appendBits_polynomial)
       separatorAccuracy_polynomial) appendBits_polynomial) (separatorPathCode_polynomial L)) appendBits_polynomial
 def separatorPreBody (L : ℕ) (s : SeparatorRaw) : List Bool := prefixBits (separatorContext s)++separatorPayload L s
 def separatorPreBodyRealizer (L : ℕ) : Realizer (separatorPreBody L) :=
   ((separatorContextRealizer.comp prefixRealizer).pair (separatorPayloadRealizer L)).comp appendBits
 theorem separatorPreBody_polynomial (L : ℕ) : PolyBound (separatorPreBodyRealizer L) := polynomial_comp
   (polynomial_pair (polynomial_comp separatorContext_polynomial prefix_polynomial) (separatorPayload_polynomial L)) appendBits_polynomial
 def separatorPreprocess (L : ℕ) (input : List Bool) : List Bool := separatorPreBody L (separatorParse input)
 def separatorPreprocessRealizer (L : ℕ) : Realizer (separatorPreprocess L) := separatorParseRealizer.comp (separatorPreBodyRealizer L)
 theorem separatorPreprocess_polynomial (L : ℕ) : PolyBound (separatorPreprocessRealizer L) := polynomial_comp separatorParse_polynomial (separatorPreBody_polynomial L)
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SeparatorPreprocessMath
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ActiveTransport HeightMath

 def activeRationalCodes {n : ℕ} (W : Finset (Fin n)) (x : Fin n → ℚ) : Fin W.card → RationalCode :=
   fun v => ratCode (x (activeMap W v))
 theorem activeRationalCodes_value {n : ℕ} (W : Finset (Fin n)) (x : Fin n → ℚ) (v : Fin W.card) :
     (activeRationalCodes W x v).value=x (activeMap W v) := ratCode_value _
 theorem activeRationalData {n : ℕ} (W : Finset (Fin n)) (x : Fin n → ℚ) (δ : ℚ) :
     rationalData (activeRationalCodes W x) (ratCode δ)=
       (W.sort (·≤·)).flatMap (fun v => encodeRat (x v))++encodeRat δ := by
   unfold rationalData
   rw [← W.listMap_orderEmbOfFin_finRange rfl,List.flatMap_map]
   simp only [List.finRange,List.flatMap_def,List.map_ofFn,Function.comp_def,ratCode_bits,activeRationalCodes]
   rfl
 theorem separatorPreprocess_correct {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (δ : ℚ) (x : Fin n → ℚ)
     (L : ℕ) (hd : 0<δ) :
     separatorPreprocess L (separatorInput G W δ x)=prefixBits (encodeNat n++mask W)++
       (flowInput (activeGraph G W) (activeRationalCodes W x) (ratCode δ)++encodeNat (pathScale L W.card δ)) := by
   rw [separatorPreprocess,separatorParse_correct]
   dsimp only [separatorPreBody,separatorContext,separatorPayload]
   have hl : (activeVertices n (mask W)).length=W.card := by rw [activeVertices_mask]; simp
   rw [activeGraph_correct,rawRationalBits_code,ratCode_bits,hl,pathScaleCode_correct L W.card δ hd]
   unfold flowInput
   rw [activeRationalData]
   simp only [List.append_assoc]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SeparatorPostprocess
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ActiveTransport

 def separatorPostHeader : Realizer (fun s : List Bool×List Bool => readNatural s.1) := Realizer.fst.comp readNaturalRealizer
 theorem separatorPostHeader_polynomial : PolyBound separatorPostHeader := polynomial_comp (linear_polynomial linear_fst) readNatural_polynomial
 def separatorPostOrder := separatorPostHeader.comp Realizer.fst
 theorem separatorPostOrder_polynomial : PolyBound separatorPostOrder := polynomial_comp separatorPostHeader_polynomial (linear_polynomial linear_fst)
 def separatorPostOwners := separatorPostHeader.comp activeVerticesRealizer
 theorem separatorPostOwners_polynomial : PolyBound separatorPostOwners := polynomial_comp separatorPostHeader_polynomial activeVertices_polynomial
 def separatorPostBody (s : List Bool×List Bool) : List Bool :=
   projectOwnerMask ((readNatural s.1).1,(activeVertices (readNatural s.1).1 (readNatural s.1).2,s.2.tail))
 def separatorPostBodyRealizer : Realizer separatorPostBody :=
   (separatorPostOrder.pair (separatorPostOwners.pair (Realizer.snd.comp BinaryAdder.tailBits))).comp projectOwnerMaskRealizer
 theorem separatorPostBody_polynomial : PolyBound separatorPostBodyRealizer := polynomial_comp
   (polynomial_pair separatorPostOrder_polynomial (polynomial_pair separatorPostOwners_polynomial
     (linear_polynomial (linear_comp linear_snd BinaryAdder.tailBits_linear)))) projectOwnerMask_polynomial
 def separatorPostprocess (input : List Bool) : List Bool := separatorPostBody (readWord input)
 def separatorPostprocessRealizer : Realizer separatorPostprocess := readWordRealizer.comp separatorPostBodyRealizer
 theorem separatorPostprocess_polynomial : PolyBound separatorPostprocessRealizer := polynomial_comp readWord_polynomial separatorPostBody_polynomial
 theorem separatorPostprocess_correct {n : ℕ} (W : Finset (Fin n)) (S : Finset (Fin W.card)) :
     separatorPostprocess (prefixBits (encodeNat n++mask W)++false::mask S)=mask (S.image (activeMap W)) := by
   rw [separatorPostprocess,readWord_prefix]
   dsimp only [separatorPostBody]
   have hb : n≤(encodeNat n++mask W).length+1 := by simp only [List.length_append,mask,List.length_ofFn]; omega
   rw [readNatural_encoded n (mask W) hb]
   simpa only [List.tail_cons,List.append_nil] using projectOwnerMask_correct W S []
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialTimeBounds
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PolynomialTimeBounds
 theorem eval_monotone (p : Polynomial ℕ) : Monotone (fun x => p.eval x) := by
   intro x y hxy
   change p.eval x≤ p.eval y
   rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
   change (∑i∈p.support,p.coeff i*x^i)≤∑i∈p.support,p.coeff i*y^i
   apply Finset.sum_le_sum
   intro i hi
   exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hxy i)
end EdgeSublinearMWIS.Main.PolynomialTimeBounds
end

-- Solutions.Reduce_lemma_6_modular
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.RawStack
open EdgeSublinearMWIS.Main.HeightMath EdgeSublinearMWIS.Main.ActiveTransport
open EdgeSublinearMWIS.Main.PolynomialTimeBounds

theorem solution (C : GraphClass) (a : ℕ) (K : ℝ)
    (separatorClass : StronglyEdgeSublinear C) (ha : 2≤ a) (bound : TreewidthBound C a K) :
    ∃ (B : ℕ) (D : ℝ) (M : Program) (time : Polynomial ℕ),0< B ∧ 0< D ∧
      (∀ (n : ℕ) (δ : ℚ),2≤ n → 0<δ → δ<1 →
        (threshold B a n δ:ℝ)≤ D*((δ:ℝ)⁻¹*logTwo n)^(4*a-2)) ∧
      (∀ (n m : ℕ) (δ : ℚ),2≤ m → m≤ n → 0<δ → δ<1 → threshold B a m δ≤ threshold B a n δ) ∧
      SeparatorContract C a B M time := by
  obtain ⟨B,L,U,timeU,hB,hL,hCall⟩ := light_separator_call C a K separatorClass.1 ha bound
  obtain ⟨M,time,Q,hPipeline⟩ := polynomial_context_program (separatorPreprocess L) separatorPostprocess
    (separatorPreprocessRealizer L) separatorPostprocessRealizer
    (separatorPreprocess_polynomial L) separatorPostprocess_polynomial U
  refine ⟨B,(B:ℝ)*4^(4*a-2)+1,M,time.comp (timeU.comp Q+Polynomial.X),hB,by positivity,?_,?_,?_⟩
  · intro n δ hn hd hd1
    exact threshold_log_bound B a n δ hn hd hd1
  · intro n m δ hm hmn hd hd1
    exact threshold_monotone B a δ hd hmn
  · intro n G W x δ hG hW hd hd1 hx hmass henergy
    let H := activeGraph G W
    let xc := activeRationalCodes W x
    let dc := ratCode δ
    let input := separatorInput G W δ x
    let ctx := encodeNat n++mask W
    let middle := flowInput H xc dc++encodeNat (pathScale L W.card δ)
    have hH : C W.card H := hereditary_active C separatorClass.1 G W hG
    have hxc : ∀v,0≤(xc v).value ∧ (xc v).value≤1 := by
      intro v
      simp only [xc,activeRationalCodes,ratCode_value]
      exact hx _ (activeMap_mem W v)
    have hdc : dc.value=δ := ratCode_value δ
    have hMass : (threshold B a W.card dc.value:ℝ)≤ vertexSum (fun v => ((xc v).value:ℝ)) Finset.univ := by
      simp only [hdc,xc,activeRationalCodes,ratCode_value]
      rw [sum_active G W (fun v => (x v:ℝ))]
      exact hmass
    have hEnergy : edgeEnergy H (fun v => ((xc v).value:ℝ))≤
        (vertexSum (fun v => ((xc v).value:ℝ)) Finset.univ)^2/threshold B a W.card dc.value := by
      simp only [hdc,xc,activeRationalCodes,ratCode_value]
      rw [sum_active G W (fun v => (x v:ℝ))]
      change edgeEnergy (activeGraph G W) (fun v => (x (activeMap W v):ℝ))≤ _
      rw [energy_active G W (fun v => (x v:ℝ))]
      exact henergy
    obtain ⟨S,tU,hU,htU,hLight⟩ := hCall W.card H xc dc hW hH hxc (by simpa only [hdc] using hd)
      (by simpa only [hdc] using hd1) hMass hEnergy
    rw [hdc] at hU htU hLight
    have hPre : separatorPreprocess L input=prefixBits ctx++middle := separatorPreprocess_correct G W δ x L hd
    obtain ⟨s,hRun,hs,hsize⟩ := hPipeline input ctx middle (false::mask S) tU hPre hU
    change Runs M input (separatorPostprocess (prefixBits ctx++(false::mask S))) s at hRun
    rw [separatorPostprocess_correct W S] at hRun
    have hLight' : Light G W (S.image (activeMap W)) δ (fun v => (x v:ℝ)) :=
      lift_light G H (activeMap W) W S δ (fun v => (x v:ℝ)) (activeMap_image W) (fun _ _ => Iff.rfl)
        (by simpa only [xc,activeRationalCodes,ratCode_value] using hLight)
    refine ⟨S.image (activeMap W),s,hRun,?_,hLight'⟩
    have htu : tU≤ timeU.eval (Q.eval (input.length+1)) := htU.trans (eval_monotone timeU hsize)
    have hinner : tU+input.length+1≤(timeU.comp Q+Polynomial.X).eval (input.length+1) := by
      simp only [Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_X]
      omega
    have hout := hs.trans (eval_monotone time hinner)
    simpa only [Polynomial.eval_comp] using hout
end
