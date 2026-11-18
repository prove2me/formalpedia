-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.lemma_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:41:38.649213+00:00
-- url     : https://prove2.me/submissions/f85a9d75-0399-4797-827f-219743c18b82
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Nat.Bits
import Mathlib.Tactic
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_OAIThreeMachineSched02
import Theorems.Thm_EdgeSublinearMWIS_Main_realizer_native_program
import Definitions.Def_EdgeSublinearMWIS_Main_Graphs
import Definitions.Def_EdgeSublinearMWIS_Main_Paths
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_EdgeSublinearMWIS_Main_WeightedExecution
import Mathlib
import Definitions.Def_EdgeSublinearMWIS_Main_BitExecution
import Theorems.Thm_EdgeSublinearMWIS_Main_gated_polynomial_context_program
import Theorems.Thm_EdgeSublinearMWIS_Main_bounded_native_iteration
import Theorems.Thm_EdgeSublinearMWIS_Main_lemma_7

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

-- Solutions.ActiveGraphTransport
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace EdgeSublinearMWIS.Main.ActiveTransport

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

end EdgeSublinearMWIS.Main.ActiveTransport
end

-- Solutions.SeparationTransport
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.SeparationTransport
open TreewidthApprox.Pushed ActiveTransport

 def Inside {n : ℕ} (G : SimpleGraph (Fin n)) (W A B : Finset (Fin n)) : Prop :=
   A.Nonempty ∧ B.Nonempty ∧ A∪B=W ∧ NoEdge G (A\B) (B\A)
 theorem lift_inside {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)) (f : Fin m ↪ Fin n)
     (W : Finset (Fin n)) (hW : Finset.univ.image f=W) (hAdj : ∀u v,H.Adj u v↔G.Adj (f u) (f v))
     (A B : Finset (Fin m)) (hsep : Separation H A B) : Inside G W (A.image f) (B.image f) := by
   refine ⟨hsep.1.image f,hsep.2.1.image f,?_,?_⟩
   · rw [← Finset.image_union,hsep.2.2.1,hW]
   · intro u hu v hv hadj
     obtain ⟨u0,hu0,rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hu).1
     obtain ⟨v0,hv0,rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hv).1
     have hub : u0∉B := by intro hb; exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_image.mpr ⟨u0,hb,rfl⟩)
     have hva : v0∉A := by intro ha; exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_image.mpr ⟨v0,ha,rfl⟩)
     exact hsep.2.2.2 u0 (Finset.mem_sdiff.mpr ⟨hu0,hub⟩) v0 (Finset.mem_sdiff.mpr ⟨hv0,hva⟩) ((hAdj u0 v0).mpr hadj)
 theorem image_inter {n m : ℕ} (f : Fin m ↪ Fin n) (A B : Finset (Fin m)) : (A∩B).image f=A.image f∩B.image f := by
   ext v
   simp only [Finset.mem_image,Finset.mem_inter]
   constructor
   · rintro ⟨u,⟨huA,huB⟩,rfl⟩
     exact ⟨⟨u,huA,rfl⟩,⟨u,huB,rfl⟩⟩
   · rintro ⟨⟨u,hu,he⟩,⟨w,hw,hwe⟩⟩
     have hwu : w=u := f.injective (hwe.trans he.symm)
     subst w
     exact ⟨u,⟨hu,hw⟩,he⟩
 theorem inside_subsets {n : ℕ} (G : SimpleGraph (Fin n)) (W A B : Finset (Fin n)) (hsep : Inside G W A B) : A⊆W ∧ B⊆W := by
   constructor <;> intro v hv <;> rw [← hsep.2.2.1]
   · exact Finset.mem_union_left B hv
   · exact Finset.mem_union_right A hv
 theorem kept_card {n : ℕ} (G : SimpleGraph (Fin n)) (W A B : Finset (Fin n)) (hsep : Inside G W A B) :
     (A\B).card+B.card=W.card := by
   have hd : Disjoint (A\B) B := by
     apply Finset.disjoint_left.mpr
     intro v hv hb
     exact (Finset.mem_sdiff.mp hv).2 hb
   have hu : (A\B)∪B=W := by rw [Finset.sdiff_union_self_eq_union,hsep.2.2.1]
   rw [← hu,Finset.card_union_of_disjoint hd]
 theorem kept_smaller {n : ℕ} (G : SimpleGraph (Fin n)) (W A B : Finset (Fin n)) (hsep : Inside G W A B) :
     (A\B).card< W.card := by
   have hh := kept_card G W A B hsep
   have hb := Finset.card_pos.mpr hsep.2.1
   omega
 theorem discarded_card {n : ℕ} (G : SimpleGraph (Fin n)) (W A B : Finset (Fin n))
     (hsep : Inside G W A B) (hAB : B.card≤ A.card) : 2*(B\A).card≤ W.card := by
   have ha := Finset.card_sdiff_add_card_inter A B
   have hb := Finset.card_sdiff_add_card_inter B A
   rw [Finset.inter_comm B A] at hb
   have hw := kept_card G W A B hsep
   omega
 theorem split_partition {n : ℕ} (G : SimpleGraph (Fin n)) (W A B : Finset (Fin n)) (hsep : Inside G W A B) :
     IsPartition3 W (A\B) (A∩B) (B\A) := by
   refine ⟨?_,?_,?_,?_⟩
   · apply Finset.disjoint_left.mpr
     intro v hv hi
     exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mp hi).2
   · apply Finset.disjoint_left.mpr
     intro v hv hi
     exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mp hi).1
   · apply Finset.disjoint_left.mpr
     intro v hv hi
     exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hv).1
   · ext v
     rw [← hsep.2.2.1]
     simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
     tauto
end EdgeSublinearMWIS.Main.SeparationTransport
end

-- Solutions.ComponentRefinement
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ComponentRefinement
open TreewidthApprox.Pushed GraphHelpers SeparationTransport

 theorem comp_mono {n : ℕ} (G : SimpleGraph (Fin n)) (S T : Finset (Fin n))
     (hST : S⊆T) (u : Fin n) : avoidComp G T u⊆avoidComp G S u := by
   intro v hv
   obtain ⟨p,hp⟩ := (comp_mem G T u v).mp hv
   exact (comp_mem G S u v).mpr ⟨p,fun w hw hs => hp w hw (hST hs)⟩
 theorem walk_stays {n : ℕ} (G : SimpleGraph (Fin n)) (X W L : Finset (Fin n))
     (hboundary : NoEdge G L ((W\X)\L)) {u v : Fin n} (p : G.Walk u v)
     (hp : ∀z∈p.support,z∈W\X) (hu : u∈L) : v∈L := by
   induction p with
   | nil => exact hu
   | @cons u w v huw p ih =>
     apply ih (fun z hz => hp z (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hz))
     by_contra hw
     exact hboundary u hu w (Finset.mem_sdiff.mpr ⟨hp w (by simp [SimpleGraph.Walk.support_cons,p.start_mem_support]),hw⟩) huw
 theorem comp_stays {n : ℕ} (G : SimpleGraph (Fin n)) (S W L : Finset (Fin n))
     (hboundary : NoEdge G L ((W\S)\L)) (u : Fin n)
     (hW : avoidComp G S u⊆W) (hu : u∈L) : avoidComp G S u⊆L := by
   intro v hv
   obtain ⟨p,hp⟩ := (comp_mem G S u v).mp hv
   apply walk_stays G S W L hboundary p _ hu
   intro z hz
   have hzComp : z∈avoidComp G S u := by
     exact (comp_mem G S u z).mpr ⟨p.takeUntil z hz,by intro w hw; exact hp w (p.support_takeUntil_subset_support hz hw)⟩
   exact Finset.mem_sdiff.mpr ⟨hW hzComp,hp z hz⟩

 def Invariant {n : ℕ} (G : SimpleGraph (Fin n)) (S W : Finset (Fin n)) : Prop :=
   Disjoint S W ∧ ∀u,u∉S → avoidComp G S u⊆W ∨ 3*(avoidComp G S u).card≤2*n
 theorem initial {n : ℕ} (G : SimpleGraph (Fin n)) : Invariant G ∅ Finset.univ := by
   refine ⟨by simp,?_⟩
   intro u hu
   exact Or.inl (Finset.subset_univ _)
 theorem cut_boundary {n : ℕ} (G : SimpleGraph (Fin n)) (S W A B : Finset (Fin n))
     (hsep : Inside G W A B) : NoEdge G (A\B) ((W\(S∪(A∩B)))\(A\B)) := by
   intro u hu v hv hadj
   have hvW := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).1
   have hvNot := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2
   have hvAB : v∈A∪B := hsep.2.2.1.symm ▸ hvW
   have hvKeep := (Finset.mem_sdiff.mp hv).2
   have hvDiscard : v∈B\A := by
     simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff] at hvAB hvNot hvKeep ⊢
     tauto
   exact hsep.2.2.2 u hu v hvDiscard hadj
 theorem inside_swap {n : ℕ} (G : SimpleGraph (Fin n)) (W A B : Finset (Fin n))
     (hsep : Inside G W A B) : Inside G W B A := by
   refine ⟨hsep.2.1,hsep.1,by rw [Finset.union_comm];exact hsep.2.2.1,?_⟩
   intro u hu v hv hadj
   exact hsep.2.2.2 v hv u hu hadj.symm
 theorem refine_cut {n : ℕ} (G : SimpleGraph (Fin n)) (S W A B : Finset (Fin n))
     (h : Invariant G S W) (hsep : Inside G W A B) (hBA : B.card≤ A.card) :
     Invariant G (S∪(A∩B)) (A\B) := by
   have hsub := inside_subsets G W A B hsep
   refine ⟨?_,?_⟩
   · apply Finset.disjoint_left.mpr
     intro u hu hk
     rcases Finset.mem_union.mp hu with hu|hu
     · exact Finset.disjoint_left.mp h.1 hu (hsub.1 (Finset.mem_sdiff.mp hk).1)
     · exact (Finset.mem_sdiff.mp hk).2 (Finset.mem_inter.mp hu).2
   · intro u hu
     have huS : u∉S := fun hs => hu (Finset.mem_union_left _ hs)
     have hm := comp_mono G S (S∪(A∩B)) Finset.subset_union_left u
     rcases h.2 u huS with hOld|hSmall
     · have hW : avoidComp G (S∪(A∩B)) u⊆W := hm.trans hOld
       have huW : u∈W := hW (comp_self G _ hu)
       have huAB : u∈A∪B := hsep.2.2.1.symm ▸ huW
       have huInter : u∉A∩B := fun hi => hu (Finset.mem_union_right _ hi)
       have hcases : u∈A\B ∨ u∈B\A := by
         simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff] at huAB huInter ⊢
         tauto
       rcases hcases with hk|hd
       · exact Or.inl (comp_stays G (S∪(A∩B)) W (A\B) (cut_boundary G S W A B hsep) u hW hk)
       · apply Or.inr
         have hb := cut_boundary G S W B A (inside_swap G W A B hsep)
         rw [Finset.inter_comm B A] at hb
         have hh := comp_stays G (S∪(A∩B)) W (B\A) hb u hW hd
         have hc := Finset.card_le_card hh
         have hD := discarded_card G W A B hsep hBA
         have hn : W.card≤ n := by simpa using Finset.card_le_univ W
         omega
     · exact Or.inr ((Nat.mul_le_mul_left 3 (Finset.card_le_card hm)).trans hSmall)
 theorem terminal {n : ℕ} (G : SimpleGraph (Fin n)) (S W : Finset (Fin n))
     (h : Invariant G S W) (hW : 3*W.card≤2*n) : Balanced G Finset.univ S := by
   refine ⟨Finset.subset_univ _,?_⟩
   intro D hD
   obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hD
   have huS := (Finset.mem_sdiff.mp hu).2
   have he : S∪(Finset.univ\(Finset.univ : Finset (Fin n)))=S := by simp
   rw [he]
   simp only [Finset.card_univ,Fintype.card_fin]
   rcases h.2 u huS with hd|hd
   · exact (Nat.mul_le_mul_left 3 (Finset.card_le_card hd)).trans hW
   · exact hd
end EdgeSublinearMWIS.Main.ComponentRefinement
end

-- Solutions.SeparatorPotential
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.SeparatorPotential
open TreewidthApprox.Pushed ComponentRefinement SeparationTransport

 theorem logTwo_mono (m n : ℕ) (hm : 1≤ m) (hmn : m≤ n) : logTwo m≤ logTwo n := by
   apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
   exact Real.log_le_log (by exact_mod_cast (show 0< m by omega)) (by exact_mod_cast hmn)
 theorem logTwo_nonneg (n : ℕ) (hn : 1≤ n) : 0≤ logTwo n :=
   div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (Real.log_nonneg (by norm_num))
 theorem cut_charge {n : ℕ} (G : SimpleGraph (Fin n)) (W A B : Finset (Fin n)) (x : Fin n → ℝ)
     (K gamma : ℝ) (hK : 0≤ K) (hg : 0< gamma) (hW : 2≤ W.card)
     (hsep : Inside G W A B)
     (hcut : vertexSum x (A∩B)≤ K*A.card*B.card*logTwo W.card/gamma) :
     vertexSum x (A∩B)≤(K*n*logTwo n/gamma)*B.card := by
   have hsub := inside_subsets G W A B hsep
   have ha : A.card≤ n := (Finset.card_le_card hsub.1).trans (by simpa using Finset.card_le_univ W)
   have hw : W.card≤ n := by simpa using Finset.card_le_univ W
   have hlog := logTwo_mono W.card n (by omega) hw
   have hlog0 := logTwo_nonneg W.card (by omega)
   have hA : (A.card:ℝ)≤ n := by exact_mod_cast ha
   have hmul := mul_le_mul hA hlog hlog0 (Nat.cast_nonneg n : (0:ℝ)≤ n)
   have hfac := mul_le_mul_of_nonneg_left hmul (mul_nonneg hK (Nat.cast_nonneg B.card : (0:ℝ)≤ B.card))
   apply hcut.trans
   calc
     K*A.card*B.card*logTwo W.card/gamma≤(K*B.card*((n:ℝ)*logTwo n))/gamma := by
       apply div_le_div_of_nonneg_right _ hg.le
       nlinarith only [hfac]
     _ = _ := by ring
 theorem potential_step {n : ℕ} (G : SimpleGraph (Fin n)) (S W A B : Finset (Fin n))
     (x : Fin n → ℝ) (F : ℝ) (h : Invariant G S W) (hsep : Inside G W A B)
     (hS : vertexSum x S≤ F*(n-W.card)) (hcut : vertexSum x (A∩B)≤ F*B.card) :
     vertexSum x (S∪(A∩B))≤ F*(n-(A\B).card) := by
   have hsub := inside_subsets G W A B hsep
   have hd : Disjoint S (A∩B) := by
     apply Finset.disjoint_left.mpr
     intro u hu hi
     exact Finset.disjoint_left.mp h.1 hu (hsub.1 (Finset.mem_inter.mp hi).1)
   have hsum : vertexSum x (S∪(A∩B))=vertexSum x S+vertexSum x (A∩B) := by
     exact Finset.sum_union hd
   have hc := kept_card G W A B hsep
   have hw : W.card≤ n := by simpa using Finset.card_le_univ W
   have hcR : ((A\B).card:ℝ)+B.card=W.card := by exact_mod_cast hc
   rw [hsum]
   have he := congrArg (fun y : ℝ => F*y) hcR
   nlinarith only [hS,hcut,he]
 theorem final_charge (n : ℕ) (K k gamma delta ell : ℝ) (S : Finset (Fin n)) (x : Fin n → ℝ)
     (hK : 0< K) (hk : 0< k) (hd : 0< delta) (hell : 0< ell) (hn : 2≤ n)
     (hg : gamma=ell*(n:ℝ)^2/(3*k))
     (hl : 3*K*delta⁻¹*logTwo n≤ ell)
     (hmass : vertexSum x S≤(K*n*logTwo n/gamma)*n) : vertexSum x S≤ delta*k := by
   have hnR : (0:ℝ)< n := by exact_mod_cast (show 0< n by omega)
   have he : (K*n*logTwo n/gamma)*n=3*K*k*logTwo n/ell := by
     rw [hg]
     field_simp
     <;> ring
   rw [he] at hmass
   apply hmass.trans
   apply (div_le_iff₀ hell).mpr
   have hh := mul_le_mul_of_nonneg_left hl (mul_nonneg hd.le hk.le)
   have hleft : delta*k*(3*K*delta⁻¹*logTwo n)=3*K*k*logTwo n := by
     field_simp
     <;> ring
   rw [hleft] at hh
   nlinarith only [hh]
end EdgeSublinearMWIS.Main.SeparatorPotential
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
open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
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
 def originalTable : Realizer (fun s : GraphRoundingInput => zipBits (vertexPairs s.1) s.2.1) :=
   ((Realizer.fst.comp vertexPairsRealizer).pair (Realizer.snd.comp Realizer.fst)).comp zipBitsRealizer
 theorem originalTable_polynomial : PolyBound originalTable := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) vertexPairs_polynomial)
     (linear_polynomial (linear_comp linear_snd linear_fst))) zipBits_polynomial
 theorem vertexPairs_bounds (n : ℕ) (p : Key) (h : p∈vertexPairs n) : p.1< n ∧ p.2< n := by
   obtain ⟨u,hu,hp⟩ := List.mem_flatMap.mp h
   obtain ⟨v,hv,he⟩ := List.mem_map.mp hp
   have hnv := List.mem_range.mp (List.mem_filter.mp hv).1
   have hnu := List.mem_range.mp hu
   subst p
   exact ⟨hnu,hnv⟩

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

end EdgeSublinearMWIS.Main.RawStack
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

-- Solutions.MaskOperations
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def maskCombine (f : Bool×Bool → Bool) (s : List Bool×List Bool) : List Bool := (zipBits s.1 s.2).map f
 def maskCombineRealizer (f : Bool×Bool → Bool) (R : Realizer f) : Realizer (maskCombine f) := zipBitsRealizer.comp (mapList R)
 theorem maskCombine_polynomial (f : Bool×Bool → Bool) (R : Realizer f) (hR : PolyBound R) : PolyBound (maskCombineRealizer f R) :=
   polynomial_comp zipBits_polynomial (polynomial_mapList hR)
 def maskInter := maskCombine (fun s => s.1 && s.2)
 def maskUnion := maskCombine (fun s => s.1 || s.2)
 def maskDiff := maskCombine (fun s => s.1 && !s.2)
 def boolDiffRealizer : Realizer (fun s : Bool×Bool => s.1 && !s.2) :=
   (Realizer.fst.pair (Realizer.snd.comp Realizer.not)).comp Realizer.and
 def maskInterRealizer : Realizer maskInter := maskCombineRealizer _ Realizer.and
 def maskUnionRealizer : Realizer maskUnion := maskCombineRealizer _ Realizer.or
 def maskDiffRealizer : Realizer maskDiff := maskCombineRealizer _ boolDiffRealizer
 theorem maskInter_polynomial : PolyBound maskInterRealizer := maskCombine_polynomial _ _ (linear_polynomial linear_and)
 theorem maskUnion_polynomial : PolyBound maskUnionRealizer := maskCombine_polynomial _ _ (linear_polynomial linear_or)
 theorem maskDiff_polynomial : PolyBound maskDiffRealizer := maskCombine_polynomial _ _
   (linear_polynomial (linear_comp (linear_pair linear_fst (linear_comp linear_snd linear_not)) linear_and))
 theorem maskCombine_mask {n : ℕ} (A B : Finset (Fin n)) (f : Bool×Bool → Bool) :
     maskCombine f (mask A,mask B)=(List.finRange n).map (fun v => f (decide (v∈A),decide (v∈B))) := by
   have hm (S : Finset (Fin n)) : mask S=(List.finRange n).map (fun v => decide (v∈S)) := by
     simp only [mask,List.finRange,List.map_ofFn];rfl
   simp only [maskCombine,hm,zipBits_map_pair,List.map_map,Function.comp_def]
 theorem maskInter_correct {n : ℕ} (A B : Finset (Fin n)) : maskInter (mask A,mask B)=mask (A∩B) := by
   rw [maskInter,maskCombine_mask]
   simp only [mask,List.finRange,List.map_ofFn]
   congr 1
   funext v
   simp
 theorem maskUnion_correct {n : ℕ} (A B : Finset (Fin n)) : maskUnion (mask A,mask B)=mask (A∪B) := by
   rw [maskUnion,maskCombine_mask]
   simp only [mask,List.finRange,List.map_ofFn]
   congr 1
   funext v
   simp
 theorem maskDiff_correct {n : ℕ} (A B : Finset (Fin n)) : maskDiff (mask A,mask B)=mask (A\B) := by
   rw [maskDiff,maskCombine_mask]
   simp only [mask,List.finRange,List.map_ofFn]
   congr 1
   funext v
   simp
 def maskCard (L : List Bool) : ℕ := (activeVertices L.length L).length
 def maskCardRealizer : Realizer maskCard := ((listLength.pair Realizer.id).comp activeVerticesRealizer).comp listLength
 theorem maskCard_polynomial : PolyBound maskCardRealizer := polynomial_comp
   (polynomial_comp (polynomial_pair listLength_polynomial (linear_polynomial linear_id)) activeVertices_polynomial) listLength_polynomial
 theorem maskCard_correct {n : ℕ} (W : Finset (Fin n)) : maskCard (mask W)=W.card := by
   unfold maskCard
   have hm : (mask W).length=n := by simp [mask]
   rw [hm,activeVertices_mask,List.length_map,Finset.length_sort]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowLoopState
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev FlowLoopState := Bool×(List Bool×(List Bool×(List Bool×(Bool×List Bool))))
 def flowLoopBits (s : FlowLoopState) : List Bool :=
   s.1::(prefixBits s.2.1++s.2.2.1++s.2.2.2.1++(s.2.2.2.2.1::s.2.2.2.2.2))
 def loopBase : Realizer (fun s : FlowLoopState => s.2.1) := Realizer.snd.comp Realizer.fst
 def loopW : Realizer (fun s : FlowLoopState => s.2.2.1) := (Realizer.snd.comp Realizer.snd).comp Realizer.fst
 def loopS : Realizer (fun s : FlowLoopState => s.2.2.2.1) := ((Realizer.snd.comp Realizer.snd).comp Realizer.snd).comp Realizer.fst
 def loopResult : Realizer (fun s : FlowLoopState => s.2.2.2.2) := ((Realizer.snd.comp Realizer.snd).comp Realizer.snd).comp Realizer.snd
 theorem loopBase_linear : Linear loopBase := linear_comp linear_snd linear_fst
 theorem loopW_linear : Linear loopW := linear_comp (linear_comp linear_snd linear_snd) linear_fst
 theorem loopS_linear : Linear loopS := linear_comp (linear_comp (linear_comp linear_snd linear_snd) linear_snd) linear_fst
 theorem loopResult_linear : Linear loopResult := linear_comp (linear_comp (linear_comp linear_snd linear_snd) linear_snd) linear_snd
 def flowLoopBitsRealizer : Realizer flowLoopBits :=
   ((Realizer.fst.pair (((loopBase.comp prefixRealizer).pair
     ((loopW.pair ((loopS.pair (loopResult.comp Realizer.cons)).comp appendBits)).comp appendBits)).comp appendBits)).comp Realizer.cons).congr (fun s => by simp only [Function.comp_apply,flowLoopBits,loopBase,loopW,loopS,loopResult,List.append_assoc])
 theorem flowLoopBits_polynomial : PolyBound flowLoopBitsRealizer := by
   unfold flowLoopBitsRealizer
   apply polynomial_congr
   exact polynomial_comp
     (polynomial_pair (linear_polynomial linear_fst) (polynomial_comp
       (polynomial_pair (polynomial_comp (linear_polynomial loopBase_linear) prefix_polynomial)
         (polynomial_comp (polynomial_pair (linear_polynomial loopW_linear)
           (polynomial_comp (polynomial_pair (linear_polynomial loopS_linear)
             (polynomial_comp (linear_polynomial loopResult_linear) (linear_polynomial linear_cons))) appendBits_polynomial)) appendBits_polynomial)) appendBits_polynomial))
     (linear_polynomial linear_cons)

 abbrev LoopAfterBase := Bool×(List Bool×(ℕ×List Bool))
 def loopReadBase (L : List Bool) : LoopAfterBase :=
   (L.headD false,((readWord L.tail).1,((readNatural (readWord L.tail).1).1,(readWord L.tail).2)))
 def loopReadBaseRealizer : Realizer loopReadBase :=
   BinaryAdder.headBit.pair (((BinaryAdder.tailBits.comp readWordRealizer).comp Realizer.fst).pair
     (((((BinaryAdder.tailBits.comp readWordRealizer).comp Realizer.fst).comp readNaturalRealizer).comp Realizer.fst).pair
       ((BinaryAdder.tailBits.comp readWordRealizer).comp Realizer.snd)))
 theorem loopReadBase_polynomial : PolyBound loopReadBaseRealizer := by
   have hr := polynomial_comp (linear_polynomial BinaryAdder.tailBits_linear) readWord_polynomial
   exact polynomial_pair (linear_polynomial BinaryAdder.headBit_linear)
     (polynomial_pair (polynomial_comp hr (linear_polynomial linear_fst))
       (polynomial_pair (polynomial_comp (polynomial_comp (polynomial_comp hr (linear_polynomial linear_fst)) readNatural_polynomial) (linear_polynomial linear_fst))
         (polynomial_comp hr (linear_polynomial linear_snd))))
 def loopSplitW : Realizer (fun s : LoopAfterBase => splitWord s.2.2.2 s.2.2.1) :=
   (((Realizer.snd.comp Realizer.snd).comp Realizer.snd).pair ((Realizer.snd.comp Realizer.snd).comp Realizer.fst)).comp splitWordRealizer
 theorem loopSplitW_polynomial : PolyBound loopSplitW := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp (linear_comp linear_snd linear_snd) linear_snd)
     (linear_comp (linear_comp linear_snd linear_snd) linear_fst))) splitWord_polynomial
 def loopSplitS : Realizer (fun s : LoopAfterBase => splitWord (splitWord s.2.2.2 s.2.2.1).2 s.2.2.1) :=
   ((loopSplitW.comp Realizer.snd).pair ((Realizer.snd.comp Realizer.snd).comp Realizer.fst)).comp splitWordRealizer
 theorem loopSplitS_polynomial : PolyBound loopSplitS := polynomial_comp
   (polynomial_pair (polynomial_comp loopSplitW_polynomial (linear_polynomial linear_snd))
     (linear_polynomial (linear_comp (linear_comp linear_snd linear_snd) linear_fst))) splitWord_polynomial
 def loopReadTail (s : LoopAfterBase) : FlowLoopState :=
   (s.1,(s.2.1,((splitWord s.2.2.2 s.2.2.1).1,((splitWord (splitWord s.2.2.2 s.2.2.1).2 s.2.2.1).1,
     (((splitWord (splitWord s.2.2.2 s.2.2.1).2 s.2.2.1).2.headD false),(splitWord (splitWord s.2.2.2 s.2.2.1).2 s.2.2.1).2.tail)))))
 def loopReadTailRealizer : Realizer loopReadTail :=
   Realizer.fst.pair ((Realizer.snd.comp Realizer.fst).pair ((loopSplitW.comp Realizer.fst).pair
     ((loopSplitS.comp Realizer.fst).pair ((loopSplitS.comp Realizer.snd).comp (BinaryAdder.headBit.pair BinaryAdder.tailBits)))))
 theorem loopReadTail_polynomial : PolyBound loopReadTailRealizer := polynomial_pair (linear_polynomial linear_fst)
   (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_fst))
     (polynomial_pair (polynomial_comp loopSplitW_polynomial (linear_polynomial linear_fst))
       (polynomial_pair (polynomial_comp loopSplitS_polynomial (linear_polynomial linear_fst))
         (polynomial_comp (polynomial_comp loopSplitS_polynomial (linear_polynomial linear_snd))
           (linear_polynomial (linear_pair BinaryAdder.headBit_linear BinaryAdder.tailBits_linear))))))
 def flowLoopParse (L : List Bool) : FlowLoopState := loopReadTail (loopReadBase L)
 def flowLoopParseRealizer : Realizer flowLoopParse := loopReadBaseRealizer.comp loopReadTailRealizer
 theorem flowLoopParse_polynomial : PolyBound flowLoopParseRealizer := polynomial_comp loopReadBase_polynomial loopReadTail_polynomial
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

-- Solutions.ConditioningParser
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace EdgeSublinearMWIS.Main.RawStack

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

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowLoopStateMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem flowLoopParse_bits (done : Bool) (base W S : List Bool) (flag : Bool) (payload : List Bool)
     (n : ℕ) (hN : (readNatural base).1=n) (hW : W.length=n) (hS : S.length=n) :
     flowLoopParse (flowLoopBits (done,(base,(W,(S,(flag,payload))))))=(done,(base,(W,(S,(flag,payload))))) := by
   have hr : readWord (prefixBits base++W++S++flag::payload)=(base,W++S++flag::payload) := by
     simpa only [List.append_assoc] using readWord_prefix base (W++S++flag::payload)
   have hW' (rest : List Bool) : splitWord (W++rest) n=(W,rest) := by
     simpa only [hW] using (show splitWord (W++rest) W.length=(W,rest) from by simp [splitWord])
   have hS' (rest : List Bool) : splitWord (S++rest) n=(S,rest) := by
     simpa only [hS] using (show splitWord (S++rest) S.length=(S,rest) from by simp [splitWord])
   dsimp only [flowLoopParse,flowLoopBits,loopReadBase]
   simp only [List.headD_cons,List.tail_cons,hr,hN]
   dsimp only [loopReadTail]
   simp only [List.append_assoc,hW',hS',List.headD_cons,List.tail_cons]
 theorem readNatural_flowInput {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode) (ell : ℕ) :
     (readNatural (flowInput G x δ++encodeNat ell)).1=n := by
   have h := graphStart_append G (rationalData x δ++encodeNat ell)
   change (graphStart (flowInput G x δ++encodeNat ell)).1=n
   simpa only [flowInput,List.append_assoc] using congrArg Prod.fst h
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

-- Solutions.ConditioningEnergyCode
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
 def sumFractions (xs : List FractionWords) : FractionWords := xs.foldl (fun s a => fractionAdd (a,s)) zeroFraction
 def sumFractionsRealizer : Realizer sumFractions := (Realizer.id.pair (Realizer.constant zeroFraction)).comp fractionAddRealizer.fold
 theorem sumFractions_polynomial : PolyBound sumFractionsRealizer :=
   polynomial_comp (linear_polynomial (linear_pair linear_id (linear_constant zeroFraction))) fractionAdd_fold_polynomial

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ConditioningFractionMath
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
 theorem fractionAdd_denpos (a b : FractionWords) (ha : 0< value a.2) (hb : 0< value b.2) :
     0< value (fractionAdd (a,b)).2 := by
   change 0< value (multiply a.2 b.2)
   rw [multiply_value]
   exact Nat.mul_pos ha hb
 theorem fractionMul_denpos (a b : FractionWords) (ha : 0< value a.2) (hb : 0< value b.2) :
     0< value (fractionMul (a,b)).2 := by
   change 0< value (multiply a.2 b.2)
   rw [multiply_value]
   exact Nat.mul_pos ha hb
 theorem fractionSum_fold_denpos (xs : List FractionWords) (s : FractionWords)
     (hs : 0< value s.2) (hx : ∀a∈xs,0< value a.2) :
     0< value (xs.foldl (fun s a => fractionAdd (a,s)) s).2 := by
   induction xs generalizing s with
   | nil => exact hs
   | cons a xs ih =>
     rw [List.foldl_cons]
     exact ih (fractionAdd (a,s)) (fractionAdd_denpos a s (hx a (by simp)) hs) (fun b hb => hx b (List.mem_cons_of_mem a hb))
 theorem fractionSum_fold_value (xs : List FractionWords) (s : FractionWords)
     (hs : 0< value s.2) (hx : ∀a∈xs,0< value a.2) :
     fractionValue (xs.foldl (fun s a => fractionAdd (a,s)) s)=fractionValue s+(xs.map fractionValue).sum := by
   induction xs generalizing s with
   | nil => simp
   | cons a xs ih =>
     rw [List.foldl_cons,ih (fractionAdd (a,s)) (fractionAdd_denpos a s (hx a (by simp)) hs)
       (fun b hb => hx b (List.mem_cons_of_mem a hb)),fractionAdd_value a s (Nat.ne_of_gt (hx a (by simp))) (Nat.ne_of_gt hs)]
     simp only [List.map_cons,List.sum_cons]
     ring
 theorem sumFractions_denpos (xs : List FractionWords) (hx : ∀a∈xs,0< value a.2) : 0< value (sumFractions xs).2 :=
   fractionSum_fold_denpos xs zeroFraction (by decide) hx
 theorem sumFractions_value (xs : List FractionWords) (hx : ∀a∈xs,0< value a.2) :
     fractionValue (sumFractions xs)=(xs.map fractionValue).sum := by
   have hh := fractionSum_fold_value xs zeroFraction (by decide) hx
   simpa only [sumFractions,zeroFraction,fractionValue,value,Bool.toNat_false,Bool.toNat_true,Nat.cast_zero,zero_div,zero_add] using hh


end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FractionDivision
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def fractionDiv (s : FractionWords×FractionWords) : FractionWords :=
   (multiply s.1.1 s.2.2,multiply s.2.1 s.1.2)
 def fractionDivRealizer : Realizer fractionDiv := crossLeft.pair crossRight
 theorem fractionDiv_polynomial : PolyBound fractionDivRealizer :=
   polynomial_pair
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst linear_fst) (linear_comp linear_snd linear_snd))) multiply_polynomial)
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) (linear_comp linear_fst linear_snd))) multiply_polynomial) 
 theorem fractionDiv_value (s t : FractionWords) : fractionValue (fractionDiv (s,t))=fractionValue s/fractionValue t := by
   dsimp only [fractionDiv,fractionValue]
   rw [multiply_value,multiply_value]
   push_cast
   simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
   ring
 def quotientWords (s : FractionWords×FractionWords) : List Bool := fractionFloor (fractionDiv s)
 def quotientWordsRealizer : Realizer quotientWords := fractionDivRealizer.comp fractionFloorRealizer
 theorem quotientWords_polynomial : PolyBound quotientWordsRealizer := polynomial_comp fractionDiv_polynomial fractionFloor_polynomial
 theorem quotientWords_value (s t : FractionWords) (hs : 0< value s.2) (ht : 0< value t.1) :
     value (quotientWords (s,t))=⌊fractionValue s/fractionValue t⌋₊ := by
   have hd : 0< value (fractionDiv (s,t)).2 := by dsimp only [fractionDiv]; rw [multiply_value]; exact Nat.mul_pos ht hs
   rw [quotientWords,fractionFloor_correct _ hd,fractionDiv_value]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowGammaCode
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev GammaRaw := ℕ×(List SignedWords×List Bool)
 def gammaCosts : Realizer (fun s : GammaRaw => sumFractions (s.2.1.map clipWords)) := ((Realizer.snd.comp Realizer.fst).comp (mapList clipWordsRealizer)).comp sumFractionsRealizer
 theorem gammaCosts_polynomial : PolyBound gammaCosts := polynomial_comp
   (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_fst)) (polynomial_mapList clipWords_polynomial)) sumFractions_polynomial
 def gammaOrderWord : Realizer (fun s : GammaRaw => natBits s.1) := Realizer.fst.comp naturalWordRealizer
 theorem gammaOrderWord_polynomial : PolyBound gammaOrderWord := polynomial_comp (linear_polynomial linear_fst) naturalWord_polynomial
 def gammaSquare : Realizer (fun s : GammaRaw => multiply (natBits s.1) (natBits s.1)) :=
   (gammaOrderWord.pair gammaOrderWord).comp multiplyRealizer
 theorem gammaSquare_polynomial : PolyBound gammaSquare := polynomial_comp
   (polynomial_pair gammaOrderWord_polynomial gammaOrderWord_polynomial) multiply_polynomial
 def gammaTop : Realizer (fun s : GammaRaw => multiply s.2.2 (multiply (natBits s.1) (natBits s.1))) :=
   ((Realizer.snd.comp Realizer.snd).pair gammaSquare).comp multiplyRealizer
 theorem gammaTop_polynomial : PolyBound gammaTop := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_snd)) gammaSquare_polynomial) multiply_polynomial
 def gammaWords (s : GammaRaw) : FractionWords :=
   let k := sumFractions (s.2.1.map clipWords)
   (multiply (multiply s.2.2 (multiply (natBits s.1) (natBits s.1))) k.2,multiply [true,true] k.1)
 def gammaWordsRealizer : Realizer gammaWords :=
   ((gammaTop.pair (gammaCosts.comp Realizer.snd)).comp multiplyRealizer).pair
     (((Realizer.constant [true,true]).pair (gammaCosts.comp Realizer.fst)).comp multiplyRealizer)
 theorem gammaWords_polynomial : PolyBound gammaWordsRealizer := polynomial_pair
   (polynomial_comp (polynomial_pair gammaTop_polynomial (polynomial_comp gammaCosts_polynomial (linear_polynomial linear_snd))) multiply_polynomial)
   (polynomial_comp (polynomial_pair (linear_polynomial (linear_constant [true,true]))
     (polynomial_comp gammaCosts_polynomial (linear_polynomial linear_fst))) multiply_polynomial)
 def gammaCode (s : GammaRaw) : List Bool := rationalBits (false,gammaWords s)
 def gammaCodeRealizer : Realizer gammaCode :=
   ((Realizer.constant false).pair gammaWordsRealizer).comp rationalBitsRealizer
 theorem gammaCode_polynomial : PolyBound gammaCodeRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_constant false)) gammaWords_polynomial) rationalBits_polynomial

 def flowEll (L : List Bool) : List Bool :=
   (readWord (readRational (readMany (graphStart L).1 (graphStart L).2.2).2).2).1
 def flowEllRealizer : Realizer flowEll :=
   (((((weightStreamRealizer.comp Realizer.snd).comp readRationalRealizer).comp Realizer.snd).comp readWordRealizer).comp Realizer.fst)
 theorem flowEll_polynomial : PolyBound flowEllRealizer := polynomial_comp
   (polynomial_comp (polynomial_comp (polynomial_comp (polynomial_comp weightStream_polynomial (linear_polynomial linear_snd)) readRational_polynomial)
     (linear_polynomial linear_snd)) readWord_polynomial) (linear_polynomial linear_fst)
 def flowGammaRaw (L : List Bool) : GammaRaw :=
   ((weightedParse L).1,((weightedParse L).2.2.1,flowEll L))
 def flowGammaRawRealizer : Realizer flowGammaRaw :=
   (weightedParseRealizer.comp Realizer.fst).pair
     (((((weightedParseRealizer.comp Realizer.snd).comp Realizer.snd).comp Realizer.fst).pair flowEllRealizer))
 theorem flowGammaRaw_polynomial : PolyBound flowGammaRawRealizer := polynomial_pair
   (polynomial_comp weightedParse_polynomial (linear_polynomial linear_fst))
   (polynomial_pair (polynomial_comp (polynomial_comp (polynomial_comp weightedParse_polynomial (linear_polynomial linear_snd))
     (linear_polynomial linear_snd)) (linear_polynomial linear_fst)) flowEll_polynomial)
 def flowGamma (L : List Bool) : List Bool := gammaCode (flowGammaRaw L)
 def flowGammaRealizer : Realizer flowGamma := flowGammaRawRealizer.comp gammaCodeRealizer
 theorem flowGamma_polynomial : PolyBound flowGammaRealizer := polynomial_comp flowGammaRaw_polynomial gammaCode_polynomial
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PointArraySemantics
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace EdgeSublinearMWIS.Main.RawStack

 def ratCode (q : ℚ) : RationalCode := ⟨q.num,q.den,q.den_pos⟩
 theorem ratCode_bits (q : ℚ) : (ratCode q).bits=encodeRat q := rfl
 theorem ratCode_value (q : ℚ) : (ratCode q).value=q := by
   exact Rat.num_div_den q

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.WeightedExecutionMath
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace EdgeSublinearMWIS.Main.WeightedExecutionMath

 theorem clipped_value (w : RationalCode) : (clippedCode w).value = max w.value 0 := by
  have hd : (0 : ℚ) < w.denominator := by exact_mod_cast w.positive
  unfold clippedCode RationalCode.value
  push_cast
  rw [← max_div_div_right (le_of_lt hd)]
  simp


end EdgeSublinearMWIS.Main.WeightedExecutionMath
end

-- Solutions.FlowGammaMath
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem weightedParse_flow_append {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode)
     (δ : RationalCode) (rest : List Bool) :
     weightedParse (flowInput G x δ++rest)=(n,(adjacencyBits G,((List.ofFn x).map codeWords,codeWords δ))) := by
   have he : rationalData x δ=(List.ofFn x).flatMap RationalCode.bits++δ.bits := by
     simp only [rationalData,List.flatMap_def,List.map_ofFn,Function.comp_def]
   have hg := graphStart_append G (rationalData x δ++rest)
   have hg' : graphStart (flowInput G x δ++rest)=(n,(adjacencyBits G,rationalData x δ++rest)) := by
     simpa only [flowInput,List.append_assoc] using hg
   dsimp only [weightedParse]
   rw [hg',he,List.append_assoc]
   have hm := readMany_codes (List.ofFn x) (δ.bits++rest)
   simp only [List.length_ofFn] at hm
   rw [hm,readRational_code]
   rfl
 theorem flowEll_correct {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode) (ell : ℕ) :
     flowEll (flowInput G x δ++encodeNat ell)=natBits ell := by
   have he : rationalData x δ=(List.ofFn x).flatMap RationalCode.bits++δ.bits := by
     simp only [rationalData,List.flatMap_def,List.map_ofFn,Function.comp_def]
   have hg := graphStart_append G (rationalData x δ++encodeNat ell)
   have hg' : graphStart (flowInput G x δ++encodeNat ell)=(n,(adjacencyBits G,rationalData x δ++encodeNat ell)) := by
     simpa only [flowInput,List.append_assoc] using hg
   dsimp only [flowEll]
   rw [hg',he,List.append_assoc]
   have hm := readMany_codes (List.ofFn x) (δ.bits++encodeNat ell)
   simp only [List.length_ofFn] at hm
   rw [hm,readRational_code]
   have hh := readWord_encoded ell []
   simpa using congrArg Prod.fst hh
 theorem flowGammaRaw_correct {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode) (ell : ℕ) :
     flowGammaRaw (flowInput G x δ++encodeNat ell)=(n,((List.ofFn x).map codeWords,natBits ell)) := by
   simp only [flowGammaRaw,weightedParse_flow_append,flowEll_correct]
 theorem clip_code_denpos (q : RationalCode) : 0< value (clipWords (codeWords q)).2 := by
   simpa only [clipWords,codeWords,value_natBits] using q.positive
 theorem clipped_cost_sum {n : ℕ} (x : Fin n → RationalCode) (hx : ∀v,0≤(x v).value) :
     fractionValue (sumFractions (((List.ofFn x).map codeWords).map clipWords))=∑v,(x v).value := by
   rw [sumFractions_value]
   · simp only [List.map_map,List.map_ofFn,List.sum_ofFn,Function.comp_def]
     apply Finset.sum_congr rfl
     intro v hv
     rw [fractionValue_code,WeightedExecutionMath.clipped_value,max_eq_left (hx v)]
   · intro a ha
     obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
     obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
     exact clip_code_denpos r
 theorem gammaCode_correct {n : ℕ} (x : Fin n → RationalCode) (ell : ℕ)
     (hx : ∀v,0≤(x v).value) (hk : 0<∑v,(x v).value) :
     gammaCode (n,((List.ofFn x).map codeWords,natBits ell))=
       encodeRat ((ell:ℚ)*(n:ℚ)^2/(3*∑v,(x v).value)) := by
   let k := sumFractions (((List.ofFn x).map codeWords).map clipWords)
   have hkD : 0< value k.2 := by
     apply sumFractions_denpos
     intro a ha
     obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
     obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
     exact clip_code_denpos r
   have hkv : fractionValue k=∑v,(x v).value := clipped_cost_sum x hx
   have hkN : 0< value k.1 := by
     by_contra hh
     have hz : value k.1=0 := by omega
     have hf : fractionValue k=0 := by simp only [fractionValue,hz,Nat.cast_zero,zero_div]
     rw [hf] at hkv
     linarith
   have hthree : value [true,true]=3 := by decide
   have hDen : 0< value (multiply [true,true] k.1) := by rw [multiply_value,hthree];omega
   dsimp only [gammaCode,gammaWords]
   rw [rationalBits_correct false _ _ hDen]
   congr 1
   change (signedValue false (multiply (multiply (natBits ell) (multiply (natBits n) (natBits n))) k.2):ℚ)/
     value (multiply [true,true] k.1)=_
   simp only [signedValue,Bool.false_eq_true,if_false,cond_false,multiply_value,value_natBits,hthree,Nat.cast_mul,Int.cast_natCast,Nat.cast_ofNat]
   have he : (value k.1:ℚ)/(value k.2:ℚ)=∑v,(x v).value := hkv
   rw [← he]
   push_cast
   field_simp
   <;> push_cast
   <;> ring
 theorem flowGamma_correct {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode) (ell : ℕ)
     (hx : ∀v,0≤(x v).value) (hk : 0<∑v,(x v).value) :
     flowGamma (flowInput G x δ++encodeNat ell)=encodeRat ((ell:ℚ)*(n:ℚ)^2/(3*∑v,(x v).value)) := by
   rw [flowGamma,flowGammaRaw_correct,gammaCode_correct x ell hx hk]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowParameters
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def flowGammaValue {n : ℕ} (x : Fin n → RationalCode) (ell : ℕ) : ℚ := (ell:ℚ)*(n:ℚ)^2/(3*∑v,(x v).value)
 theorem flowGammaValue_cast {n : ℕ} (x : Fin n → RationalCode) (ell : ℕ) :
     (flowGammaValue x ell:ℝ)=(ell:ℝ)*(n:ℝ)^2/(3*vertexSum (fun v => ((x v).value:ℝ)) Finset.univ) := by
   simp only [flowGammaValue,vertexSum]
   push_cast
   rfl
 theorem flow_parameters (n : ℕ) (K k delta : ℝ) (ell : ℕ) (hn : 2≤ n) (hK : 0< K) (hk : 0< k) (hd : 0< delta)
     (hell : (3*K+1)*delta⁻¹*logTwo n≤ ell) :
     let gamma := (ell:ℝ)*(n:ℝ)^2/(3*k)
     let F := K*n*logTwo n/gamma
     0< ell ∧ 0< gamma ∧ 0≤ F ∧ F*n≤ delta*k := by
   dsimp only
   have hlog := HeightMath.one_le_logTwo hn
   have hinv : 0< delta⁻¹ := inv_pos.mpr hd
   have hc : 0<3*K+1 := by linarith
   have hl : 0<(ell:ℝ) := lt_of_lt_of_le (mul_pos (mul_pos hc hinv) (by linarith)) hell
   have hnR : (0:ℝ)< n := by exact_mod_cast (show 0< n by omega)
   have hg : 0<(ell:ℝ)*(n:ℝ)^2/(3*k) := by positivity
   refine ⟨by exact_mod_cast hl,hg,by positivity,?_⟩
   have hth : 3*K*delta⁻¹*logTwo n≤ ell := by
     have hm := mul_le_mul_of_nonneg_right (show 3*K≤3*K+1 by linarith) (mul_nonneg hinv.le (by linarith : 0≤ logTwo n))
     nlinarith only [hm,hell]
   have he : (K*n*logTwo n/((ell:ℝ)*(n:ℝ)^2/(3*k)))*n=3*K*k*logTwo n/ell := by
     field_simp
     <;> ring
   rw [he]
   apply (div_le_iff₀ hl).mpr
   have hm := mul_le_mul_of_nonneg_left hth (mul_nonneg hd.le hk.le)
   have he : delta*k*(3*K*delta⁻¹*logTwo n)=3*K*k*logTwo n := by
     field_simp
     <;> ring
   rw [he] at hm
   nlinarith only [hm]
 theorem flow_total_positive {n : ℕ} (x : Fin n → RationalCode)
     (hk : 0< vertexSum (fun v => ((x v).value:ℝ)) Finset.univ) : 0<∑v,(x v).value := by
   change 0<∑v:Fin n,((x v).value:ℝ) at hk
   exact_mod_cast hk
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowSevenContract
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
 def FlowSevenContract (U : Program) (K : ℝ) (time : Polynomial ℕ) : Prop :=
   ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (gamma : RationalCode),
     2≤ n → (∀v,0≤(x v).value) → 0< gamma.value →
     ∃t,t≤ time.eval ((flowInput G x gamma).length+1) ∧
       ((∃f : List (List (Fin n)×ℚ),Runs U (flowInput G x gamma) (false::encodeSparsePaths f) t ∧ UnitFlow G f ∧
         ∀v,vertexMass (realPaths f) v≤(gamma.value:ℝ)*((x v).value:ℝ)) ∨
        ∃A B : Finset (Fin n),Runs U (flowInput G x gamma) (true::(mask A++mask B)) t ∧ Separation G A B ∧
         vertexSum (fun v => ((x v).value:ℝ)) (A∩B)≤ K*A.card*B.card*logTwo n/(gamma.value:ℝ))
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.StreamParserIteration
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]
 theorem volume_pair_eta {β γ : Type} [Coding β] [Coding γ] (s : β×γ) : volume s=volume s.1+volume s.2+1 := by cases s;exact volume_pair _ _
 def streamStep (f : List Bool → α×List Bool) (s : List Bool×List α) : List Bool×List α :=
   ((f s.1).2,(f s.1).1::s.2)
 def streamStepRealizer {f : List Bool → α×List Bool} (R : Realizer f) : Realizer (streamStep f) :=
   ((Realizer.fst.comp R).comp Realizer.snd).pair
     ((((Realizer.fst.comp R).comp Realizer.fst).pair Realizer.snd).comp Realizer.cons)
 theorem streamStep_polynomial {f : List Bool → α×List Bool} (R : Realizer f) (hR : PolyBound R) :
     PolyBound (streamStepRealizer R) := polynomial_pair
   (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) hR) (linear_polynomial linear_snd))
   (polynomial_comp (polynomial_pair (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) hR) (linear_polynomial linear_fst))
     (linear_polynomial linear_snd)) (linear_polynomial linear_cons))
 theorem streamStep_iterate_bound {f : List Bool → α×List Bool} (C q : ℕ)
     (hf : ∀L,volume (f L).1≤ C*(volume L+1)^q) (hr : ∀L,volume (f L).2≤ volume L)
     (s : List Bool×List α) (j : ℕ) :
     volume ((streamStep f)^[j] s).1≤ volume s.1 ∧
       volume ((streamStep f)^[j] s)≤ volume s+j*(C*(volume s.1+1)^q+1) := by
   induction j with
   | zero => simp
   | succ j ih =>
     rw [Function.iterate_succ_apply']
     have hrest := hr ((streamStep f)^[j] s).1
     have hentry := hf ((streamStep f)^[j] s).1
     have hp := Nat.pow_le_pow_left (Nat.add_le_add_right ih.1 1) q
     have he := hentry.trans (Nat.mul_le_mul_left C hp)
     refine ⟨hrest.trans ih.1,?_⟩
     simp only [streamStep,volume_pair,volume_cons]
     have hi := ih.2
     rw [volume_pair_eta ((streamStep f)^[j] s)] at hi
     nlinarith
 theorem streamStep_iterate_polynomial {f : List Bool → α×List Bool} (R : Realizer f)
     (hR : PolyBound R) (hr : ∀L,volume (f L).2≤ volume L) : PolyBound (streamStepRealizer R).iterate := by
   obtain ⟨C,q,hC,hR'⟩ := hR
   apply polynomial_iterate_growth (streamStep_polynomial R ⟨C,q,hC,hR'⟩) (C+10) (q+2)
   intro s j
   have hentry (L : List Bool) : volume (f L).1≤ C*(volume L+1)^q := by
     have hh := (hR' L).2
     rw [volume_pair_eta (f L)] at hh
     omega
   have hh := (streamStep_iterate_bound C q hentry hr s j).2
   let z := volume s+j+1
   have hz : 1≤ z := by dsimp [z];omega
   have hs : volume s≤ z := by dsimp [z];omega
   have hj : j≤ z := by dsimp [z];omega
   have hL : volume s.1+1≤ z := by dsimp [z];rw [volume_pair_eta s];omega
   have hq := Nat.pow_le_pow_left hL q
   have hp : 1≤ z^q := one_le_pow₀ hz
   have hmul := Nat.mul_le_mul hj (show C*(volume s.1+1)^q+1≤(C+1)*z^q by nlinarith only [hq,hp])
   have hpow : z^(q+1)≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hlow : z≤ z^(q+2) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+2)
   have hprod : z*((C+1)*z^q)=(C+1)*z^(q+1) := by rw [pow_succ];ring
   rw [hprod] at hmul
   change volume ((streamStep f)^[j] s)≤(C+10)*z^(q+2)
   nlinarith only [hh,hs,hmul,Nat.mul_le_mul_left (C+1) hpow,hlow]
end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.ProjectionSemantics
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler
 theorem map_range_ofFn {α : Type} (n : ℕ) (f : ℕ → α) : (List.range n).map f=List.ofFn (fun i : Fin n => f i.val) := by
   rw [← finRange_val n,List.map_map]
   simp only [List.finRange,List.map_ofFn,Function.comp_def,id_eq]
 noncomputable def natMask {N : ℕ} (J : Finset (Fin N)) (i : ℕ) : Bool :=
   if hi : i< N then decide ((⟨i,hi⟩ : Fin N)∈J) else false
 theorem mask_range {N : ℕ} (J : Finset (Fin N)) : mask J=(List.range N).map (natMask J) := by
   rw [map_range_ofFn]
   unfold mask
   apply congrArg List.ofFn
   funext i
   simp only [natMask,dif_pos i.isLt]
 theorem containsOwner_true (xs : List ℕ) (v : ℕ) : containsOwner (v,xs)=true ↔ v∈xs := by
   dsimp only [containsOwner]
   simp

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.WordArrayCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev WordArrayState := List Bool×List (List Bool)
 def wordArrayStep (s : WordArrayState) : WordArrayState := let w := readWord s.1; (w.2,w.1::s.2)
 def wordArrayStepRealizer : Realizer wordArrayStep :=
   (((Realizer.fst.comp readWordRealizer).comp Realizer.snd).pair
     ((((Realizer.fst.comp readWordRealizer).comp Realizer.fst).pair Realizer.snd).comp Realizer.cons))
 theorem wordArrayStep_polynomial : PolyBound wordArrayStepRealizer :=
   polynomial_pair (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) readWord_polynomial) (linear_polynomial linear_snd))
     (polynomial_comp (polynomial_pair (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) readWord_polynomial)
       (linear_polynomial linear_fst)) (linear_polynomial linear_snd)) (linear_polynomial linear_cons))
 theorem wordArrayStep_volume (s : WordArrayState) : volume (wordArrayStep s)≤ volume s+2 := by
   rcases s with ⟨L,acc⟩
   have hh := readWord_volume L
   simp only [wordArrayStep,volume_pair,volume_cons]
   omega
 def readWords (n : ℕ) (L : List Bool) : List (List Bool)×List Bool :=
   let s := wordArrayStep^[n] (L,[])
   (s.2.reverse,s.1)
 def readWordsRealizer : Realizer (fun s : ℕ×List Bool => readWords s.1 s.2) :=
   (((Realizer.fst.pair (Realizer.snd.pair Realizer.nil)).comp wordArrayStepRealizer.iterate).comp
     ((Realizer.snd.comp Realizer.reverse).pair Realizer.fst))
 theorem readWords_polynomial : PolyBound readWordsRealizer := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : ℕ×List Bool => ([] : List (List Bool)))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   exact polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_fst)
     (polynomial_pair (linear_polynomial linear_snd) (linear_polynomial hn)))
       (polynomial_iterate wordArrayStep_polynomial 2 wordArrayStep_volume))
     (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) reverse_polynomial_generic) (linear_polynomial linear_fst))
 def wordArrayBits (ws : List (List Bool)) : List Bool := ws.flatMap prefixBits
 def wordArrayBitsRealizer : Realizer wordArrayBits := (mapList prefixRealizer).comp flattenList
 theorem wordArrayBits_polynomial : PolyBound wordArrayBitsRealizer := polynomial_comp (polynomial_mapList prefix_polynomial) flattenList_polynomial
 theorem wordArray_run (ws : List (List Bool)) (rest : List Bool) (acc : List (List Bool)) :
     wordArrayStep^[ws.length] (wordArrayBits ws++rest,acc)=(rest,ws.reverse++acc) := by
   induction ws generalizing acc with
   | nil => simp [wordArrayBits]
   | cons a ws ih =>
     rw [List.length_cons,Function.iterate_succ_apply]
     simp only [wordArrayBits,List.flatMap_cons,List.append_assoc,wordArrayStep,readWord_prefix]
     rw [← wordArrayBits,ih,List.reverse_cons]
     simp only [List.append_assoc,List.singleton_append]
 theorem readWords_bits (ws : List (List Bool)) (rest : List Bool) : readWords ws.length (wordArrayBits ws++rest)=(ws,rest) := by
   dsimp only [readWords]
   rw [wordArray_run]
   simp
 theorem wordArrayBits_length (ws : List (List Bool)) : ws.length≤(wordArrayBits ws).length := by
   induction ws with
   | nil => simp [wordArrayBits]
   | cons a ws ih =>
     have he : (wordArrayBits (a::ws)).length=(prefixBits a).length+(wordArrayBits ws).length := by simp [wordArrayBits]
     have ha : 1≤(prefixBits a).length := by simp [prefixBits]; omega
     rw [he,List.length_cons]
     omega

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SparsePathParser
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem readWord_rest_volume (L : List Bool) : volume (readWord L).2≤ volume L := by
   have hh := readWord_volume L
   have hp := volume_pos (readWord L).1
   omega
 theorem readNatural_rest_volume (L : List Bool) : volume (readNatural L).2≤ volume L := readWord_rest_volume L
 theorem readRational_rest_volume (L : List Bool) : volume (readRational L).2≤ volume L := by
   exact (readWord_rest_volume (readWord L.tail).2).trans ((readWord_rest_volume L.tail).trans (tailList_volume L))
 theorem wordArray_remaining_volume (n : ℕ) (s : WordArrayState) : volume (wordArrayStep^[n] s).1≤ volume s.1 := by
   induction n with
   | zero => exact le_rfl
   | succ n ih =>
     rw [Function.iterate_succ_apply']
     exact (readWord_rest_volume (wordArrayStep^[n] s).1).trans ih
 theorem readWords_rest_volume (n : ℕ) (L : List Bool) : volume (readWords n L).2≤ volume L := wordArray_remaining_volume n (L,[])
 def readRawPath (L : List Bool) : List (List Bool)×List Bool := readWords (readNatural L).1 (readNatural L).2
 def readRawPathRealizer : Realizer readRawPath := readNaturalRealizer.comp readWordsRealizer
 theorem readRawPath_polynomial : PolyBound readRawPathRealizer := polynomial_comp readNatural_polynomial readWords_polynomial
 theorem readRawPath_rest_volume (L : List Bool) : volume (readRawPath L).2≤ volume L :=
   (readWords_rest_volume _ _).trans (readNatural_rest_volume L)
 abbrev RawPathEntry := List (List Bool)×SignedWords
 def readPathEntry (L : List Bool) : RawPathEntry×List Bool :=
   (((readRawPath L).1,(readRational (readRawPath L).2).1),(readRational (readRawPath L).2).2)
 def readPathEntryRealizer : Realizer readPathEntry :=
   ((readRawPathRealizer.comp Realizer.fst).pair (((readRawPathRealizer.comp Realizer.snd).comp readRationalRealizer).comp Realizer.fst)).pair
     (((readRawPathRealizer.comp Realizer.snd).comp readRationalRealizer).comp Realizer.snd)
 theorem readPathEntry_polynomial : PolyBound readPathEntryRealizer := by
   have hr := polynomial_comp (polynomial_comp readRawPath_polynomial (linear_polynomial linear_snd)) readRational_polynomial
   exact polynomial_pair (polynomial_pair (polynomial_comp readRawPath_polynomial (linear_polynomial linear_fst))
     (polynomial_comp hr (linear_polynomial linear_fst))) (polynomial_comp hr (linear_polynomial linear_snd))
 theorem readPathEntry_rest_volume (L : List Bool) : volume (readPathEntry L).2≤ volume L :=
   (readRational_rest_volume (readRawPath L).2).trans (readRawPath_rest_volume L)
 def readPathEntries (n : ℕ) (L : List Bool) : List RawPathEntry×List Bool :=
   let s := (streamStep readPathEntry)^[n] (L,[])
   (s.2.reverse,s.1)
 def readPathEntriesRealizer : Realizer (fun s : ℕ×List Bool => readPathEntries s.1 s.2) :=
   (((Realizer.fst.pair (Realizer.snd.pair Realizer.nil)).comp (streamStepRealizer readPathEntryRealizer).iterate).comp
     ((Realizer.snd.comp Realizer.reverse).pair Realizer.fst))
 theorem readPathEntries_polynomial : PolyBound readPathEntriesRealizer := by
   have hn : PolyBound (Realizer.nil : Realizer (fun _ : ℕ×List Bool => ([] : List RawPathEntry))) :=
     linear_polynomial (linear_of _ 3 (by omega) (fun _ => by change 2≤ _;omega) (fun _ => by simp;omega))
   exact polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_fst)
     (polynomial_pair (linear_polynomial linear_snd) hn))
     (streamStep_iterate_polynomial readPathEntryRealizer readPathEntry_polynomial readPathEntry_rest_volume))
     (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) reverse_polynomial_generic) (linear_polynomial linear_fst))
 def readSparsePaths (L : List Bool) : List RawPathEntry := (readPathEntries (readNatural L).1 (readNatural L).2).1
 def readSparsePathsRealizer : Realizer readSparsePaths := (readNaturalRealizer.comp readPathEntriesRealizer).comp Realizer.fst
 theorem readSparsePaths_polynomial : PolyBound readSparsePathsRealizer := polynomial_comp
   (polynomial_comp readNatural_polynomial readPathEntries_polynomial) (linear_polynomial linear_fst)
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SparsePathParserMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def rawPathWords {n : ℕ} (p : List (Fin n)) : List (List Bool) := p.map (fun v => natBits v.val)
 def rawPathEntry {n : ℕ} (e : List (Fin n)×ℚ) : RawPathEntry := (rawPathWords e.1,codeWords (ratCode e.2))
 theorem pathBits_words {n : ℕ} (p : List (Fin n)) : encodePath p=encodeNat p.length++wordArrayBits (rawPathWords p) := by
   simp only [encodePath,wordArrayBits,rawPathWords,List.flatMap_map,prefix_natBits]
 theorem readRawPath_correct {n : ℕ} (p : List (Fin n)) (rest : List Bool) :
     readRawPath (encodePath p++rest)=(rawPathWords p,rest) := by
   have hw : (rawPathWords p).length=p.length := by simp [rawPathWords]
   have hlen := wordArrayBits_length (rawPathWords p)
   have hp : p.length≤(encodePath p++rest).length+1 := by
     rw [pathBits_words,List.length_append,List.length_append]
     omega
   rw [pathBits_words,List.append_assoc] at hp
   dsimp only [readRawPath]
   rw [pathBits_words,List.append_assoc,readNatural_encoded p.length _ hp]
   rw [← hw,readWords_bits]
 theorem readPathEntry_correct {n : ℕ} (e : List (Fin n)×ℚ) (rest : List Bool) :
     readPathEntry ((encodePath e.1++encodeRat e.2)++rest)=(rawPathEntry e,rest) := by
   dsimp only [readPathEntry]
   rw [List.append_assoc,readRawPath_correct]
   have he : encodeRat e.2=(ratCode e.2).bits := rfl
   rw [he,readRational_code]
   rfl
 def pathEntryBits {n : ℕ} (f : List (List (Fin n)×ℚ)) : List Bool :=
   f.flatMap (fun e => encodePath e.1++encodeRat e.2)
 theorem pathEntryBits_length {n : ℕ} (f : List (List (Fin n)×ℚ)) : f.length≤(pathEntryBits f).length := by
   induction f with
   | nil => simp [pathEntryBits]
   | cons a f ih =>
     have hprefix : 1≤(encodeNat a.1.length).length := by simp [encodeNat];omega
     simp only [pathEntryBits,List.flatMap_cons,List.length_append,encodePath,List.length_cons] at ih ⊢
     omega
 theorem pathEntries_run {n : ℕ} (f : List (List (Fin n)×ℚ)) (rest : List Bool) (acc : List RawPathEntry) :
     (streamStep readPathEntry)^[f.length] (pathEntryBits f++rest,acc)=
       (rest,(f.map rawPathEntry).reverse++acc) := by
   induction f generalizing acc with
   | nil => simp [pathEntryBits]
   | cons a f ih =>
     rw [List.length_cons,Function.iterate_succ_apply]
     simp only [pathEntryBits,List.flatMap_cons,List.append_assoc,streamStep]
     rw [← List.append_assoc (encodePath a.1) (encodeRat a.2),readPathEntry_correct]
     rw [← pathEntryBits,ih,List.map_cons,List.reverse_cons]
     simp only [List.append_assoc,List.singleton_append]
 theorem readSparsePaths_correct {n : ℕ} (f : List (List (Fin n)×ℚ)) :
     readSparsePaths (encodeSparsePaths f)=f.map rawPathEntry := by
   have hlen := pathEntryBits_length f
   have hp : f.length≤(encodeSparsePaths f).length+1 := by
     change f.length≤(encodeNat f.length++pathEntryBits f).length+1
     simp only [List.length_append]
     omega
   unfold readSparsePaths encodeSparsePaths
   rw [readNatural_encoded f.length _ hp]
   change (readPathEntries f.length (pathEntryBits f)).1=_
   dsimp only [readPathEntries]
   have hh := pathEntries_run f [] []
   simp only [List.append_nil] at hh
   rw [hh]
   simp
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MaskSelect
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
variable {α : Type} [Coding α]
 def maskSelect (s : List α×List Bool) : List α := ((zipBits s.1 s.2).filter (fun e => e.2)).map Prod.fst
 def selectTaggedRealizer : Realizer (fun xs : List (α×Bool) => (xs.filter (fun e => e.2)).map Prod.fst) :=
   ((Realizer.id.pair (Realizer.constant ())).comp (filterEnvironment (Realizer.fst.comp Realizer.snd))).comp (mapList Realizer.fst)
 theorem selectTagged_polynomial : PolyBound (selectTaggedRealizer (α:=α)) := polynomial_comp
   (polynomial_comp (linear_polynomial (linear_pair linear_id (linear_constant ())))
     (filterEnvironment_polynomial (linear_polynomial (linear_comp linear_fst linear_snd))))
   (polynomial_mapList (linear_polynomial linear_fst))
 def maskSelectRealizer : Realizer (maskSelect (α:=α)) := zipBitsRealizer.comp selectTaggedRealizer
 theorem maskSelect_polynomial : PolyBound (maskSelectRealizer (α:=α)) := polynomial_comp zipBits_polynomial selectTagged_polynomial
 theorem maskSelect_correct {n : ℕ} (W : Finset (Fin n)) (f : Fin n → α) :
     maskSelect (List.ofFn f,mask W)=(W.sort (·≤·)).map f := by
   have hf : ((List.finRange n).filter (fun v => decide (v∈W)))=W.sort (·≤·) := by
     exact (((List.sortedLT_finRange n).pairwise.filter _).sortedLT).eq_of_mem_iff W.sortedLT_sort (by intro v;simp)
   have hm : mask W=(List.finRange n).map (fun v => decide (v∈W)) := by simp only [mask,List.finRange,List.map_ofFn];rfl
   have he : List.ofFn f=(List.finRange n).map f := by simp only [List.finRange,List.map_ofFn];rfl
   unfold maskSelect
   rw [he,hm,zipBits_map_pair]
   simp only [List.filter_map,List.map_map,Function.comp_def]
   rw [hf]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.HalfAccuracyCode
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

-- Solutions.FlowActiveCall
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def loopOriginal : Realizer (fun s : FlowLoopState => weightedParse s.2.1) := loopBase.comp weightedParseRealizer
 theorem loopOriginal_polynomial : PolyBound loopOriginal := polynomial_comp (linear_polynomial loopBase_linear) weightedParse_polynomial
 def loopOrder : Realizer (fun s : FlowLoopState => (weightedParse s.2.1).1) := loopOriginal.comp Realizer.fst
 def loopAdj : Realizer (fun s : FlowLoopState => (weightedParse s.2.1).2.1) := (loopOriginal.comp Realizer.snd).comp Realizer.fst
 def loopWeights : Realizer (fun s : FlowLoopState => (weightedParse s.2.1).2.2.1) :=
   ((loopOriginal.comp Realizer.snd).comp Realizer.snd).comp Realizer.fst
 theorem loopOrder_polynomial : PolyBound loopOrder := polynomial_comp loopOriginal_polynomial (linear_polynomial linear_fst)
 theorem loopAdj_polynomial : PolyBound loopAdj := polynomial_comp (polynomial_comp loopOriginal_polynomial (linear_polynomial linear_snd)) (linear_polynomial linear_fst)
 theorem loopWeights_polynomial : PolyBound loopWeights := polynomial_comp
   (polynomial_comp (polynomial_comp loopOriginal_polynomial (linear_polynomial linear_snd)) (linear_polynomial linear_snd)) (linear_polynomial linear_fst)
 def loopOwners := (loopOrder.pair loopW).comp activeVerticesRealizer
 theorem loopOwners_polynomial : PolyBound loopOwners := polynomial_comp
   (polynomial_pair loopOrder_polynomial (linear_polynomial loopW_linear)) activeVertices_polynomial
 def loopActiveGraph := (loopOrder.pair (loopAdj.pair loopOwners)).comp activeGraphRealizer
 theorem loopActiveGraph_polynomial : PolyBound loopActiveGraph := polynomial_comp
   (polynomial_pair loopOrder_polynomial (polynomial_pair loopAdj_polynomial loopOwners_polynomial)) activeGraph_polynomial
 def loopActiveCosts := (loopWeights.pair loopW).comp maskSelectRealizer
 theorem loopActiveCosts_polynomial : PolyBound loopActiveCosts := polynomial_comp
   (polynomial_pair loopWeights_polynomial (linear_polynomial loopW_linear)) maskSelect_polynomial
 def loopCostBits := (loopActiveCosts.comp (mapList rawRationalBitsRealizer)).comp flattenList
 theorem loopCostBits_polynomial : PolyBound loopCostBits := polynomial_comp
   (polynomial_comp loopActiveCosts_polynomial (polynomial_mapList rawRationalBits_polynomial)) flattenList_polynomial
 def flowActivePayload (s : FlowLoopState) : List Bool :=
   activeGraphBits ((weightedParse s.2.1).1,((weightedParse s.2.1).2.1,activeVertices (weightedParse s.2.1).1 s.2.2.1))++
     (maskSelect ((weightedParse s.2.1).2.2.1,s.2.2.1)).flatMap rawRationalBits++flowGamma s.2.1
 def flowActivePayloadRealizer : Realizer flowActivePayload :=
   ((((loopActiveGraph.pair loopCostBits).comp appendBits).pair (loopBase.comp flowGammaRealizer)).comp appendBits).congr (fun s => by
     simp only [Function.comp_apply,flowActivePayload,loopActiveGraph,loopOwners,loopOrder,loopAdj,loopOriginal,loopW,
       loopCostBits,loopActiveCosts,loopWeights,loopBase,List.flatMap_def])
 theorem flowActivePayload_polynomial : PolyBound flowActivePayloadRealizer := by
   unfold flowActivePayloadRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (polynomial_comp (polynomial_pair loopActiveGraph_polynomial loopCostBits_polynomial) appendBits_polynomial)
     (polynomial_comp (linear_polynomial loopBase_linear) flowGamma_polynomial)) appendBits_polynomial
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

-- Solutions.FlowCutCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def orientMasks (s : List Bool×List Bool) : List Bool×List Bool :=
   if maskCard s.2≤ maskCard s.1 then s else (s.2,s.1)
 def orientTest : Realizer (fun s : List Bool×List Bool => decide (maskCard s.2≤ maskCard s.1)) :=
   ((Realizer.snd.comp maskCardRealizer).pair (Realizer.fst.comp maskCardRealizer)).comp Realizer.le
 def orientMasksRealizer : Realizer orientMasks :=
   ((orientTest.pair Realizer.id).comp (Realizer.id.choose (Realizer.snd.pair Realizer.fst))).congr (fun s => by simp [Function.comp_apply,orientMasks])
 theorem orientTest_polynomial : PolyBound orientTest := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) maskCard_polynomial)
     (polynomial_comp (linear_polynomial linear_fst) maskCard_polynomial)) nat_le_polynomial
 theorem orientMasks_polynomial : PolyBound orientMasksRealizer := by
   unfold orientMasksRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair orientTest_polynomial (linear_polynomial linear_id))
     (polynomial_choose (linear_polynomial linear_id) (linear_polynomial (linear_pair linear_snd linear_fst)))

 abbrev FlowPostRaw := FlowLoopState×List Bool
 def postOrder : Realizer (fun s : FlowPostRaw => (weightedParse s.1.2.1).1) := Realizer.fst.comp loopOrder
 def postOwners : Realizer (fun s : FlowPostRaw => activeVertices (weightedParse s.1.2.1).1 s.1.2.2.1) := Realizer.fst.comp loopOwners
 def postActiveOrder : Realizer (fun s : FlowPostRaw => maskCard s.1.2.2.1) := ((Realizer.fst.comp loopW).comp maskCardRealizer)
 theorem postOrder_polynomial : PolyBound (postOrder : Realizer (fun s : FlowPostRaw => (weightedParse s.1.2.1).1)) :=
   polynomial_comp (linear_polynomial linear_fst) loopOrder_polynomial
 theorem postOwners_polynomial : PolyBound (postOwners : Realizer (fun s : FlowPostRaw => activeVertices (weightedParse s.1.2.1).1 s.1.2.2.1)) :=
   polynomial_comp (linear_polynomial linear_fst) loopOwners_polynomial
 theorem postActiveOrder_polynomial : PolyBound (postActiveOrder : Realizer (fun s : FlowPostRaw => maskCard s.1.2.2.1)) :=
   polynomial_comp (polynomial_comp (linear_polynomial linear_fst) (linear_polynomial loopW_linear)) maskCard_polynomial
 def postFirstSplit : Realizer (fun s : FlowPostRaw => splitWord s.2.tail (maskCard s.1.2.2.1)) :=
   ((Realizer.snd.comp BinaryAdder.tailBits).pair postActiveOrder).comp splitWordRealizer
 theorem postFirstSplit_polynomial : PolyBound postFirstSplit := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_comp linear_snd BinaryAdder.tailBits_linear)) postActiveOrder_polynomial) splitWord_polynomial
 def postSecondSplit : Realizer (fun s : FlowPostRaw => splitWord (splitWord s.2.tail (maskCard s.1.2.2.1)).2 (maskCard s.1.2.2.1)) :=
   ((postFirstSplit.comp Realizer.snd).pair postActiveOrder).comp splitWordRealizer
 theorem postSecondSplit_polynomial : PolyBound postSecondSplit := polynomial_comp
   (polynomial_pair (polynomial_comp postFirstSplit_polynomial (linear_polynomial linear_snd)) postActiveOrder_polynomial) splitWord_polynomial
 def postA := (postOrder.pair (postOwners.pair (postFirstSplit.comp Realizer.fst))).comp projectOwnerMaskRealizer
 def postB := (postOrder.pair (postOwners.pair (postSecondSplit.comp Realizer.fst))).comp projectOwnerMaskRealizer
 theorem postA_polynomial : PolyBound postA := polynomial_comp
   (polynomial_pair postOrder_polynomial (polynomial_pair postOwners_polynomial (polynomial_comp postFirstSplit_polynomial (linear_polynomial linear_fst)))) projectOwnerMask_polynomial
 theorem postB_polynomial : PolyBound postB := polynomial_comp
   (polynomial_pair postOrder_polynomial (polynomial_pair postOwners_polynomial (polynomial_comp postSecondSplit_polynomial (linear_polynomial linear_fst)))) projectOwnerMask_polynomial
 def postOriented := (postA.pair postB).comp orientMasksRealizer
 theorem postOriented_polynomial : PolyBound postOriented := polynomial_comp (polynomial_pair postA_polynomial postB_polynomial) orientMasks_polynomial

 def cutUpdate (s : FlowLoopState×(List Bool×List Bool)) : FlowLoopState :=
   (false,(s.1.2.1,(maskDiff s.2,(maskUnion (s.1.2.2.2.1,maskInter s.2),(false,[])))))
 def cutUpdateRealizer : Realizer cutUpdate :=
   (Realizer.constant false).pair ((Realizer.fst.comp loopBase).pair
     ((Realizer.snd.comp maskDiffRealizer).pair
       (((((Realizer.fst.comp loopS).pair (Realizer.snd.comp maskInterRealizer)).comp maskUnionRealizer)).pair
         ((Realizer.constant false).pair Realizer.nil))))
 theorem cutUpdate_polynomial : PolyBound cutUpdateRealizer := by
   have hn : PolyBound (Realizer.nil : Realizer (fun _ : FlowLoopState×(List Bool×List Bool) => ([] : List Bool))) :=
     linear_polynomial (linear_of _ 3 (by omega) (fun _ => by change 2≤ _;omega) (fun _ => by simp;omega))
   exact polynomial_pair (linear_polynomial (linear_constant false))
     (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) (linear_polynomial loopBase_linear))
       (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) maskDiff_polynomial)
         (polynomial_pair (polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) (linear_polynomial loopS_linear))
           (polynomial_comp (linear_polynomial linear_snd) maskInter_polynomial)) maskUnion_polynomial)
           (polynomial_pair (linear_polynomial (linear_constant false)) hn))))
 def flowCutUpdateRealizer := (Realizer.fst.pair postOriented).comp cutUpdateRealizer
 theorem flowCutUpdate_polynomial : PolyBound flowCutUpdateRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial linear_fst) postOriented_polynomial) cutUpdate_polynomial
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowLoopPre
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def twiceNatRealizer : Realizer (fun n : ℕ => n+n) := (Realizer.id.pair Realizer.id).comp Realizer.add
 def thriceNatRealizer : Realizer (fun n : ℕ => n+n+n) := (twiceNatRealizer.pair Realizer.id).comp Realizer.add
 theorem twiceNat_polynomial : PolyBound twiceNatRealizer := polynomial_comp
   (linear_polynomial (linear_pair linear_id linear_id)) BinaryGcd.nat_add_polynomial
 theorem thriceNat_polynomial : PolyBound thriceNatRealizer := polynomial_comp
   (polynomial_pair twiceNat_polynomial (linear_polynomial linear_id)) BinaryGcd.nat_add_polynomial
 def loopSmall (s : FlowLoopState) : Bool := decide (maskCard s.2.2.1+maskCard s.2.2.1+maskCard s.2.2.1≤(weightedParse s.2.1).1+(weightedParse s.2.1).1)
 def loopSmallRealizer : Realizer loopSmall :=
   ((((loopW.comp maskCardRealizer).comp thriceNatRealizer).pair (loopOrder.comp twiceNatRealizer)).comp Realizer.le)
 theorem loopSmall_polynomial : PolyBound loopSmallRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (polynomial_comp (linear_polynomial loopW_linear) maskCard_polynomial) thriceNat_polynomial)
     (polynomial_comp loopOrder_polynomial twiceNat_polynomial)) nat_le_polynomial
 def freezeBalanced (s : FlowLoopState) : FlowLoopState := (true,(s.2.1,(s.2.2.1,(s.2.2.2.1,(false,[])))))
 def freezeBalancedRealizer : Realizer freezeBalanced :=
   (Realizer.constant true).pair (loopBase.pair (loopW.pair (loopS.pair ((Realizer.constant false).pair Realizer.nil))))
 theorem nilBits_polynomial {α : Type} [Coding α] : PolyBound (Realizer.nil : Realizer (fun _ : α => ([] : List Bool))) :=
   linear_polynomial (linear_of _ 3 (by omega) (fun _ => by change 2≤ _;omega) (fun _ => by simp;omega))
 theorem freezeBalanced_polynomial : PolyBound freezeBalancedRealizer := polynomial_pair
   (linear_polynomial (linear_constant true))
   (polynomial_pair (linear_polynomial loopBase_linear) (polynomial_pair (linear_polynomial loopW_linear)
     (polynomial_pair (linear_polynomial loopS_linear) (polynomial_pair (linear_polynomial (linear_constant false)) nilBits_polynomial))))
 def skipFlowCall (s : FlowLoopState) : List Bool := false::prefixBits (false::flowLoopBits s)
 def skipFlowCallRealizer : Realizer skipFlowCall :=
   ((Realizer.constant false).pair ((((Realizer.constant false).pair flowLoopBitsRealizer).comp Realizer.cons).comp prefixRealizer)).comp Realizer.cons
 theorem skipFlowCall_polynomial : PolyBound skipFlowCallRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_constant false))
     (polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial (linear_constant false)) flowLoopBits_polynomial)
       (linear_polynomial linear_cons)) prefix_polynomial)) (linear_polynomial linear_cons)
 def invokeFlowCall (s : FlowLoopState) : List Bool := true::(prefixBits (true::flowLoopBits s)++flowActivePayload s)
 def invokeFlowCallRealizer : Realizer invokeFlowCall :=
   ((Realizer.constant true).pair ((((((Realizer.constant true).pair flowLoopBitsRealizer).comp Realizer.cons).comp prefixRealizer).pair flowActivePayloadRealizer).comp appendBits)).comp Realizer.cons
 theorem invokeFlowCall_polynomial : PolyBound invokeFlowCallRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_constant true))
     (polynomial_comp (polynomial_pair (polynomial_comp (polynomial_comp
       (polynomial_pair (linear_polynomial (linear_constant true)) flowLoopBits_polynomial) (linear_polynomial linear_cons)) prefix_polynomial)
       flowActivePayload_polynomial) appendBits_polynomial)) (linear_polynomial linear_cons)
 def flowPrepare (s : FlowLoopState) : List Bool :=
   if s.1 then skipFlowCall s else if loopSmall s then skipFlowCall (freezeBalanced s) else invokeFlowCall s
 def flowPrepareRealizer : Realizer flowPrepare :=
   ((Realizer.fst.pair Realizer.id).comp
     (skipFlowCallRealizer.choose ((loopSmallRealizer.pair Realizer.id).comp
       ((freezeBalancedRealizer.comp skipFlowCallRealizer).choose invokeFlowCallRealizer)))).congr (fun s => rfl)
 theorem flowPrepare_polynomial : PolyBound flowPrepareRealizer := by
   unfold flowPrepareRealizer
   apply polynomial_congr
   exact polynomial_comp (linear_polynomial (linear_pair linear_fst linear_id))
     (polynomial_choose skipFlowCall_polynomial
       (polynomial_comp (polynomial_pair loopSmall_polynomial (linear_polynomial linear_id))
         (polynomial_choose (polynomial_comp freezeBalanced_polynomial skipFlowCall_polynomial) invokeFlowCall_polynomial)))
 def flowLoopPre (L : List Bool) : List Bool := flowPrepare (flowLoopParse L)
 def flowLoopPreRealizer : Realizer flowLoopPre := flowLoopParseRealizer.comp flowPrepareRealizer
 theorem flowLoopPre_polynomial : PolyBound flowLoopPreRealizer := polynomial_comp flowLoopParse_polynomial flowPrepare_polynomial
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowLoopPost
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def postMaskPair (s : FlowPostRaw) : List Bool×List Bool :=
   let n := (weightedParse s.1.2.1).1
   let owners := activeVertices n s.1.2.2.1
   let m := maskCard s.1.2.2.1
   (projectOwnerMask (n,(owners,(splitWord s.2.tail m).1)),
     projectOwnerMask (n,(owners,(splitWord (splitWord s.2.tail m).2 m).1)))
 def flowCutResponse (s : FlowPostRaw) : FlowLoopState := cutUpdate (s.1,orientMasks (postMaskPair s))
 def flowCutResponseRealizer : Realizer flowCutResponse := flowCutUpdateRealizer
 theorem flowCutResponse_polynomial : PolyBound flowCutResponseRealizer := flowCutUpdate_polynomial
 def freezeFlow (s : FlowPostRaw) : FlowLoopState := (true,(s.1.2.1,(s.1.2.2.1,(s.1.2.2.2.1,(true,s.2.tail)))))
 def freezeFlowRealizer : Realizer freezeFlow :=
   (Realizer.constant true).pair ((Realizer.fst.comp loopBase).pair ((Realizer.fst.comp loopW).pair
     ((Realizer.fst.comp loopS).pair ((Realizer.constant true).pair (Realizer.snd.comp BinaryAdder.tailBits)))))
 theorem freezeFlow_polynomial : PolyBound freezeFlowRealizer := polynomial_pair (linear_polynomial (linear_constant true))
   (polynomial_pair (linear_polynomial (linear_comp linear_fst loopBase_linear))
     (polynomial_pair (linear_polynomial (linear_comp linear_fst loopW_linear))
       (polynomial_pair (linear_polynomial (linear_comp linear_fst loopS_linear))
         (polynomial_pair (linear_polynomial (linear_constant true)) (linear_polynomial (linear_comp linear_snd BinaryAdder.tailBits_linear))))))
 def flowRespond (s : FlowPostRaw) : FlowLoopState := if s.2.headD false then flowCutResponse s else freezeFlow s
 def flowRespondRealizer : Realizer flowRespond :=
   (((Realizer.snd.comp BinaryAdder.headBit).pair Realizer.id).comp (flowCutResponseRealizer.choose freezeFlowRealizer)).congr (fun s => rfl)
 theorem flowRespond_polynomial : PolyBound flowRespondRealizer := by
   unfold flowRespondRealizer
   apply polynomial_congr
   exact polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd BinaryAdder.headBit_linear) linear_id))
     (polynomial_choose flowCutResponse_polynomial freezeFlow_polynomial)
 def flowRespondInput (s : List Bool×List Bool) : FlowPostRaw := (flowLoopParse s.1.tail,s.2)
 def flowRespondInputRealizer : Realizer flowRespondInput :=
   (((Realizer.fst.comp BinaryAdder.tailBits).comp flowLoopParseRealizer).pair Realizer.snd)
 theorem flowRespondInput_polynomial : PolyBound flowRespondInputRealizer := polynomial_pair
   (polynomial_comp (linear_polynomial (linear_comp linear_fst BinaryAdder.tailBits_linear)) flowLoopParse_polynomial) (linear_polynomial linear_snd)
 def flowPostBody (s : List Bool×List Bool) : List Bool :=
   if s.1.headD false then flowLoopBits (flowRespond (flowRespondInput s)) else s.1.tail
 def flowPostBodyRealizer : Realizer flowPostBody :=
   (((Realizer.fst.comp BinaryAdder.headBit).pair Realizer.id).comp
     (((flowRespondInputRealizer.comp flowRespondRealizer).comp flowLoopBitsRealizer).choose (Realizer.fst.comp BinaryAdder.tailBits))).congr (fun s => rfl)
 theorem flowPostBody_polynomial : PolyBound flowPostBodyRealizer := by
   unfold flowPostBodyRealizer
   apply polynomial_congr
   exact polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst BinaryAdder.headBit_linear) linear_id))
     (polynomial_choose (polynomial_comp (polynomial_comp flowRespondInput_polynomial flowRespond_polynomial) flowLoopBits_polynomial)
       (linear_polynomial (linear_comp linear_fst BinaryAdder.tailBits_linear)))
 def flowLoopPost (L : List Bool) : List Bool := flowPostBody (readWord L)
 def flowLoopPostRealizer : Realizer flowLoopPost := readWordRealizer.comp flowPostBodyRealizer
 theorem flowLoopPost_polynomial : PolyBound flowLoopPostRealizer := polynomial_comp readWord_polynomial flowPostBody_polynomial
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowNormalizeCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def liftedVertexBits (s : List Bool×List ℕ) : List Bool :=
   encodeNat ((s.2.drop (cappedValue s.1 s.2.length)).headD 0)
 def liftedIndex : Realizer (fun s : List Bool×List ℕ => cappedValue s.1 s.2.length) := (Realizer.fst.pair (Realizer.snd.comp listLength)).comp cappedValueRealizer
 theorem liftedIndex_polynomial : PolyBound (liftedIndex : Realizer (fun s : List Bool×List ℕ => cappedValue s.1 s.2.length)) :=
   polynomial_comp (polynomial_pair (linear_polynomial linear_fst) (polynomial_comp (linear_polynomial linear_snd) listLength_polynomial)) cappedValue_polynomial
 def liftedVertexBitsRealizer : Realizer liftedVertexBits :=
   ((Realizer.snd.pair liftedIndex).comp lookupNat).comp naturalCodeRealizer
 theorem liftedVertexBits_polynomial : PolyBound liftedVertexBitsRealizer := polynomial_comp
   (polynomial_comp (polynomial_pair (linear_polynomial linear_snd) liftedIndex_polynomial) lookupNat_polynomial) naturalCode_polynomial
 def liftedPathBits (s : List (List Bool)×List ℕ) : List Bool :=
   encodeNat s.1.length++(s.1.flatMap (fun v => liftedVertexBits (v,s.2)))
 def liftedPathBitsRealizer : Realizer liftedPathBits :=
   (((Realizer.fst.comp listLength).comp naturalCodeRealizer).pair
     ((mapEnvironment liftedVertexBitsRealizer).comp flattenList)).comp appendBits
 theorem liftedPathBits_polynomial : PolyBound liftedPathBitsRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) listLength_polynomial) naturalCode_polynomial)
     (polynomial_comp (polynomial_mapEnvironment liftedVertexBits_polynomial) flattenList_polynomial)) appendBits_polynomial
 def normalizingSquare : Realizer (fun xs : List ℕ => multiply (natBits xs.length) (natBits xs.length)) :=
   (((listLength.comp naturalWordRealizer).pair (listLength.comp naturalWordRealizer)).comp multiplyRealizer)
 theorem normalizingSquare_polynomial : PolyBound normalizingSquare := polynomial_comp
   (polynomial_pair (polynomial_comp listLength_polynomial naturalWord_polynomial)
     (polynomial_comp listLength_polynomial naturalWord_polynomial)) multiply_polynomial
 def normalizedWeight (s : SignedWords×List ℕ) : SignedWords :=
   (s.1.1,(s.1.2.1,multiply s.1.2.2 (multiply (natBits s.2.length) (natBits s.2.length))))
 def normalizedWeightRealizer : Realizer normalizedWeight :=
   (Realizer.fst.comp Realizer.fst).pair (((Realizer.fst.comp Realizer.snd).comp Realizer.fst).pair
     (((((Realizer.fst.comp Realizer.snd).comp Realizer.snd).pair (Realizer.snd.comp normalizingSquare))).comp multiplyRealizer))
 theorem normalizedWeight_polynomial : PolyBound normalizedWeightRealizer := polynomial_pair
   (linear_polynomial (linear_comp linear_fst linear_fst))
   (polynomial_pair (linear_polynomial (linear_comp (linear_comp linear_fst linear_snd) linear_fst))
     (polynomial_comp (polynomial_pair (linear_polynomial (linear_comp (linear_comp linear_fst linear_snd) linear_snd))
       (polynomial_comp (linear_polynomial linear_snd) normalizingSquare_polynomial)) multiply_polynomial))
 def normalizedEntryBits (s : RawPathEntry×List ℕ) : List Bool :=
   liftedPathBits (s.1.1,s.2)++rationalBits (normalizedWeight (s.1.2,s.2))
 def normalizedEntryBitsRealizer : Realizer normalizedEntryBits :=
   (((((Realizer.fst.comp Realizer.fst).pair Realizer.snd).comp liftedPathBitsRealizer)).pair
     (((((Realizer.fst.comp Realizer.snd).pair Realizer.snd).comp normalizedWeightRealizer)).comp rationalBitsRealizer)).comp appendBits
 theorem normalizedEntryBits_polynomial : PolyBound normalizedEntryBitsRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst linear_fst) linear_snd)) liftedPathBits_polynomial)
     (polynomial_comp (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst linear_snd) linear_snd)) normalizedWeight_polynomial) rationalBits_polynomial)) appendBits_polynomial
 def normalizedSparseBits (s : List RawPathEntry×List ℕ) : List Bool :=
   encodeNat s.1.length++s.1.flatMap (fun e => normalizedEntryBits (e,s.2))
 def normalizedSparseBitsRealizer : Realizer normalizedSparseBits :=
   (((Realizer.fst.comp listLength).comp naturalCodeRealizer).pair
     ((mapEnvironment normalizedEntryBitsRealizer).comp flattenList)).comp appendBits
 theorem normalizedSparseBits_polynomial : PolyBound normalizedSparseBitsRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) listLength_polynomial) naturalCode_polynomial)
     (polynomial_comp (polynomial_mapEnvironment normalizedEntryBits_polynomial) flattenList_polynomial)) appendBits_polynomial
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PathMass
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PathMass

 theorem vertexMass_cons {n : ℕ} (e : List (Fin n) × ℝ) (f : List (List (Fin n) × ℝ)) (v : Fin n) :
    vertexMass (e::f) v = (if v∈e.1 then e.2 else 0)+vertexMass f v := by
  by_cases hv : v∈e.1 <;> simp [vertexMass,hv]

 theorem endpointMass_cons {n : ℕ} (e : List (Fin n) × ℝ) (f : List (List (Fin n) × ℝ)) (u v : Fin n) :
    endpointMass (e::f) u v = (if HasEndpoints e.1 u v then e.2 else 0)+endpointMass f u v := by
  by_cases hv : HasEndpoints e.1 u v <;> simp [endpointMass,hv]

 theorem sum_indicator {n : ℕ} (W : Finset (Fin n)) (p : List (Fin n)) (hp : p.Nodup)
    (hW : ∀ v∈p,v∈W) (w : ℝ) :
    (∑ v∈W,if v∈p then w else 0) = (p.length:ℝ)*w := by
  have heq : W.filter (fun v => v∈p)=p.toFinset := by
    ext v
    simp only [Finset.mem_filter,List.mem_toFinset]
    exact ⟨fun h => h.2,fun h => ⟨hW v h,h⟩⟩
  rw [←Finset.sum_filter,heq]
  simp only [Finset.sum_const,List.toFinset_card_of_nodup hp, nsmul_eq_mul]

 theorem length_identity {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (f : List (List (Fin n) × ℝ)) (hf : SparseValid G W f) :
    (f.map (fun e => e.2*(e.1.length:ℝ))).sum = ∑ v∈W,vertexMass f v := by
  induction f with
  | nil => simp [vertexMass]
  | cons e f ih =>
    have he := hf e (by simp)
    have hrest : SparseValid G W f := by intro x hx; exact hf x (by simp [hx])
    simp only [List.map_cons,List.sum_cons,vertexMass_cons,Finset.sum_add_distrib]
    rw [←ih hrest,sum_indicator W e.1 he.2.2.1 he.2.2.2.1 e.2]
    ring

 theorem expected_length_bound {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ)
    (ell : ℝ) (W : Finset (Fin n)) (f : List (List (Fin n) × ℝ))
    (hell : 0 ≤ ell) (hx : ∀ v,0 ≤ x v) (hk : 0 < vertexSum x Finset.univ)
    (hf : PathOutcome G x ell W f) :
    (f.map (fun e => e.2*(e.1.length:ℝ))).sum ≤ ell := by
  rw [length_identity G W f hf.2.1]
  have hsub : (∑ v∈W,x v) ≤ vertexSum x Finset.univ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => hx v)
  calc
    _ ≤ ∑ v∈W,ell*x v/vertexSum x Finset.univ := Finset.sum_le_sum (fun v hv => hf.2.2.2.2 v hv)
    _ = (ell/vertexSum x Finset.univ)*(∑ v∈W,x v) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ ≤ (ell/vertexSum x Finset.univ)*vertexSum x Finset.univ :=
      mul_le_mul_of_nonneg_left hsub (div_nonneg hell hk.le)
    _ = ell := div_mul_cancel₀ _ hk.ne'

end EdgeSublinearMWIS.Main.PathMass
end

-- Solutions.PathKernelAverage
noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace EdgeSublinearMWIS.Main.PathMass

 theorem endpoints_exist {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (p : List (Fin n)) (hp : SimplePath G W p) :
    ∃ u v : W,HasEndpoints p u.val v.val := by
  let u : W := ⟨p.head hp.1,hp.2.2.1 _ (List.head_mem hp.1)⟩
  let v : W := ⟨p.getLast hp.1,hp.2.2.1 _ (List.getLast_mem hp.1)⟩
  exact ⟨u,v,List.head?_eq_some_head hp.1,List.getLast?_eq_some_getLast hp.1⟩


end EdgeSublinearMWIS.Main.PathMass
end

-- Solutions.FlowMass
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.FlowLaw
open PathMass

 theorem endpoints_unique {n : ℕ} (p : List (Fin n)) (u v a b : Fin n) (hp : HasEndpoints p a b) :
     HasEndpoints p u v ↔ u=a ∧ v=b := by
   constructor
   · intro h
     exact ⟨Option.some.inj (h.1.symm.trans hp.1),Option.some.inj (h.2.symm.trans hp.2)⟩
   · rintro ⟨rfl,rfl⟩
     exact hp
 theorem endpoint_total {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
     (f : List (List (Fin n)×ℝ)) (hf : SparseValid G W f) :
     (∑u∈W,∑v∈W,endpointMass f u v)=(f.map Prod.snd).sum := by
   induction f with
   | nil => simp [endpointMass]
   | cons e f ih =>
     have he := hf e (by simp)
     have hrest : SparseValid G W f := by intro a ha; exact hf a (List.mem_cons_of_mem e ha)
     obtain ⟨a,b,hp⟩ := endpoints_exist G W e.1 he.2
     have hrow (u : Fin n) : (∑v∈W,if HasEndpoints e.1 u v then e.2 else 0)=if u=a.val then e.2 else 0 := by
       simp_rw [endpoints_unique e.1 u _ a.val b.val hp]
       by_cases hu : u=a.val <;> simp [hu,b.property]
     simp only [List.map_cons,List.sum_cons,endpointMass_cons,Finset.sum_add_distrib]
     rw [ih hrest]
     simp only [hrow,Finset.sum_ite_eq',a.property,if_true]
 theorem unit_total {n : ℕ} (G : SimpleGraph (Fin n)) (f : List (List (Fin n)×ℚ)) (hf : UnitFlow G f) :
     ((realPaths f).map Prod.snd).sum=(n:ℝ)^2 := by
   rw [← endpoint_total G Finset.univ (realPaths f) hf.1]
   simp only [hf.2,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
   ring
 def scale {n : ℕ} (f : List (List (Fin n)×ℝ)) (q : ℝ) : List (List (Fin n)×ℝ) :=
   f.map (fun e => (e.1,e.2/q))
 theorem scale_valid {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (f : List (List (Fin n)×ℝ))
     (q : ℝ) (hq : 0≤ q) (hf : SparseValid G W f) : SparseValid G W (scale f q) := by
   intro e he
   obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
   exact ⟨div_nonneg (hf a ha).1 hq,(hf a ha).2⟩
 theorem scale_total {n : ℕ} (f : List (List (Fin n)×ℝ)) (q : ℝ) :
     ((scale f q).map Prod.snd).sum=(f.map Prod.snd).sum/q := by
   induction f with
   | nil => simp [scale]
   | cons e f ih =>
     simp only [scale,List.map_cons,List.sum_cons] at ih ⊢
     rw [ih,add_div]
 theorem scale_endpoint {n : ℕ} (f : List (List (Fin n)×ℝ)) (q : ℝ) (u v : Fin n) :
     endpointMass (scale f q) u v=endpointMass f u v/q := by
   induction f with
   | nil => simp [scale,endpointMass]
   | cons e f ih =>
     change endpointMass ((e.1,e.2/q)::scale f q) u v=endpointMass (e::f) u v/q
     rw [endpointMass_cons,endpointMass_cons,ih]
     by_cases h : HasEndpoints e.1 u v <;> simp [h,add_div]
 theorem scale_vertex {n : ℕ} (f : List (List (Fin n)×ℝ)) (q : ℝ) (v : Fin n) :
     vertexMass (scale f q) v=vertexMass f v/q := by
   induction f with
   | nil => simp [scale,vertexMass]
   | cons e f ih =>
     change vertexMass ((e.1,e.2/q)::scale f q) v=vertexMass (e::f) v/q
     rw [vertexMass_cons,vertexMass_cons,ih]
     by_cases h : v∈e.1 <;> simp [h,add_div]
end EdgeSublinearMWIS.Main.FlowLaw
end

-- Solutions.FlowLift
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.FlowLaw
open ActiveTransport PathMass

 def liftPaths {m n : ℕ} (f : Fin m ↪ Fin n) (ps : List (List (Fin m)×ℝ)) : List (List (Fin n)×ℝ) :=
   ps.map (fun e => (e.1.map f,e.2))
 theorem lift_simple {m n : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)) (f : Fin m ↪ Fin n)
     (W : Finset (Fin n)) (hW : Finset.univ.image f=W) (hAdj : ∀u v,H.Adj u v↔G.Adj (f u) (f v))
     (p : List (Fin m)) (hp : SimplePath H Finset.univ p) : SimplePath G W (p.map f) := by
   refine ⟨by simpa using hp.1,hp.2.1.map f.injective,?_,?_⟩
   · intro v hv
     obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
     rw [← hW]
     exact Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩
   · rw [List.isChain_map]
     exact hp.2.2.2.imp (fun u v h => (hAdj u v).mp h)
 theorem lift_valid {m n : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)) (f : Fin m ↪ Fin n)
     (W : Finset (Fin n)) (hW : Finset.univ.image f=W) (hAdj : ∀u v,H.Adj u v↔G.Adj (f u) (f v))
     (ps : List (List (Fin m)×ℝ)) (hp : SparseValid H Finset.univ ps) : SparseValid G W (liftPaths f ps) := by
   intro e he
   obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
   exact ⟨(hp a ha).1,lift_simple G H f W hW hAdj a.1 (hp a ha).2⟩
 theorem option_map_embedding {α β : Type} (f : α ↪ β) (o : Option α) (a : α) :
     o.map f=some (f a) ↔ o=some a := by
   cases o <;> simp [f.injective.eq_iff]
 theorem lift_endpoints {m n : ℕ} (f : Fin m ↪ Fin n) (p : List (Fin m)) (u v : Fin m) :
     HasEndpoints (p.map f) (f u) (f v) ↔ HasEndpoints p u v := by
   unfold HasEndpoints
   rw [List.head?_map,List.getLast?_map,option_map_embedding,option_map_embedding]
 theorem lift_endpointMass {m n : ℕ} (f : Fin m ↪ Fin n) (ps : List (List (Fin m)×ℝ)) (u v : Fin m) :
     endpointMass (liftPaths f ps) (f u) (f v)=endpointMass ps u v := by
   induction ps with
   | nil => simp [liftPaths,endpointMass]
   | cons e ps ih =>
     change endpointMass ((e.1.map f,e.2)::liftPaths f ps) (f u) (f v)=endpointMass (e::ps) u v
     rw [endpointMass_cons,endpointMass_cons,lift_endpoints,ih]
 theorem lift_vertexMass {m n : ℕ} (f : Fin m ↪ Fin n) (ps : List (List (Fin m)×ℝ)) (v : Fin m) :
     vertexMass (liftPaths f ps) (f v)=vertexMass ps v := by
   induction ps with
   | nil => simp [liftPaths,vertexMass]
   | cons e ps ih =>
     change vertexMass ((e.1.map f,e.2)::liftPaths f ps) (f v)=vertexMass (e::ps) v
     rw [vertexMass_cons,vertexMass_cons,ih]
     have hm : f v∈e.1.map f ↔ v∈e.1 := by simp [f.injective.eq_iff]
     simp only [hm]
 theorem lift_total {m n : ℕ} (f : Fin m ↪ Fin n) (ps : List (List (Fin m)×ℝ)) :
     ((liftPaths f ps).map Prod.snd).sum=(ps.map Prod.snd).sum := by
   simp only [liftPaths,List.map_map,Function.comp_def]
 def normalizeLift {m n : ℕ} (f : Fin m ↪ Fin n) (ps : List (List (Fin m)×ℚ)) : List (List (Fin n)×ℚ) :=
   ps.map (fun e => (e.1.map f,e.2/(m:ℚ)^2))
 theorem normalizeLift_real {m n : ℕ} (f : Fin m ↪ Fin n) (ps : List (List (Fin m)×ℚ)) :
     realPaths (normalizeLift f ps)=liftPaths f (scale (realPaths ps) ((m:ℝ)^2)) := by
   simp only [realPaths,normalizeLift,liftPaths,scale,List.map_map,Function.comp_def]
   apply List.map_congr_left
   intro e he
   simp only [Rat.cast_div,Rat.cast_pow,Rat.cast_natCast]
end EdgeSublinearMWIS.Main.FlowLaw
end

-- Solutions.FlowNormalizeMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ActiveTransport

 theorem liftedVertexBits_correct {n : ℕ} (W : Finset (Fin n)) (i : Fin W.card) :
     liftedVertexBits (natBits i.val,activeVertices n (mask W))=encodeNat (activeMap W i).val := by
   have hl : (activeVertices n (mask W)).length=W.card := by rw [activeVertices_mask];simp
   unfold liftedVertexBits
   rw [cappedValue_eq,value_natBits,hl,Nat.min_eq_right i.isLt.le,activeVertices_lookup]
 theorem liftedPathBits_correct {n : ℕ} (W : Finset (Fin n)) (p : List (Fin W.card)) :
     liftedPathBits (rawPathWords p,activeVertices n (mask W))=encodePath (p.map (activeMap W)) := by
   simp only [liftedPathBits,rawPathWords,List.length_map,List.flatMap_map,liftedVertexBits_correct,encodePath]
 theorem normalizedWeight_bits {n : ℕ} (W : Finset (Fin n)) (q : ℚ) (hW : 0< W.card) :
     rationalBits (normalizedWeight (codeWords (ratCode q),activeVertices n (mask W)))=encodeRat (q/(W.card:ℚ)^2) := by
   have hl : (activeVertices n (mask W)).length=W.card := by rw [activeVertices_mask];simp
   have hd : 0< value (multiply (natBits q.den) (multiply (natBits W.card) (natBits W.card))) := by
     rw [multiply_value,multiply_value,value_natBits,value_natBits]
     exact Nat.mul_pos q.den_pos (Nat.mul_pos hW hW)
   dsimp only [normalizedWeight,codeWords,ratCode]
   rw [hl,rationalBits_correct _ _ _ hd,signedValue_encode,multiply_value,multiply_value,value_natBits,value_natBits]
   congr 1
   push_cast
   conv_rhs => rw [← Rat.num_div_den q]
   ring
 theorem normalizedEntryBits_correct {n : ℕ} (W : Finset (Fin n)) (e : List (Fin W.card)×ℚ) (hW : 0< W.card) :
     normalizedEntryBits (rawPathEntry e,activeVertices n (mask W))=
       encodePath (e.1.map (activeMap W))++encodeRat (e.2/(W.card:ℚ)^2) := by
   simp only [normalizedEntryBits,rawPathEntry,liftedPathBits_correct,normalizedWeight_bits W e.2 hW]
 theorem normalizedSparseBits_correct {n : ℕ} (W : Finset (Fin n)) (f : List (List (Fin W.card)×ℚ)) (hW : 0< W.card) :
     normalizedSparseBits (f.map rawPathEntry,activeVertices n (mask W))=
       encodeSparsePaths (FlowLaw.normalizeLift (activeMap W) f) := by
   simp only [normalizedSparseBits,List.length_map,List.flatMap_map,normalizedEntryBits_correct W _ hW,
     encodeSparsePaths,FlowLaw.normalizeLift]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowActiveMath
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ActiveTransport

 def inducedCodes {n : ℕ} (W : Finset (Fin n)) (x : Fin n → RationalCode) : Fin W.card → RationalCode := fun i => x (activeMap W i)
 theorem inducedRationalData {n : ℕ} (W : Finset (Fin n)) (x : Fin n → RationalCode) (gamma : RationalCode) :
     rationalData (inducedCodes W x) gamma=(W.sort (·≤·)).flatMap (fun v => (x v).bits)++gamma.bits := by
   unfold rationalData
   rw [← W.listMap_orderEmbOfFin_finRange rfl,List.flatMap_map]
   simp only [List.finRange,List.flatMap_def,List.map_ofFn,Function.comp_def,inducedCodes,activeMap]
   rfl
 theorem flowActivePayload_correct {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode)
     (ell : ℕ) (done : Bool) (W S : Finset (Fin n)) (flag : Bool) (payload : List Bool)
     (hx : ∀v,0≤(x v).value) (hk : 0<∑v,(x v).value) :
     flowActivePayload (done,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(flag,payload)))))=
       flowInput (activeGraph G W) (inducedCodes W x) (ratCode ((ell:ℚ)*(n:ℚ)^2/(3*∑v,(x v).value))) := by
   have hMask : maskSelect ((List.ofFn x).map codeWords,mask W)=(W.sort (·≤·)).map (fun v => codeWords (x v)) := by
     rw [List.map_ofFn]
     exact maskSelect_correct W (fun v => codeWords (x v))
   dsimp only [flowActivePayload]
   rw [weightedParse_flow_append,activeGraph_correct,hMask,flowGamma_correct G x δ ell hx hk]
   unfold flowInput
   rw [inducedRationalData]
   simp only [List.flatMap_map,rawRationalBits_code,ratCode_bits,List.append_assoc]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowLoopFinish
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ActiveTransport

 def flowFinishLaw (s : FlowLoopState) : List Bool :=
   true::(s.2.2.1++normalizedSparseBits (readSparsePaths s.2.2.2.2.2,activeVertices (weightedParse s.2.1).1 s.2.2.1))
 def flowFinishLawRealizer : Realizer flowFinishLaw :=
   ((Realizer.constant true).pair ((loopW.pair
     (((((loopResult.comp Realizer.snd).comp readSparsePathsRealizer).pair loopOwners).comp normalizedSparseBitsRealizer))).comp appendBits)).comp Realizer.cons
 theorem flowFinishLaw_polynomial : PolyBound flowFinishLawRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_constant true))
     (polynomial_comp (polynomial_pair (linear_polynomial loopW_linear)
       (polynomial_comp (polynomial_pair (polynomial_comp (polynomial_comp (linear_polynomial loopResult_linear)
         (linear_polynomial linear_snd)) readSparsePaths_polynomial) loopOwners_polynomial) normalizedSparseBits_polynomial)) appendBits_polynomial))
   (linear_polynomial linear_cons)
 def flowFinishBalanced (s : FlowLoopState) : List Bool := false::s.2.2.2.1
 def flowFinishBalancedRealizer : Realizer flowFinishBalanced := ((Realizer.constant false).pair loopS).comp Realizer.cons
 theorem flowFinishBalanced_polynomial : PolyBound flowFinishBalancedRealizer := polynomial_comp
   (linear_polynomial (linear_pair (linear_constant false) loopS_linear)) (linear_polynomial linear_cons)
 def flowFinish (s : FlowLoopState) : List Bool := if s.2.2.2.2.1 then flowFinishLaw s else flowFinishBalanced s
 def flowFinishRealizer : Realizer flowFinish :=
   (((loopResult.comp Realizer.fst).pair Realizer.id).comp (flowFinishLawRealizer.choose flowFinishBalancedRealizer)).congr (fun s => rfl)
 theorem flowFinish_polynomial : PolyBound flowFinishRealizer := by
   unfold flowFinishRealizer
   apply polynomial_congr
   exact polynomial_comp (linear_polynomial (linear_pair (linear_comp loopResult_linear linear_fst) linear_id))
     (polynomial_choose flowFinishLaw_polynomial flowFinishBalanced_polynomial)
 def flowFinishBits (L : List Bool) : List Bool := flowFinish (flowLoopParse L)
 def flowFinishBitsRealizer : Realizer flowFinishBits := flowLoopParseRealizer.comp flowFinishRealizer
 theorem flowFinishBits_polynomial : PolyBound flowFinishBitsRealizer := polynomial_comp flowLoopParse_polynomial flowFinish_polynomial
 theorem flowFinishBits_balanced {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode)
     (ell : ℕ) (done : Bool) (W S : Finset (Fin n)) (payload : List Bool) :
     flowFinishBits (flowLoopBits (done,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(false,payload))))))=false::mask S := by
   unfold flowFinishBits
   rw [flowLoopParse_bits done _ _ _ false payload n (readNatural_flowInput G x δ ell) (by simp [mask]) (by simp [mask])]
   rfl
 theorem flowFinishBits_law {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode)
     (ell : ℕ) (done : Bool) (W S : Finset (Fin n)) (f : List (List (Fin W.card)×ℚ)) (hW : 0< W.card) :
     flowFinishBits (flowLoopBits (done,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(true,encodeSparsePaths f))))))=
       true::(mask W++encodeSparsePaths (FlowLaw.normalizeLift (activeMap W) f)) := by
   unfold flowFinishBits
   rw [flowLoopParse_bits done _ _ _ true _ n (readNatural_flowInput G x δ ell) (by simp [mask]) (by simp [mask])]
   dsimp only [flowFinish,flowFinishLaw]
   simp only [if_true,readSparsePaths_correct,weightedParse_flow_append,normalizedSparseBits_correct W f hW]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowLoopInitialize
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def flowOriginalOrder : Realizer (fun L : List Bool => (weightedParse L).1) := weightedParseRealizer.comp Realizer.fst
 theorem flowOriginalOrder_polynomial : PolyBound flowOriginalOrder := polynomial_comp weightedParse_polynomial (linear_polynomial linear_fst)
 def initialTrueMask := (flowOriginalOrder.pair (Realizer.constant true)).comp replicateList
 def initialFalseMask := (flowOriginalOrder.pair (Realizer.constant false)).comp replicateList
 theorem initialTrueMask_polynomial : PolyBound initialTrueMask := polynomial_comp
   (polynomial_pair flowOriginalOrder_polynomial (linear_polynomial (linear_constant true))) replicateList_polynomial
 theorem initialFalseMask_polynomial : PolyBound initialFalseMask := polynomial_comp
   (polynomial_pair flowOriginalOrder_polynomial (linear_polynomial (linear_constant false))) replicateList_polynomial
 def flowInitialRecord (L : List Bool) : FlowLoopState :=
   (false,(L,(List.replicate (weightedParse L).1 true,(List.replicate (weightedParse L).1 false,(false,[])))))
 def flowInitialRecordRealizer : Realizer flowInitialRecord :=
   (Realizer.constant false).pair (Realizer.id.pair (initialTrueMask.pair (initialFalseMask.pair ((Realizer.constant false).pair Realizer.nil))))
 theorem flowInitialRecord_polynomial : PolyBound flowInitialRecordRealizer := polynomial_pair
   (linear_polynomial (linear_constant false))
   (polynomial_pair (linear_polynomial linear_id) (polynomial_pair initialTrueMask_polynomial
     (polynomial_pair initialFalseMask_polynomial (polynomial_pair (linear_polynomial (linear_constant false)) nilBits_polynomial))))
 def flowInitialBits (L : List Bool) : List Bool := flowLoopBits (flowInitialRecord L)
 def flowInitialBitsRealizer : Realizer flowInitialBits := flowInitialRecordRealizer.comp flowLoopBitsRealizer
 theorem flowInitialBits_polynomial : PolyBound flowInitialBitsRealizer := polynomial_comp flowInitialRecord_polynomial flowLoopBits_polynomial
 def flowInitialInput (L : List Bool) : List Bool := List.replicate (weightedParse L).1 true++false::flowInitialBits L
 def flowInitialInputRealizer : Realizer flowInitialInput :=
   (initialTrueMask.pair (((Realizer.constant false).pair flowInitialBitsRealizer).comp Realizer.cons)).comp appendBits
 theorem flowInitialInput_polynomial : PolyBound flowInitialInputRealizer := polynomial_comp
   (polynomial_pair initialTrueMask_polynomial (polynomial_comp (polynomial_pair (linear_polynomial (linear_constant false)) flowInitialBits_polynomial)
     (linear_polynomial linear_cons))) appendBits_polynomial
 theorem mask_univ {n : ℕ} : mask (Finset.univ : Finset (Fin n))=List.replicate n true := by simp [mask]
 theorem mask_empty {n : ℕ} : mask (∅ : Finset (Fin n))=List.replicate n false := by simp [mask]
 theorem flowInitialRecord_correct {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode) (ell : ℕ) :
     flowInitialRecord (flowInput G x δ++encodeNat ell)=
       (false,(flowInput G x δ++encodeNat ell,(mask (Finset.univ : Finset (Fin n)),(mask (∅ : Finset (Fin n)),(false,[]))))) := by
   simp only [flowInitialRecord,weightedParse_flow_append,mask_univ,mask_empty]
 theorem flowInitialInput_correct {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode) (ell : ℕ) :
     flowInitialInput (flowInput G x δ++encodeNat ell)=List.replicate n true++false::flowInitialBits (flowInput G x δ++encodeNat ell) := by
   simp only [flowInitialInput,weightedParse_flow_append]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowActiveSize
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem flow_base_order_bound {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode) (ell : ℕ) :
     n≤(flowInput G x δ++encodeNat ell).length+1 := by
   have hh := graph_order_bound G
   simp only [flowInput,List.length_append]
   omega
 theorem flow_active_size : ∃A q : ℕ,0< A ∧ 0< q ∧
     ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode) (ell : ℕ)
       (done flag : Bool) (W S : Finset (Fin n)) (payload : List Bool),
       (flowActivePayload (done,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(flag,payload)))))).length+1≤
         A*((flowInput G x δ++encodeNat ell).length+1)^q := by
   obtain ⟨C,q,hC,hR⟩ := flowActivePayload_polynomial
   refine ⟨C*100^q+1,q+1,by positivity,by omega,?_⟩
   intro n G x δ ell done flag W S payload
   let base := flowInput G x δ++encodeNat ell
   let s : FlowLoopState := (false,(base,(mask W,([],(false,[])))))
   let z := base.length+1
   have hz : 1≤ z := by dsimp [z];omega
   have hn : n≤ base.length+1 := flow_base_order_bound G x δ ell
   have hbase := BinaryAdder.volume_bits base
   have hmask := BinaryAdder.volume_bits (mask W)
   have hlen : (mask W).length=n := by simp [mask]
   have hvol : volume s+1≤100*z := by
     dsimp only [s]
     simp only [volume_pair,volume_bool_false,volume_nil]
     dsimp only [z]
     omega
   have hv := (hR s).2
   have hh := Nat.pow_le_pow_left hvol q
   rw [mul_pow] at hh
   have hh := hv.trans (Nat.mul_le_mul_left C hh)
   have hq : z^q≤ z^(q+1) := Nat.pow_le_pow_right hz (by omega)
   have hh := hh.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (C*100^q) hq)
   have hp : 1≤ z^(q+1) := one_le_pow₀ hz
   have hout := bits_length_volume (flowActivePayload s)
   change (flowActivePayload s).length+1≤(C*100^q+1)*z^(q+1)
   nlinarith only [hh,hp,hout]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowRecordSize
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
 theorem flowLoopBits_length (done : Bool) (base W S : List Bool) (flag : Bool) (payload : List Bool) :
     (flowLoopBits (done,(base,(W,(S,(flag,payload)))))).length=2*base.length+W.length+S.length+3+payload.length := by
   simp only [flowLoopBits,List.length_cons,List.length_append,prefixBits,List.length_replicate]
   omega
 theorem freezeBalanced_length (s : FlowLoopState) : (flowLoopBits (freezeBalanced s)).length≤(flowLoopBits s).length := by
   rcases s with ⟨done,base,W,S,flag,payload⟩
   simp only [freezeBalanced,flowLoopBits_length,List.length_nil]
   omega
 theorem flow_record_size {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode)
     (ell : ℕ) (done : Bool) (W S : Finset (Fin n)) (flag : Bool) (payload : List Bool) :
     (flowLoopBits (done,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(flag,payload)))))).length≤
       4*((flowInput G x δ++encodeNat ell).length+1)+5+payload.length := by
   have hn := flow_base_order_bound G x δ ell
   have hw : (mask W).length=n := by simp [mask]
   have hs : (mask S).length=n := by simp [mask]
   rw [flowLoopBits_length,hw,hs]
   omega
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowCutMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ActiveTransport

 theorem orientMasks_correct {n : ℕ} (A B : Finset (Fin n)) :
     orientMasks (mask A,mask B)=if B.card≤ A.card then (mask A,mask B) else (mask B,mask A) := by
   simp only [orientMasks,maskCard_correct]
 theorem cutUpdate_correct {n : ℕ} (base : List Bool) (done flag : Bool) (W S A B : Finset (Fin n)) (payload : List Bool) :
     cutUpdate ((done,(base,(mask W,(mask S,(flag,payload))))),(mask A,mask B))=
       (false,(base,(mask (A\B),(mask (S∪(A∩B)),(false,[]))))) := by
   simp only [cutUpdate,maskDiff_correct,maskInter_correct,maskUnion_correct]
 theorem postMaskPair_correct {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode)
     (ell : ℕ) (done flag : Bool) (W S : Finset (Fin n)) (payload : List Bool) (A B : Finset (Fin W.card)) :
     postMaskPair ((done,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(flag,payload))))),true::(mask A++mask B))=
       (mask (A.image (activeMap W)),mask (B.image (activeMap W))) := by
   have hA : (mask A).length=W.card := by simp [mask]
   have hB : (mask B).length=W.card := by simp [mask]
   have ha : splitWord (mask A++mask B) W.card=(mask A,mask B) := by
     simpa only [hA] using (show splitWord (mask A++mask B) (mask A).length=(mask A,mask B) from by simp [splitWord])
   have hb : splitWord (mask B) W.card=(mask B,[]) := by
     simpa only [hB,List.append_nil] using (show splitWord (mask B++[]) (mask B).length=(mask B,[]) from by simp [splitWord])
   dsimp only [postMaskPair]
   rw [weightedParse_flow_append,maskCard_correct]
   simp only [List.tail_cons,ha,hb]
   congr 1
   · simpa only [List.append_nil] using projectOwnerMask_correct W A []
   · simpa only [List.append_nil] using projectOwnerMask_correct W B []
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowCutResult
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ActiveTransport SeparationTransport ComponentRefinement

 def orientedImages {n : ℕ} (W : Finset (Fin n)) (A B : Finset (Fin W.card)) : Finset (Fin n)×Finset (Fin n) :=
   if B.card≤ A.card then (A.image (activeMap W),B.image (activeMap W)) else (B.image (activeMap W),A.image (activeMap W))
 theorem orientedImages_card {n : ℕ} (W : Finset (Fin n)) (A B : Finset (Fin W.card)) :
     (orientedImages W A B).2.card≤(orientedImages W A B).1.card := by
   unfold orientedImages
   split_ifs with h
   · simpa only [Finset.card_image_of_injective _ (activeMap W).injective] using h
   · have hh : A.card≤ B.card := by omega
     simpa only [Finset.card_image_of_injective _ (activeMap W).injective] using hh
 theorem orientedImages_inside {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
     (A B : Finset (Fin W.card)) (hsep : Separation (activeGraph G W) A B) :
     Inside G W (orientedImages W A B).1 (orientedImages W A B).2 := by
   have hh := lift_inside G (activeGraph G W) (activeMap W) W (activeMap_image W) (fun _ _ => Iff.rfl) A B hsep
   unfold orientedImages
   split_ifs
   · exact hh
   · exact inside_swap G W _ _ hh
 theorem image_vertexSum {n m : ℕ} (f : Fin m ↪ Fin n) (A : Finset (Fin m)) (x : Fin n → ℝ) :
     vertexSum x (A.image f)=vertexSum (fun v => x (f v)) A := by
   exact Finset.sum_image (fun u hu v hv huv => f.injective huv)
 theorem orientedImages_charge {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
     (A B : Finset (Fin W.card)) (x : Fin n → ℝ) (K gamma : ℝ)
     (hcut : vertexSum (fun v => x (activeMap W v)) (A∩B)≤ K*A.card*B.card*logTwo W.card/gamma) :
     vertexSum x ((orientedImages W A B).1∩(orientedImages W A B).2)≤
       K*(orientedImages W A B).1.card*(orientedImages W A B).2.card*logTwo W.card/gamma := by
   unfold orientedImages
   split_ifs
   · simp only [Finset.card_image_of_injective _ (activeMap W).injective]
     rw [← image_inter,image_vertexSum]
     exact hcut
   · simp only [Finset.card_image_of_injective _ (activeMap W).injective]
     rw [Finset.inter_comm,← image_inter,image_vertexSum]
     convert hcut using 1 <;> ring
 theorem flowCutResponse_correct {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode)
     (ell : ℕ) (done flag : Bool) (W S : Finset (Fin n)) (payload : List Bool) (A B : Finset (Fin W.card)) :
     let AB := orientedImages W A B
     flowCutResponse ((done,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(flag,payload))))),true::(mask A++mask B))=
       (false,(flowInput G x δ++encodeNat ell,(mask (AB.1\AB.2),(mask (S∪(AB.1∩AB.2)),(false,[]))))) := by
   dsimp only
   unfold flowCutResponse
   rw [postMaskPair_correct,orientMasks_correct]
   simp only [Finset.card_image_of_injective _ (activeMap W).injective]
   unfold orientedImages
   split_ifs <;> exact cutUpdate_correct _ done flag W S _ _ payload
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowOutcome
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.FlowLaw
open ActiveTransport

 theorem large_active_ratio (n m : ℕ) (h : 2*n<3*m) : (n:ℝ)^2≤3*(m:ℝ)^2 := by
   have hh : (2:ℝ)*n<3*m := by exact_mod_cast h
   have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2*n) hh.le 2
   nlinarith only [hpow,sq_nonneg (n:ℝ)]
 theorem normalized_flow_outcome {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (x : Fin n → ℝ)
     (ell gamma : ℝ) (hn : 2≤ n) (hW : 2*n<3*W.card) (hx : ∀v,0≤ x v)
     (hk : 0< vertexSum x Finset.univ) (hell : 0≤ ell)
     (hgamma : gamma=ell*(n:ℝ)^2/(3*vertexSum x Finset.univ))
     (f : List (List (Fin W.card)×ℚ)) (hf : UnitFlow (activeGraph G W) f)
     (hcap : ∀v,vertexMass (realPaths f) v≤ gamma*x (activeMap W v)) :
     PathOutcome G x ell W (realPaths (normalizeLift (activeMap W) f)) := by
   have hm : 0< W.card := by omega
   have hmR : (0:ℝ)< W.card := by exact_mod_cast hm
   have hq : (0:ℝ)<(W.card:ℝ)^2 := sq_pos_of_pos hmR
   rw [normalizeLift_real]
   refine ⟨hW,lift_valid G (activeGraph G W) (activeMap W) W (activeMap_image W)
     (fun _ _ => Iff.rfl) _ (scale_valid _ _ _ _ hq.le hf.1),?_,?_,?_⟩
   · rw [lift_total,scale_total,unit_total _ _ hf]
     exact div_self hq.ne'
   · intro u hu v hv
     obtain ⟨i,hi,hei⟩ := Finset.mem_image.mp ((activeMap_image W).symm ▸ hu)
     obtain ⟨j,hj,hej⟩ := Finset.mem_image.mp ((activeMap_image W).symm ▸ hv)
     subst u
     subst v
     rw [lift_endpointMass,scale_endpoint,hf.2]
   · intro v hv
     obtain ⟨i,hi,hei⟩ := Finset.mem_image.mp ((activeMap_image W).symm ▸ hv)
     subst v
     rw [lift_vertexMass,scale_vertex]
     have hratio := large_active_ratio n W.card hW
     have hmul := mul_le_mul_of_nonneg_left hratio hell
     have hfactor : gamma/(W.card:ℝ)^2≤ ell/vertexSum x Finset.univ := by
       apply (div_le_div_iff₀ hq hk).mpr
       rw [hgamma]
       have he : ell*(n:ℝ)^2/(3*vertexSum x Finset.univ)*vertexSum x Finset.univ=ell*(n:ℝ)^2/3 := by
         field_simp
         <;> ring
       rw [he]
       apply (div_le_iff₀ (by norm_num : (0:ℝ)<3)).mpr
       nlinarith only [hmul]
     calc
       vertexMass (realPaths f) i/(W.card:ℝ)^2≤(gamma*x (activeMap W i))/(W.card:ℝ)^2 :=
         div_le_div_of_nonneg_right (hcap i) hq.le
       _ = (gamma/(W.card:ℝ)^2)*x (activeMap W i) := by ring
       _ ≤ (ell/vertexSum x Finset.univ)*x (activeMap W i) := mul_le_mul_of_nonneg_right hfactor (hx _)
       _ = ell*x (activeMap W i)/vertexSum x Finset.univ := by ring
end EdgeSublinearMWIS.Main.FlowLaw
end

-- Solutions.FlowGoodState
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ActiveTransport ComponentRefinement

 def flowRecord {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode) (ell : ℕ)
     (done : Bool) (W S : Finset (Fin n)) (flag : Bool) (payload : List Bool) : List Bool :=
   flowLoopBits (done,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(flag,payload)))))
 def FlowGood {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode) (ell : ℕ)
     (F : ℝ) (J i : ℕ) (L : List Bool) : Prop :=
   (∃W S,L=flowRecord G x δ ell false W S false [] ∧ Invariant G S W ∧
     vertexSum (fun v => ((x v).value:ℝ)) S≤ F*((n:ℝ)-W.card) ∧ W.card+i≤ n) ∨
   (∃W S,L=flowRecord G x δ ell true W S false [] ∧ Light G Finset.univ S δ.value (fun v => ((x v).value:ℝ))) ∨
   (∃(W S : Finset (Fin n)) (f : List (List (Fin W.card)×ℚ)),
     L=flowRecord G x δ ell true W S true (encodeSparsePaths f) ∧
     PathOutcome G (fun v => ((x v).value:ℝ)) ell W (realPaths (FlowLaw.normalizeLift (activeMap W) f)) ∧
     (encodeSparsePaths f).length≤ J)
 theorem FlowGood.initial {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode) (ell : ℕ) (F : ℝ) (J : ℕ) :
     FlowGood G x δ ell F J 0 (flowInitialBits (flowInput G x δ++encodeNat ell)) := by
   apply Or.inl
   refine ⟨Finset.univ,∅,?_,ComponentRefinement.initial G,?_,?_⟩
   · unfold flowInitialBits flowRecord
     rw [flowInitialRecord_correct]
   · simp [vertexSum]
   · simp
 theorem FlowGood.size {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode) (ell : ℕ)
     (F : ℝ) (J i : ℕ) (L : List Bool) (h : FlowGood G x δ ell F J i L) :
     L.length≤4*((flowInput G x δ++encodeNat ell).length+1)+5+J := by
   rcases h with h|h|h
   · obtain ⟨W,S,rfl,hi,hMass,hRank⟩ := h
     exact (flow_record_size G x δ ell false W S false []).trans (by simp)
   · obtain ⟨W,S,rfl,hLight⟩ := h
     exact (flow_record_size G x δ ell true W S false []).trans (by simp)
   · obtain ⟨W,S,f,rfl,hLaw,hsize⟩ := h
     exact (flow_record_size G x δ ell true W S true (encodeSparsePaths f)).trans (by omega)
 theorem FlowGood.finish {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode) (ell : ℕ)
     (F : ℝ) (J : ℕ) (L : List Bool) (h : FlowGood G x δ ell F J n L)
     (hFinal : F*n≤(δ.value:ℝ)*vertexSum (fun v => ((x v).value:ℝ)) Finset.univ) :
     (∃S,flowFinishBits L=false::mask S ∧ Light G Finset.univ S δ.value (fun v => ((x v).value:ℝ))) ∨
       ∃(W : Finset (Fin n)) (f : List (List (Fin n)×ℚ)),
         flowFinishBits L=true::(mask W++encodeSparsePaths f) ∧ PathOutcome G (fun v => ((x v).value:ℝ)) ell W (realPaths f) := by
   rcases h with h|h|h
   · obtain ⟨W,S,rfl,hi,hMass,hRank⟩ := h
     have hw : W.card=0 := by omega
     refine Or.inl ⟨S,flowFinishBits_balanced G x δ ell false W S [],?_,?_⟩
     · exact terminal G S W hi (by omega)
     · simp only [hw,Nat.cast_zero,sub_zero] at hMass
       exact hMass.trans hFinal
   · obtain ⟨W,S,rfl,hLight⟩ := h
     exact Or.inl ⟨S,flowFinishBits_balanced G x δ ell true W S [],hLight⟩
   · obtain ⟨W,S,f,rfl,hLaw,hsize⟩ := h
     have hw : 0< W.card := by have hh := hLaw.1;omega
     exact Or.inr ⟨W,FlowLaw.normalizeLift (activeMap W) f,flowFinishBits_law G x δ ell true W S f hw,hLaw⟩
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowTurnProtocol
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ActiveTransport

 theorem flowLoopPost_skip (L : List Bool) : flowLoopPost (prefixBits (false::L))=L := by
   have hh := readWord_prefix (false::L) []
   simp only [List.append_nil] at hh
   simp only [flowLoopPost,hh,flowPostBody,List.headD_cons,Bool.false_eq_true,if_false,List.tail_cons]
 theorem loopSmall_correct {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode)
     (ell : ℕ) (done flag : Bool) (W S : Finset (Fin n)) (payload : List Bool) :
     loopSmall (done,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(flag,payload)))))=decide (3*W.card≤2*n) := by
   simp only [loopSmall,maskCard_correct,weightedParse_flow_append]
   have h1 : W.card+W.card+W.card=3*W.card := by omega
   have h2 : n+n=2*n := by omega
   rw [h1,h2]
 theorem flowLoopPost_invoke (done : Bool) (base W S : List Bool) (flag : Bool) (payload output : List Bool)
     (n : ℕ) (hN : (readNatural base).1=n) (hW : W.length=n) (hS : S.length=n) :
     flowLoopPost (prefixBits (true::flowLoopBits (done,(base,(W,(S,(flag,payload))))))++output)=
       flowLoopBits (flowRespond ((done,(base,(W,(S,(flag,payload))))),output)) := by
   simp only [flowLoopPost,readWord_prefix,flowPostBody,List.headD_cons,if_true,flowRespondInput,List.tail_cons]
   rw [flowLoopParse_bits done base W S flag payload n hN hW hS]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowTurnPreMath
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ActiveTransport

 theorem flowLoopPre_done {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode)
     (ell : ℕ) (W S : Finset (Fin n)) (flag : Bool) (payload : List Bool) :
     let s : FlowLoopState := (true,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(flag,payload)))))
     flowLoopPre (flowLoopBits s)=false::prefixBits (false::flowLoopBits s) := by
   dsimp only
   unfold flowLoopPre
   rw [flowLoopParse_bits true _ _ _ flag payload n (readNatural_flowInput G x δ ell) (by simp [mask]) (by simp [mask])]
   rfl
 theorem flowLoopPre_small {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode)
     (ell : ℕ) (W S : Finset (Fin n)) (flag : Bool) (payload : List Bool) (hSmall : 3*W.card≤2*n) :
     let s : FlowLoopState := (false,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(flag,payload)))))
     flowLoopPre (flowLoopBits s)=false::prefixBits (false::flowLoopBits (freezeBalanced s)) := by
   dsimp only
   unfold flowLoopPre
   rw [flowLoopParse_bits false _ _ _ flag payload n (readNatural_flowInput G x δ ell) (by simp [mask]) (by simp [mask])]
   simp only [flowPrepare,Bool.false_eq_true,if_false,loopSmall_correct,hSmall,decide_true,if_true,skipFlowCall]
 theorem flowLoopPre_active {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode)
     (ell : ℕ) (W S : Finset (Fin n)) (flag : Bool) (payload : List Bool)
     (hLarge : 2*n<3*W.card) (hx : ∀v,0≤(x v).value) (hk : 0<∑v,(x v).value) :
     let s : FlowLoopState := (false,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(flag,payload)))))
     flowLoopPre (flowLoopBits s)=true::(prefixBits (true::flowLoopBits s)++
       flowInput (activeGraph G W) (inducedCodes W x) (ratCode ((ell:ℚ)*(n:ℚ)^2/(3*∑v,(x v).value)))) := by
   dsimp only
   unfold flowLoopPre
   rw [flowLoopParse_bits false _ _ _ flag payload n (readNatural_flowInput G x δ ell) (by simp [mask]) (by simp [mask])]
   have hSmall : ¬3*W.card≤2*n := by omega
   simp only [flowPrepare,Bool.false_eq_true,if_false,loopSmall_correct,hSmall,decide_false,invokeFlowCall]
   rw [flowActivePayload_correct G x δ ell false W S flag payload hx hk]
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

-- Solutions.RawStackTrace
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kDecidableEq
open Turing.TM2
variable {κ Λ σ : Type} [DecidableEq κ] {Γ : κ → Type}

 def cfg (l : Option Λ) (v : σ) (S : ∀i,List (Γ i)) : Cfg Γ Λ σ := ⟨l,v,S⟩
 def run (code : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) : ℕ → Option (Cfg Γ Λ σ)
   | 0 => some c
   | t+1 => (run code c t).bind (step code)

 theorem run_iter (code : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) (t : ℕ) :
    run code c t=(fun o : Option (Cfg Γ Λ σ) => o.bind (step code))^[t] (some c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run,ih,Function.iterate_succ_apply']

 theorem run_add (code : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) (s t : ℕ) :
    run code c (s+t)=(run code c s).bind (fun d => run code d t) := by
  induction t with
  | zero => simp only [Nat.add_zero,run]; cases run code c s <;> rfl
  | succ t ih => rw [Nat.add_succ,run,ih]; simp only [Option.bind_assoc,run]

 theorem run_trans (code : Λ → Stmt Γ Λ σ) (c d e : Cfg Γ Λ σ) (s t : ℕ)
    (hs : run code c s=some d) (ht : run code d t=some e) : run code c (s+t)=some e := by
  rw [run_add,hs,Option.bind_some,ht]

 theorem run_one (code : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) : run code c 1=step code c := rfl

 theorem run_first (code : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) (t : ℕ) :
    run code c (t+1)=(step code c).bind (fun d => run code d t) := by
  rw [show t+1=1+t by omega,run_add,run_one]

 theorem outputs {tm : Turing.FinTM2} (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁))
    (t : ℕ) (h : run tm.m (Turing.initList tm input) t=some (Turing.haltList tm output)) :
    Nonempty (Turing.TM2OutputsInTime tm input (some output) t) := by
  refine ⟨⟨⟨t,?_⟩,le_rfl⟩⟩
  have h' := run_iter tm.m (Turing.initList tm input) t
  rw [h'] at h
  exact h

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ProgramEmbedding
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
variable {κ μ Λ Ω σ τ : Type} [DecidableEq κ] [DecidableEq μ]
variable {Γ : κ → Type} {Δ : μ → Type}

 abbrev StackSum (A : κ → Type) (B : μ → Type) : κ⊕μ → Type
   | .inl k => A k
   | .inr k => B k

 def extendStore (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) : ∀k : κ⊕μ,List (StackSum Γ Δ k) := fun k => match k with | .inl k => S k | .inr k => T k
 @[simp] theorem extendStore_inl (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) (k : κ) : extendStore S T (.inl k)=S k := rfl
 @[simp] theorem extendStore_inr (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) (k : μ) : extendStore S T (.inr k)=T k := rfl

 def extendCfg (ret : Ω) (v : τ) (T : ∀k,List (Δ k)) (c : Cfg Γ Λ σ) :
     Cfg (StackSum Γ Δ) (Λ⊕Ω) (σ×τ) :=
   ⟨some (match c.l with | none => .inr ret | some l => .inl l),(c.var,v),extendStore c.stk T⟩
 def extendStmt (ret : Ω) : Stmt Γ Λ σ → Stmt (StackSum Γ Δ) (Λ⊕Ω) (σ×τ)
   | .push k f q => .push (.inl k) (fun v => f v.1) (extendStmt ret q)
   | .pop k f q => .pop (.inl k) (fun v a => (f v.1 a,v.2)) (extendStmt ret q)
   | .peek k f q => .peek (.inl k) (fun v a => (f v.1 a,v.2)) (extendStmt ret q)
   | .load f q => .load (fun v => (f v.1,v.2)) (extendStmt ret q)
   | .branch f q r => .branch (fun v => f v.1) (extendStmt ret q) (extendStmt ret r)
   | .goto f => .goto (fun v => .inl (f v.1))
   | .halt => .goto (fun _ => .inr ret)

 theorem update_extend (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) (k : κ) (x : List (Γ k)) :
     Function.update (extendStore S T) (.inl k) x=extendStore (Function.update S k x) T := by
   funext j
   cases j with
   | inl j =>
     by_cases h : j=k
     · subst j; simp [Function.update,extendStore]
     · simp [Function.update,extendStore,h]
   | inr j => simp [Function.update,extendStore]

 theorem stepAux_extend (ret : Ω) (q : Stmt Γ Λ σ) (v : σ) (w : τ)
     (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) :
     stepAux (extendStmt ret q) (v,w) (extendStore S T)=extendCfg ret w T (stepAux q v S) := by
   induction q generalizing v S with
   | push k f q ih =>
     simp only [extendStmt,stepAux,extendStore_inl]
     rw [update_extend]
     exact ih _ _
   | pop k f q ih =>
     simp only [extendStmt,stepAux,extendStore_inl]
     rw [update_extend]
     exact ih _ _
   | peek k f q ih =>
     simp only [extendStmt,stepAux,extendStore_inl]
     exact ih _ _
   | load f q ih => simpa only [extendStmt,stepAux,extendStore_inl] using ih (f v) S
   | branch f q r iq ir =>
     cases hf : f v <;> simp only [extendStmt,stepAux,hf,cond_true,cond_false] <;> first | exact iq v S | exact ir v S
   | goto f => rfl
   | halt => rfl

 theorem step_extend (ret : Ω) (code : Λ → Stmt Γ Λ σ)
     (target : Λ⊕Ω → Stmt (StackSum Γ Δ) (Λ⊕Ω) (σ×τ))
     (hcode : ∀l,target (.inl l)=extendStmt ret (code l))
     (c : Cfg Γ Λ σ) (w : τ) (T : ∀k,List (Δ k)) (l : Λ) (hc : c.l=some l) :
     step target (extendCfg ret w T c)=(step code c).map (extendCfg ret w T) := by
   rcases c with ⟨cl,v,S⟩
   dsimp only at hc
   subst cl
   simp only [extendCfg,step,hcode,Option.map_some]
   exact congrArg some (stepAux_extend ret (code l) v w S T)

 theorem run_extend (ret : Ω) (code : Λ → Stmt Γ Λ σ)
     (target : Λ⊕Ω → Stmt (StackSum Γ Δ) (Λ⊕Ω) (σ×τ))
     (hcode : ∀l,target (.inl l)=extendStmt ret (code l))
     (c d : Cfg Γ Λ σ) (w : τ) (T : ∀k,List (Δ k)) (t : ℕ)
     (hr : RawStack.run code c t=some d) :
     RawStack.run target (extendCfg ret w T c) t=some (extendCfg ret w T d) := by
   induction t generalizing c with
   | zero => simp only [RawStack.run,Option.some.injEq] at hr; subst d; rfl
   | succ t ih =>
     rw [RawStack.run_first] at hr ⊢
     cases hc : c.l with
     | none =>
       have hn : step code c=none := by cases c; simp_all [step]
       rw [hn,Option.bind_none] at hr
       contradiction
     | some l =>
       have hs : ∃ e,step code c=some e := by cases c; simp_all [step]
       obtain ⟨e,he⟩ := hs
       rw [step_extend ret code target hcode c w T l hc,he,Option.map_some,Option.bind_some]
       rw [he,Option.bind_some] at hr
       exact ih e hr

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ProgramPrefix
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
variable {κ μ Λ Ω σ τ : Type} [DecidableEq κ] [DecidableEq μ]
variable {Γ : κ → Type} {Δ : μ → Type}

 def prefixStore (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) : ∀k : μ⊕κ,List (StackSum Δ Γ k) := fun k => match k with | .inl k => T k | .inr k => S k
 @[simp] theorem prefixStore_source (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) (k : κ) : prefixStore S T (.inr k)=S k := rfl
 @[simp] theorem prefixStore_extra (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) (k : μ) : prefixStore S T (.inl k)=T k := rfl

 def prefixCfg (ret : Ω) (v : τ) (T : ∀k,List (Δ k)) (c : Cfg Γ Λ σ) :
     Cfg (StackSum Δ Γ) (Ω⊕Λ) (τ×σ) :=
   ⟨some (match c.l with | none => .inl ret | some l => .inr l),(v,c.var),prefixStore c.stk T⟩
 def prefixStmt (ret : Ω) : Stmt Γ Λ σ → Stmt (StackSum Δ Γ) (Ω⊕Λ) (τ×σ)
   | .push k f q => .push (.inr k) (fun v => f v.2) (prefixStmt ret q)
   | .pop k f q => .pop (.inr k) (fun v a => (v.1,f v.2 a)) (prefixStmt ret q)
   | .peek k f q => .peek (.inr k) (fun v a => (v.1,f v.2 a)) (prefixStmt ret q)
   | .load f q => .load (fun v => (v.1,f v.2)) (prefixStmt ret q)
   | .branch f q r => .branch (fun v => f v.2) (prefixStmt ret q) (prefixStmt ret r)
   | .goto f => .goto (fun v => .inr (f v.2))
   | .halt => .goto (fun _ => .inl ret)

 theorem update_prefix (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) (k : κ) (x : List (Γ k)) :
     Function.update (prefixStore S T) (.inr k) x=prefixStore (Function.update S k x) T := by
   funext j
   cases j with
   | inr j =>
     by_cases h : j=k
     · subst j; simp [Function.update,prefixStore]
     · simp [Function.update,prefixStore,h]
   | inl j => simp [Function.update,prefixStore]

 theorem stepAux_prefix (ret : Ω) (q : Stmt Γ Λ σ) (v : σ) (w : τ)
     (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) :
     stepAux (prefixStmt ret q) (w,v) (prefixStore S T)=prefixCfg ret w T (stepAux q v S) := by
   induction q generalizing v S with
   | push k f q ih =>
     simp only [prefixStmt,stepAux,prefixStore_source]
     rw [update_prefix]
     exact ih _ _
   | pop k f q ih =>
     simp only [prefixStmt,stepAux,prefixStore_source]
     rw [update_prefix]
     exact ih _ _
   | peek k f q ih =>
     simp only [prefixStmt,stepAux,prefixStore_source]
     exact ih _ _
   | load f q ih => simpa only [prefixStmt,stepAux,prefixStore_source] using ih (f v) S
   | branch f q r iq ir =>
     cases hf : f v <;> simp only [prefixStmt,stepAux,hf,cond_true,cond_false] <;> first | exact iq v S | exact ir v S
   | goto f => rfl
   | halt => rfl

 theorem step_prefix (ret : Ω) (code : Λ → Stmt Γ Λ σ)
     (target : Ω⊕Λ → Stmt (StackSum Δ Γ) (Ω⊕Λ) (τ×σ))
     (hcode : ∀l,target (.inr l)=prefixStmt ret (code l))
     (c : Cfg Γ Λ σ) (w : τ) (T : ∀k,List (Δ k)) (l : Λ) (hc : c.l=some l) :
     step target (prefixCfg ret w T c)=(step code c).map (prefixCfg ret w T) := by
   rcases c with ⟨cl,v,S⟩
   dsimp only at hc
   subst cl
   simp only [prefixCfg,step,hcode,Option.map_some]
   exact congrArg some (stepAux_prefix ret (code l) v w S T)

 theorem run_prefix (ret : Ω) (code : Λ → Stmt Γ Λ σ)
     (target : Ω⊕Λ → Stmt (StackSum Δ Γ) (Ω⊕Λ) (τ×σ))
     (hcode : ∀l,target (.inr l)=prefixStmt ret (code l))
     (c d : Cfg Γ Λ σ) (w : τ) (T : ∀k,List (Δ k)) (t : ℕ)
     (hr : RawStack.run code c t=some d) :
     RawStack.run target (prefixCfg ret w T c) t=some (prefixCfg ret w T d) := by
   induction t generalizing c with
   | zero => simp only [RawStack.run,Option.some.injEq] at hr; subst d; rfl
   | succ t ih =>
     rw [RawStack.run_first] at hr ⊢
     cases hc : c.l with
     | none =>
       have hn : step code c=none := by cases c; simp_all [step]
       rw [hn,Option.bind_none] at hr
       contradiction
     | some l =>
       have hs : ∃ e,step code c=some e := by cases c; simp_all [step]
       obtain ⟨e,he⟩ := hs
       rw [step_prefix ret code target hcode c w T l hc,he,Option.map_some,Option.bind_some]
       rw [he,Option.bind_some] at hr
       exact ih e hr

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.StackTape
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackTape

variable {K : Type} {Γ : K → Type} {b : ℕ}

/-- One-hot symbol slots in a fixed-width block; unused blocks are all false. -/
noncomputable def tapeBit (e : (Sigma Γ) ≃ Fin b) (S : ∀ k, List (Γ k)) (p : ℕ) : Bool :=
  if hr : p % (b + 1) < b then
    let x := e.symm ⟨p % (b + 1), hr⟩
    decide ((S x.1)[p / (b + 1)]? = some x.2)
  else false

 theorem read_cell (e : (Sigma Γ) ≃ Fin b) (S : ∀ k, List (Γ k)) (j : ℕ) (x : Sigma Γ) :
    tapeBit e S (j * (b + 1) + (e x).val) = decide ((S x.1)[j]? = some x.2) := by
  have hslot : (e x).val < b + 1 := (e x).isLt.trans (Nat.lt_succ_self _)
  have hmod : (j * (b + 1) + (e x).val) % (b + 1) = (e x).val := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hslot]
  have hdiv : (j * (b + 1) + (e x).val) / (b + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_succ b), Nat.div_eq_of_lt hslot, Nat.zero_add]
  have hr : (j * (b + 1) + (e x).val) % (b + 1) < b := by rw [hmod]; exact (e x).isLt
  have he : e.symm ⟨(j * (b + 1) + (e x).val) % (b + 1), hr⟩ = x := by
    calc
      _ = e.symm (e x) := congrArg e.symm (Fin.ext hmod)
      _ = x := e.symm_apply_apply x
  unfold tapeBit
  rw [dif_pos hr]
  simp only [hdiv]
  exact congrArg (fun z : Sigma Γ => decide ((S z.1)[j]? = some z.2)) he

 theorem tape_injective (e : (Sigma Γ) ≃ Fin b) : Function.Injective (tapeBit e) := by
  intro S T h
  funext k
  apply List.ext_getElem?
  intro j
  apply Option.ext
  intro γ
  have hh := congrFun h (j * (b + 1) + (e ⟨k,γ⟩).val)
  simp only [read_cell] at hh
  simpa only [Option.mem_def, eq_comm] using (decide_eq_decide.mp hh)

 theorem beyond_false (e : (Sigma Γ) ≃ Fin b) (S : ∀ k, List (Γ k)) (bound p : ℕ)
    (hbound : ∀ k, (S k).length ≤ bound) (hp : bound ≤ p / (b + 1)) : tapeBit e S p = false := by
  unfold tapeBit
  split_ifs with hr
  · dsimp
    have hlen := (hbound (e.symm ⟨p % (b + 1), hr⟩).1).trans hp
    simp [List.getElem?_eq_none hlen]
  · rfl

 theorem empty_tape (e : (Sigma Γ) ≃ Fin b) : tapeBit e (fun _ => []) = fun _ => false := by
  funext p
  exact beyond_false e (fun _ => []) 0 p (fun _ => Nat.le_refl _) (Nat.zero_le _)

end EdgeSublinearMWIS.Main.StackTape
end

-- Solutions.StackSpace
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackSpace

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

 def cost : Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => cost q + 1
  | .peek _ _ q => cost q + 1
  | .pop _ _ q => cost q + 1
  | .load _ q => cost q + 1
  | .branch _ q r => max (cost q) (cost r) + 1
  | .goto _ => 1
  | .halt => 1

 theorem cost_pos (q : Turing.TM2.Stmt Γ Λ σ) : 0 < cost q := by cases q <;> simp [cost]

 def space [Fintype K] (S : ∀ k, List (Γ k)) : ℕ := ∑ k, (S k).length

 theorem space_update [Fintype K] [DecidableEq K] (S : ∀ k, List (Γ k)) (k : K) (L : List (Γ k)) :
    space (Function.update S k L) + (S k).length = space S + L.length := by
  have heq : (fun j => (Function.update S k L j).length) = Function.update (fun j => (S j).length) k L.length := by
    funext j
    by_cases h : j = k
    · subst j; simp
    · simp [Function.update, h]
  unfold space
  rw [heq, Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add (s := Finset.univ) (fun j => (S j).length) (Finset.mem_univ k)
  omega

 theorem stepAux_space [Fintype K] [DecidableEq K] (q : Turing.TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) :
    space (Turing.TM2.stepAux q v S).stk ≤ space S + cost q := by
  induction q generalizing v S with
  | push k f q ih =>
    have hh := ih v (Function.update S k (f v :: S k))
    have hu := space_update S k (f v :: S k)
    simp only [List.length_cons] at hu
    change space (Turing.TM2.stepAux q v (Function.update S k (f v :: S k))).stk ≤ space S + (cost q + 1)
    omega
  | peek k f q ih =>
    have hh := ih (f v (S k).head?) S
    change space (Turing.TM2.stepAux q (f v (S k).head?) S).stk ≤ space S + (cost q + 1)
    omega
  | pop k f q ih =>
    have hh := ih (f v (S k).head?) (Function.update S k (S k).tail)
    have hu := space_update S k (S k).tail
    have hl : (S k).tail.length ≤ (S k).length := by simp only [List.length_tail]; omega
    change space (Turing.TM2.stepAux q (f v (S k).head?) (Function.update S k (S k).tail)).stk ≤ space S + (cost q + 1)
    omega
  | load f q ih =>
    have hh := ih (f v) S
    change space (Turing.TM2.stepAux q (f v) S).stk ≤ space S + (cost q + 1)
    omega
  | branch f q r ihq ihr =>
    change space (cond (f v) (Turing.TM2.stepAux q v S) (Turing.TM2.stepAux r v S)).stk ≤ space S + (max (cost q) (cost r) + 1)
    cases hv : f v with
    | false => simp only [cond_false]; have hh := ihr v S; have hm := le_max_right (cost q) (cost r); omega
    | true => simp only [cond_true]; have hh := ihq v S; have hm := le_max_left (cost q) (cost r); omega
  | goto f => simp [Turing.TM2.stepAux, cost]
  | halt => simp [Turing.TM2.stepAux, cost]

 def bound (tm : Turing.FinTM2) : ℕ := Finset.univ.sup (fun l => cost (tm.m l))

 theorem cost_le_bound (tm : Turing.FinTM2) (l : tm.Λ) : cost (tm.m l) ≤ bound tm := by
  unfold bound
  exact Finset.le_sup (f := fun l => cost (tm.m l)) (Finset.mem_univ l)

 theorem bound_pos (tm : Turing.FinTM2) : 0 < bound tm :=
  (cost_pos (tm.m tm.main)).trans_le (cost_le_bound tm tm.main)

 theorem initial_space (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) :
    space (Turing.initList tm input).stk = input.length := by
  have hlen (k : tm.K) : ((Turing.initList tm input).stk k).length = if k = tm.k₀ then input.length else 0 := by
    by_cases h : k = tm.k₀
    · subst k; simp [Turing.initList]
    · simp [Turing.initList, h]
  unfold space
  simp only [hlen]
  simp

 set_option backward.isDefEq.respectTransparency.types false in
 theorem step_space (tm : Turing.FinTM2) (c c' : tm.Cfg) (h : tm.step c = some c') :
    space c'.stk ≤ space c.stk + bound tm := by
  letI : DecidableEq tm.K := tm.decidableEqK
  change Turing.TM2.step tm.m c = some c' at h
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [Turing.FinTM2.step, Turing.TM2.step] at h
  | some l =>
    change some (Turing.TM2.stepAux (tm.m l) v S) = some c' at h
    have heq := Option.some.inj h
    rw [← heq]
    exact (stepAux_space (tm.m l) v S).trans (Nat.add_le_add_left (cost_le_bound tm l) _)

 def run (tm : Turing.FinTM2) (start : tm.Cfg) : ℕ → Option tm.Cfg
  | 0 => some start
  | t + 1 => (run tm start t).bind tm.step

 theorem run_space (tm : Turing.FinTM2) (start : tm.Cfg) (t : ℕ) (c : tm.Cfg)
    (h : run tm start t = some c) : space c.stk ≤ space start.stk + bound tm * t := by
  induction t generalizing c with
  | zero => simp only [run, Option.some.injEq] at h; subst c; simp
  | succ t ih =>
    cases he : run tm start t with
    | none => simp only [run, he, Option.bind_none, reduceCtorEq] at h
    | some prev =>
      have hstep : tm.step prev = some c := by simpa only [run, he, Option.bind_some] using h
      have hi := ih prev he
      have hs := step_space tm prev c hstep
      rw [Nat.mul_succ]
      omega

 theorem input_run_space (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (t : ℕ) (c : tm.Cfg)
    (h : run tm (Turing.initList tm input) t = some c) : space c.stk ≤ input.length + bound tm * t := by
  simpa only [initial_space] using run_space tm (Turing.initList tm input) t c h

 theorem stack_length_le_space [Fintype K] (S : ∀ k, List (Γ k)) (k : K) : (S k).length ≤ space S := by
  unfold space
  exact Finset.single_le_sum (f := fun j => (S j).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

end EdgeSublinearMWIS.Main.StackSpace
end

-- Solutions.StackCompilerTypes
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackCompiler

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

noncomputable instance alphabetFintype (P : EdgeSublinearMWIS.Main.Program) (k : P.machine.tm.K) :
    Fintype (P.machine.tm.Γ k) := @Fintype.ofFinite _ (P.finiteAlphabet k)

noncomputable def allStatements (P : EdgeSublinearMWIS.Main.Program) : Finset P.machine.tm.Stmt :=
  Finset.univ.biUnion (fun l => Turing.TM2.stmts₁ (P.machine.tm.m l))

abbrev Statement (P : EdgeSublinearMWIS.Main.Program) := {q // q ∈ allStatements P}

abbrev Resume (P : EdgeSublinearMWIS.Main.Program) := Statement P × P.machine.tm.σ

noncomputable def alphabetCode (P : EdgeSublinearMWIS.Main.Program) :
    (Sigma P.machine.tm.Γ) ≃ Fin (Fintype.card (Sigma P.machine.tm.Γ)) := Fintype.equivFin _

noncomputable def blockSize (P : EdgeSublinearMWIS.Main.Program) : ℕ := Fintype.card (Sigma P.machine.tm.Γ) + 1

 theorem blockSize_pos (P : EdgeSublinearMWIS.Main.Program) : 0 < blockSize P := Nat.zero_lt_succ _

 theorem main_mem (P : EdgeSublinearMWIS.Main.Program) (l : P.machine.tm.Λ) :
    P.machine.tm.m l ∈ allStatements P := by
  exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, Turing.TM2.stmts₁_self⟩

noncomputable instance resumeFintype (P : EdgeSublinearMWIS.Main.Program) : Fintype (Resume P) := inferInstance

end EdgeSublinearMWIS.Main.StackCompiler
end

-- Solutions.ProgramSequence
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 inductive Phase where | out | into | finish deriving Fintype,DecidableEq
 abbrev SeqK (P Q : Program) := P.machine.tm.K⊕(Q.machine.tm.K⊕Unit)
 abbrev SeqΓ (P Q : Program) : SeqK P Q → Type := StackSum P.machine.tm.Γ (StackSum Q.machine.tm.Γ (fun _ : Unit => Bool))
 noncomputable instance seqAlphabet (P Q : Program) (k : SeqK P Q) : Fintype (SeqΓ P Q k) :=
   @Fintype.ofFinite _ (by
     cases k with
     | inl k => exact P.finiteAlphabet k
     | inr k => cases k with
       | inl k => exact Q.finiteAlphabet k
       | inr u => change Finite Bool; infer_instance)
 abbrev SeqΛ (P Q : Program) := P.machine.tm.Λ⊕(Q.machine.tm.Λ⊕Phase)
 abbrev Seqσ (P Q : Program) := P.machine.tm.σ×(Q.machine.tm.σ×Option Bool)
 def seqInitial (P Q : Program) : Seqσ P Q := (P.machine.tm.initialState,(Q.machine.tm.initialState,none))
 def setCarry {P Q : Program} (v : Seqσ P Q) (b : Option Bool) : Seqσ P Q := (v.1,(v.2.1,b))
 def outLabel {P Q : Program} : SeqΛ P Q := .inr (.inr .out)
 def intoLabel {P Q : Program} : SeqΛ P Q := .inr (.inr .into)
 def finishLabel {P Q : Program} : SeqΛ P Q := .inr (.inr .finish)
 def tempStack {P Q : Program} : SeqK P Q := .inr (.inr ())

 def seqCode (P Q : Program) : SeqΛ P Q → Stmt (SeqΓ P Q) (SeqΛ P Q) (Seqσ P Q)
   | .inl l => extendStmt (.inr .out) (P.machine.tm.m l)
   | .inr (.inl l) => prefixStmt P.machine.tm.main (extendStmt .finish (Q.machine.tm.m l))
   | .inr (.inr .out) =>
     .peek (.inl P.machine.tm.k₁) (fun v a => setCarry v (a.map P.machine.outputAlphabet))
       (.branch (fun v => v.2.2.isSome)
         (.push tempStack (fun v => v.2.2.getD false)
           (.pop (.inl P.machine.tm.k₁) (fun v _ => setCarry v none) (.goto (fun _ => outLabel))))
         (.load (fun v => setCarry v none) (.goto (fun _ => intoLabel))))
   | .inr (.inr .into) =>
     .pop tempStack (fun v a => setCarry v a)
       (.branch (fun v => v.2.2.isSome)
         (.push (.inr (.inl Q.machine.tm.k₀)) (fun v => Q.machine.inputAlphabet.symm (v.2.2.getD false))
           (.load (fun v => setCarry v none) (.goto (fun _ => intoLabel))))
         (.load (fun v => setCarry v none) (.goto (fun _ => .inr (.inl Q.machine.tm.main)))))
   | .inr (.inr .finish) => .halt

 def seqTM (P Q : Program) : Turing.FinTM2 where
   K := SeqK P Q
   Γ := SeqΓ P Q
   Λ := SeqΛ P Q
   σ := Seqσ P Q
   k₀ := .inl P.machine.tm.k₀
   k₁ := .inr (.inl Q.machine.tm.k₁)
   initialState := seqInitial P Q
   main := .inl P.machine.tm.main
   m := seqCode P Q
 def sequence (P Q : Program) : Program where
   machine := ⟨seqTM P Q,(by change P.machine.tm.Γ P.machine.tm.k₀ ≃ Bool; exact P.machine.inputAlphabet),
     (by change Q.machine.tm.Γ Q.machine.tm.k₁ ≃ Bool; exact Q.machine.outputAlphabet)⟩
   finiteAlphabet k := by
     cases k with
     | inl k => exact P.finiteAlphabet k
     | inr k => cases k with
       | inl k => exact Q.finiteAlphabet k
       | inr u => change Finite Bool; infer_instance

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ProgramTransfer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 def onlyStack {κ : Type} [DecidableEq κ] {Γ : κ → Type} (k : κ) (L : List (Γ k)) : ∀j,List (Γ j) :=
   Function.update (fun _ => []) k L
 @[simp] theorem onlyStack_self {κ : Type} [DecidableEq κ] {Γ : κ → Type} (k : κ) (L : List (Γ k)) : onlyStack k L k=L := by simp [onlyStack]
 theorem onlyStack_nil {κ : Type} [DecidableEq κ] {Γ : κ → Type} (k : κ) : onlyStack k ([] : List (Γ k))=(fun _ => []) := by simp [onlyStack,Function.update_eq_self]
 theorem onlyStack_update {κ : Type} [DecidableEq κ] {Γ : κ → Type} (k : κ) (L R : List (Γ k)) :
     Function.update (onlyStack k L) k R=onlyStack k R := by simp [onlyStack,Function.update_idem]

 def outStore (P Q : Program) (L acc : List Bool) : ∀k,List (SeqΓ P Q k) :=
   extendStore (onlyStack P.machine.tm.k₁ (L.map P.machine.outputAlphabet.symm))
     (extendStore (fun _ => []) (fun _ : Unit => acc))
 def intoStore (P Q : Program) (L acc : List Bool) : ∀k,List (SeqΓ P Q k) :=
   extendStore (fun _ => [])
     (extendStore (onlyStack Q.machine.tm.k₀ (acc.map Q.machine.inputAlphabet.symm)) (fun _ : Unit => L))
 def outCfg (P Q : Program) (L acc : List Bool) : (seqTM P Q).Cfg :=
   cfg (some outLabel) (seqInitial P Q) (outStore P Q L acc)
 def intoCfg (P Q : Program) (L acc : List Bool) : (seqTM P Q).Cfg :=
   cfg (some intoLabel) (seqInitial P Q) (intoStore P Q L acc)

 theorem out_step_cons (P Q : Program) (b : Bool) (L acc : List Bool) :
     step (seqCode P Q) (outCfg P Q (b::L) acc)=some (outCfg P Q L (b::acc)) := by
   change step (seqCode P Q) (cfg (some outLabel) (seqInitial P Q) (outStore P Q (b::L) acc))=
     some (cfg (some outLabel) (seqInitial P Q) (outStore P Q L (b::acc)))
   simp only [cfg,step,seqCode,outLabel,stepAux,outStore,seqInitial,setCarry,extendStore_inl,
     List.map_cons,onlyStack_self,List.head?_cons,Option.map_some,Equiv.apply_symm_apply,Option.isSome_some,
     cond_true,Option.getD_some,List.tail_cons,tempStack,extendStore_inr,Function.update_of_ne (by simp :
       (Sum.inl P.machine.tm.k₁ : SeqK P Q)≠Sum.inr (Sum.inr ()))]
   congr 1
   congr 1
   funext k
   cases k with
   | inl k =>
     by_cases hk : k=P.machine.tm.k₁
     · subst k
       simp [Function.update,onlyStack,extendStore]
     · simp [Function.update,onlyStack,extendStore,hk]
   | inr k => cases k with
     | inl k => simp [Function.update,onlyStack,extendStore]
     | inr u => cases u; simp [Function.update,onlyStack,extendStore]

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ProgramSequenceRun
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 def qCfg (P Q : Program) (c : Q.machine.tm.Cfg) : (seqTM P Q).Cfg :=
   prefixCfg P.machine.tm.main P.machine.tm.initialState (fun _ => [])
     (extendCfg .finish (none : Option Bool) (fun _ : Unit => []) c)
 theorem q_stepAux (P Q : Program) (q : Q.machine.tm.Stmt) (v : Q.machine.tm.σ)
     (S : ∀k,List (Q.machine.tm.Γ k)) :
     stepAux (prefixStmt P.machine.tm.main (extendStmt .finish q))
       (P.machine.tm.initialState,(v,(none : Option Bool)))
       (prefixStore (extendStore S (fun _ : Unit => [])) (fun _ => []))=
         qCfg P Q (stepAux q v S) := by
   rw [stepAux_prefix,stepAux_extend]
   rfl
 theorem q_step (P Q : Program) (c : Q.machine.tm.Cfg) (l : Q.machine.tm.Λ) (hc : c.l=some l) :
     step (seqCode P Q) (qCfg P Q c)=(step Q.machine.tm.m c).map (qCfg P Q) := by
   rcases c with ⟨cl,v,S⟩
   dsimp only at hc
   subst cl
   simp only [qCfg,prefixCfg,extendCfg,step,seqCode,Option.map_some]
   exact congrArg some (q_stepAux P Q (Q.machine.tm.m l) v S)
 theorem q_run (P Q : Program) (c d : Q.machine.tm.Cfg) (t : ℕ)
     (hr : run Q.machine.tm.m c t=some d) :
     run (seqCode P Q) (qCfg P Q c) t=some (qCfg P Q d) := by
   induction t generalizing c with
   | zero => simp only [run,Option.some.injEq] at hr; subst d; rfl
   | succ t ih =>
     rw [run_first] at hr ⊢
     cases hc : c.l with
     | none =>
       have hn : step Q.machine.tm.m c=none := by cases c; simp_all [step]
       rw [hn,Option.bind_none] at hr
       contradiction
     | some l =>
       have hs : ∃ e,step Q.machine.tm.m c=some e := by cases c; simp_all [step]
       obtain ⟨e,he⟩ := hs
       rw [q_step P Q c l hc,he,Option.map_some,Option.bind_some]
       rw [he,Option.bind_some] at hr
       exact ih e hr

 theorem outputs_run (P : Program) (input output : List Bool) (T : ℕ) (h : Runs P input output T) :
     ∃ t,t≤ T ∧ run P.machine.tm.m (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm)) t=
       some (Turing.haltList P.machine.tm (output.map P.machine.outputAlphabet.symm)) := by
   obtain ⟨h⟩ := h
   refine ⟨h.steps,h.steps_le_m,?_⟩
   rw [RawStack.run_iter]
   exact h.evals_in_steps

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ProgramTransferEnd
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem out_step_nil (P Q : Program) (acc : List Bool) :
     step (seqCode P Q) (outCfg P Q [] acc)=some (intoCfg P Q acc []) := by
   simp [outCfg,intoCfg,cfg,step,seqCode,outLabel,intoLabel,stepAux,outStore,intoStore,seqInitial,setCarry,
     onlyStack_nil,tempStack,extendStore]
 theorem into_step_cons (P Q : Program) (b : Bool) (L acc : List Bool) :
     step (seqCode P Q) (intoCfg P Q (b::L) acc)=some (intoCfg P Q L (b::acc)) := by
   simp only [intoCfg,cfg,step,seqCode,intoLabel,stepAux,intoStore,seqInitial,setCarry,tempStack,
     extendStore_inr,extendStore_inl,List.head?_cons,Option.isSome_some,cond_true,Option.getD_some,List.tail_cons]
   congr 1
   congr 1
   funext k
   cases k with
   | inl k => simp [Function.update,onlyStack,extendStore]
   | inr k => cases k with
     | inl k =>
       by_cases hk : k=Q.machine.tm.k₀
       · subst k; simp [Function.update,onlyStack,extendStore]
       · simp [Function.update,onlyStack,extendStore,hk]
     | inr u => cases u; simp [Function.update,onlyStack,extendStore]

 theorem initList_store (tm : Turing.FinTM2) (L : List (tm.Γ tm.k₀)) :
     (Turing.initList tm L).stk=onlyStack tm.k₀ L := by
   funext k
   by_cases h : k=tm.k₀
   · subst k; simp [Turing.initList,onlyStack]
   · simp [Turing.initList,onlyStack,Function.update,h]
 theorem haltList_store (tm : Turing.FinTM2) (L : List (tm.Γ tm.k₁)) :
     (Turing.haltList tm L).stk=onlyStack tm.k₁ L := by
   funext k
   by_cases h : k=tm.k₁
   · subst k; simp [Turing.haltList,onlyStack]
   · simp [Turing.haltList,onlyStack,Function.update,h]

 theorem into_step_nil (P Q : Program) (acc : List Bool) :
     step (seqCode P Q) (intoCfg P Q [] acc)=some (qCfg P Q
       (Turing.initList Q.machine.tm (acc.map Q.machine.inputAlphabet.symm))) := by
   simp only [intoCfg,cfg,step,seqCode,intoLabel,stepAux,intoStore,seqInitial,setCarry,tempStack,
     extendStore_inr,List.head?_nil,Option.isSome_none,cond_false,List.tail_nil]
   congr 1
   simp only [qCfg,prefixCfg,extendCfg,Turing.initList]
   congr 1
   funext k
   cases k with
   | inl k => simp [prefixStore,extendStore,Function.update]
   | inr k => cases k with
     | inl k =>
       by_cases hk : k=Q.machine.tm.k₀
       · subst k; simp [prefixStore,extendStore,Function.update,onlyStack]
       · simp [prefixStore,extendStore,Function.update,onlyStack,hk]
     | inr u => cases u; simp [prefixStore,extendStore,Function.update,onlyStack]

 theorem out_loop (P Q : Program) (L acc : List Bool) :
     run (seqCode P Q) (outCfg P Q L acc) (L.length+1)=some (intoCfg P Q (L.reverse++acc) []) := by
   induction L generalizing acc with
   | nil => exact out_step_nil P Q acc
   | cons b L ih =>
     rw [List.length_cons,run_first,out_step_cons,Option.bind_some]
     have hh := ih (b::acc)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
 theorem into_loop (P Q : Program) (L acc : List Bool) :
     run (seqCode P Q) (intoCfg P Q L acc) (L.length+1)=some (qCfg P Q
       (Turing.initList Q.machine.tm ((L.reverse++acc).map Q.machine.inputAlphabet.symm))) := by
   induction L generalizing acc with
   | nil => exact into_step_nil P Q acc
   | cons b L ih =>
     rw [List.length_cons,run_first,into_step_cons,Option.bind_some]
     have hh := ih (b::acc)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ProgramCompositionRuns
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem cfg_eq {κ Λ σ : Type} {Γ : κ → Type} {c d : Cfg Γ Λ σ}
     (hl : c.l=d.l) (hv : c.var=d.var) (hs : c.stk=d.stk) : c=d := by
   cases c; cases d; simp_all

 def seqExtra (Q : Program) : ∀k : Q.machine.tm.K⊕Unit,List (StackSum Q.machine.tm.Γ (fun _ : Unit => Bool) k) :=
   extendStore (fun _ => []) (fun _ => [])
 theorem p_start (P Q : Program) (input : List Bool) :
     extendCfg (.inr Phase.out) (Q.machine.tm.initialState,(none : Option Bool)) (seqExtra Q)
       (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm))=
         Turing.initList (seqTM P Q) (input.map P.machine.inputAlphabet.symm) := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change extendStore (Turing.initList P.machine.tm _).stk (seqExtra Q)=(Turing.initList (seqTM P Q) _).stk
   rw [initList_store,initList_store]
   funext k
   cases k with
   | inl k =>
     by_cases hk : k=P.machine.tm.k₀
     · subst k; simp [onlyStack,Function.update,seqTM,extendStore]
     · simp [onlyStack,Function.update,seqTM,extendStore,hk]
   | inr k => cases k with
     | inl k => simp [onlyStack,Function.update,seqTM,extendStore,seqExtra]
     | inr u => cases u; simp [onlyStack,Function.update,seqTM,extendStore,seqExtra]
 theorem p_finish (P Q : Program) (output : List Bool) :
     extendCfg (.inr Phase.out) (Q.machine.tm.initialState,(none : Option Bool)) (seqExtra Q)
       (Turing.haltList P.machine.tm (output.map P.machine.outputAlphabet.symm))=outCfg P Q output [] := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change extendStore (Turing.haltList P.machine.tm _).stk (seqExtra Q)=outStore P Q output []
   rw [haltList_store]
   rfl
 theorem finish_step (P Q : Program) (output : List Bool) :
     step (seqCode P Q) (qCfg P Q (Turing.haltList Q.machine.tm (output.map Q.machine.outputAlphabet.symm)))=
       some (Turing.haltList (seqTM P Q) (output.map Q.machine.outputAlphabet.symm)) := by
   change some (cfg none (seqInitial P Q)
     (prefixStore (extendStore (Turing.haltList Q.machine.tm _).stk (fun _ : Unit => [])) (fun _ => [])))=some _
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change prefixStore (extendStore (Turing.haltList Q.machine.tm _).stk (fun _ : Unit => [])) (fun _ => [])=
     (Turing.haltList (seqTM P Q) _).stk
   rw [haltList_store,haltList_store]
   funext k
   cases k with
   | inl k => simp [prefixStore,extendStore,onlyStack,Function.update,seqTM]
   | inr k => cases k with
     | inl k =>
       by_cases hk : k=Q.machine.tm.k₁
       · subst k; simp [prefixStore,extendStore,onlyStack,Function.update,seqTM]
       · simp [prefixStore,extendStore,onlyStack,Function.update,seqTM,hk]
     | inr u => cases u; simp [prefixStore,extendStore,onlyStack,Function.update,seqTM]

 theorem sequence_runs (P Q : Program) (input middle output : List Bool) (T U : ℕ)
     (hP : Runs P input middle T) (hQ : Runs Q middle output U) :
     Runs (sequence P Q) input output (T+U+2*middle.length+3) := by
   obtain ⟨t,ht,hp⟩ := outputs_run P input middle T hP
   obtain ⟨u,hu,hq⟩ := outputs_run Q middle output U hQ
   have h1 := run_extend (.inr Phase.out) P.machine.tm.m (seqCode P Q) (fun _ => rfl)
     _ _ (Q.machine.tm.initialState,(none : Option Bool)) (seqExtra Q) t hp
   rw [p_start,p_finish] at h1
   have h2 := out_loop P Q middle []
   simp only [List.append_nil] at h2
   have h3 := into_loop P Q middle.reverse []
   simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h3
   have h4 := q_run P Q _ _ u hq
   have h5 : run (seqCode P Q) (qCfg P Q (Turing.haltList Q.machine.tm (output.map Q.machine.outputAlphabet.symm))) 1=
     some (Turing.haltList (seqTM P Q) (output.map Q.machine.outputAlphabet.symm)) := finish_step P Q output
   have hr := run_trans _ _ _ _ _ _ h1 h2
   have hr := run_trans _ _ _ _ _ _ hr h3
   have hr := run_trans _ _ _ _ _ _ hr h4
   have hr := run_trans _ _ _ _ _ _ hr h5
   have he := RawStack.outputs (tm:=seqTM P Q) (input.map P.machine.inputAlphabet.symm)
     (output.map Q.machine.outputAlphabet.symm) _ hr
   obtain ⟨he⟩ := he
   refine ⟨{he with steps_le_m := he.steps_le_m.trans ?_}⟩
   omega

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ProgramCompositionBound
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem spaceRun_eq (tm : Turing.FinTM2) (c : tm.Cfg) (t : ℕ) :
     StackSpace.run tm c t=RawStack.run tm.m c t := by
   induction t with
   | zero => rfl
   | succ t ih => simp only [StackSpace.run,RawStack.run,ih]; rfl
 theorem output_length (P : Program) (input output : List Bool) (T : ℕ) (h : Runs P input output T) :
     output.length≤ input.length+StackSpace.bound P.machine.tm*T := by
   obtain ⟨t,ht,hr⟩ := outputs_run P input output T h
   have hr' : StackSpace.run P.machine.tm (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm)) t=
     some (Turing.haltList P.machine.tm (output.map P.machine.outputAlphabet.symm)) := by rw [spaceRun_eq]; exact hr
   have hs := StackSpace.input_run_space P.machine.tm (input.map P.machine.inputAlphabet.symm) t _ hr'
   have hl := StackSpace.stack_length_le_space (Turing.haltList P.machine.tm (output.map P.machine.outputAlphabet.symm)).stk P.machine.tm.k₁
   simp only [haltList_store,onlyStack_self,List.length_map] at hl
   rw [haltList_store] at hs
   simp only [List.length_map] at hs
   have hmul := Nat.mul_le_mul_left (StackSpace.bound P.machine.tm) ht
   omega

 theorem sequence_runs_linear (P Q : Program) :
     ∃ K : ℕ,0< K ∧ ∀ (input middle output : List Bool) (T U : ℕ),
       Runs P input middle T → Runs Q middle output U →
       Runs (sequence P Q) input output (K*(T+U+input.length+1)) := by
   refine ⟨2*StackSpace.bound P.machine.tm+4,by omega,?_⟩
   intro input middle output T U hP hQ
   obtain ⟨hr⟩ := sequence_runs P Q input middle output T U hP hQ
   refine ⟨{hr with steps_le_m := hr.steps_le_m.trans ?_}⟩
   have hl := output_length P input middle T hP
   nlinarith

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.FlowBodyExecution
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ProgramComposition ActiveTransport PolynomialTimeBounds

 def FlowBodyContract (U P : Program) (time : Polynomial ℕ) : Prop :=
   (∀input output : List Bool,flowLoopPre input=false::output →
     ∃s,Runs P input (flowLoopPost output) s ∧ s≤ time.eval (2*output.length+input.length+4)) ∧
   (∀(input ctx middle output : List Bool) (T : ℕ),flowLoopPre input=true::(prefixBits ctx++middle) → Runs U middle output T →
     ∃s,Runs P input (flowLoopPost (prefixBits ctx++output)) s ∧
       s≤ time.eval (T+4*ctx.length+2*middle.length+input.length+8))
 theorem flow_body_program (U : Program) : ∃P time,FlowBodyContract U P time := by
   simpa only [FlowBodyContract,prefixBits] using gated_polynomial_context_program flowLoopPre flowLoopPost
     flowLoopPreRealizer flowLoopPostRealizer flowLoopPre_polynomial flowLoopPost_polynomial U
 theorem flow_body_done (U P : Program) (time : Polynomial ℕ) (hP : FlowBodyContract U P time)
     {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode)
     (ell : ℕ) (W S : Finset (Fin n)) (flag : Bool) (payload : List Bool) :
     let s : FlowLoopState := (true,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(flag,payload)))))
     ∃t,Runs P (flowLoopBits s) (flowLoopBits s) t ∧ t≤ time.eval (5*(flowLoopBits s).length+10) := by
   dsimp only
   let s : FlowLoopState := (true,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(flag,payload)))))
   have hPre := flowLoopPre_done G x δ ell W S flag payload
   obtain ⟨t,hr,ht⟩ := hP.1 (flowLoopBits s) (prefixBits (false::flowLoopBits s)) hPre
   rw [flowLoopPost_skip] at hr
   refine ⟨t,hr,?_⟩
   change t≤ time.eval (2*(prefixBits (false::flowLoopBits s)).length+(flowLoopBits s).length+4) at ht
   change t≤ time.eval (5*(flowLoopBits s).length+10)
   apply ht.trans
   apply eval_monotone time
   simp only [prefixBits,List.length_append,List.length_cons,List.length_replicate]
   omega
 theorem flow_body_small (U P : Program) (time : Polynomial ℕ) (hP : FlowBodyContract U P time)
     {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode)
     (ell : ℕ) (W S : Finset (Fin n)) (flag : Bool) (payload : List Bool) (hSmall : 3*W.card≤2*n) :
     let s : FlowLoopState := (false,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(flag,payload)))))
     ∃t,Runs P (flowLoopBits s) (flowLoopBits (freezeBalanced s)) t ∧ t≤ time.eval (5*(flowLoopBits s).length+10) := by
   dsimp only
   let s : FlowLoopState := (false,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(flag,payload)))))
   have hPre := flowLoopPre_small G x δ ell W S flag payload hSmall
   obtain ⟨t,hr,ht⟩ := hP.1 (flowLoopBits s) (prefixBits (false::flowLoopBits (freezeBalanced s))) hPre
   rw [flowLoopPost_skip] at hr
   refine ⟨t,hr,?_⟩
   change t≤ time.eval (2*(prefixBits (false::flowLoopBits (freezeBalanced s))).length+(flowLoopBits s).length+4) at ht
   change t≤ time.eval (5*(flowLoopBits s).length+10)
   apply ht.trans
   apply eval_monotone time
   have hh := freezeBalanced_length s
   simp only [prefixBits,List.length_append,List.length_cons,List.length_replicate]
   omega
 theorem flow_body_active (U P : Program) (time : Polynomial ℕ) (hP : FlowBodyContract U P time)
     {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (δ : RationalCode)
     (ell : ℕ) (W S : Finset (Fin n)) (flag : Bool) (payload output : List Bool) (T : ℕ)
     (hLarge : 2*n<3*W.card) (hx : ∀v,0≤(x v).value) (hk : 0<∑v,(x v).value)
     (hU : Runs U (flowInput (activeGraph G W) (inducedCodes W x) (ratCode ((ell:ℚ)*(n:ℚ)^2/(3*∑v,(x v).value)))) output T) :
     let s : FlowLoopState := (false,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(flag,payload)))))
     let middle := flowInput (activeGraph G W) (inducedCodes W x) (ratCode ((ell:ℚ)*(n:ℚ)^2/(3*∑v,(x v).value)))
     ∃t,Runs P (flowLoopBits s) (flowLoopBits (flowRespond (s,output))) t ∧
       t≤ time.eval (T+5*(flowLoopBits s).length+2*middle.length+12) := by
   dsimp only
   let s : FlowLoopState := (false,(flowInput G x δ++encodeNat ell,(mask W,(mask S,(flag,payload)))))
   have hPre := flowLoopPre_active G x δ ell W S flag payload hLarge hx hk
   obtain ⟨t,hr,ht⟩ := hP.2 (flowLoopBits s) (true::flowLoopBits s) (flowInput (activeGraph G W) (inducedCodes W x) (ratCode ((ell:ℚ)*(n:ℚ)^2/(3*∑v,(x v).value)))) output T hPre hU
   rw [flowLoopPost_invoke false _ _ _ flag payload output n (readNatural_flowInput G x δ ell) (by simp [mask]) (by simp [mask])] at hr
   refine ⟨t,hr,?_⟩
   apply ht.trans
   apply eval_monotone time
   change T+4*(true::flowLoopBits s).length+2*(flowInput (activeGraph G W) (inducedCodes W x) (ratCode ((ell:ℚ)*(n:ℚ)^2/(3*∑v,(x v).value)))).length+(flowLoopBits s).length+8≤
     T+5*(flowLoopBits s).length+2*(flowInput (activeGraph G W) (inducedCodes W x) (ratCode ((ell:ℚ)*(n:ℚ)^2/(3*∑v,(x v).value)))).length+12
   simp only [List.length_cons]
   omega
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowActiveTurn
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ActiveTransport ComponentRefinement SeparationTransport PolynomialTimeBounds ProgramComposition

 theorem flow_active_turn (U P : Program) (K : ℝ) (timeU timeP : Polynomial ℕ)
     (h7 : FlowSevenContract U K timeU) (hP : FlowBodyContract U P timeP) (hK : 0< K)
     {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (delta : RationalCode) (ell : ℕ)
     (F : ℝ) (J i N V : ℕ) (W S : Finset (Fin n))
     (hn : 2≤ n) (hx : ∀v,0≤(x v).value) (hk : 0< vertexSum (fun v => ((x v).value:ℝ)) Finset.univ)
     (hgamma : 0< flowGammaValue x ell) (hF : F=K*n*logTwo n/(flowGammaValue x ell:ℝ))
     (hInv : Invariant G S W) (hMass : vertexSum (fun v => ((x v).value:ℝ)) S≤ F*((n:ℝ)-W.card))
     (hRank : W.card+i≤ n) (hLarge : 2*n<3*W.card)
     (hInput : (flowInput (activeGraph G W) (inducedCodes W x) (ratCode (flowGammaValue x ell))).length+1≤ N)
     (hSize : (flowRecord G x delta ell false W S false []).length≤ V)
     (hJ : N+StackSpace.bound U.machine.tm*timeU.eval N≤ J) :
     ∃L,Runs P (flowRecord G x delta ell false W S false []) L
       (timeP.eval (timeU.eval N+5*V+2*N+12)) ∧ FlowGood G x delta ell F J (i+1) L := by
   have hm : 2≤ W.card := by omega
   have hgCode : 0<(ratCode (flowGammaValue x ell)).value := by rwa [ratCode_value]
   have hxCode : ∀v,0≤(inducedCodes W x v).value := fun v => hx (activeMap W v)
   obtain ⟨t,ht,hout⟩ := h7 W.card (activeGraph G W) (inducedCodes W x) (ratCode (flowGammaValue x ell)) hm hxCode hgCode
   have htMax : t≤ timeU.eval N := ht.trans (eval_monotone timeU hInput)
   have hMid : (flowInput (activeGraph G W) (inducedCodes W x) (ratCode (flowGammaValue x ell))).length≤ N := by omega
   have hkQ := flow_total_positive x hk
   have hgR : (0:ℝ)< flowGammaValue x ell := by exact_mod_cast hgamma
   rcases hout with hflow|hcut
   · obtain ⟨f,hRun,hFlow,hCap⟩ := hflow
     obtain ⟨s,hr,hs⟩ := flow_body_active U P timeP hP G x delta ell W S false [] (false::encodeSparsePaths f) t hLarge hx hkQ hRun
     change Runs P (flowRecord G x delta ell false W S false []) (flowRecord G x delta ell true W S true (encodeSparsePaths f)) s at hr
     have hClock : s≤ timeP.eval (timeU.eval N+5*V+2*N+12) := hs.trans (eval_monotone timeP (by
       change t+5*(flowRecord G x delta ell false W S false []).length+
         2*(flowInput (activeGraph G W) (inducedCodes W x) (ratCode (flowGammaValue x ell))).length+12≤ _
       omega))
     refine ⟨_,NativeCompiler.runs_mono _ _ _ hr hClock,Or.inr (Or.inr ?_)⟩
     refine ⟨W,S,f,rfl,?_,?_⟩
     · apply FlowLaw.normalized_flow_outcome G W (fun v => ((x v).value:ℝ)) ell (flowGammaValue x ell:ℝ) hn hLarge
         (fun v => by exact_mod_cast hx v) hk (Nat.cast_nonneg ell) (flowGammaValue_cast x ell) f hFlow
       intro v
       simpa only [ratCode_value,inducedCodes] using hCap v
     · have hlen := output_length U _ _ t hRun
       have hmul := Nat.mul_le_mul_left (StackSpace.bound U.machine.tm) htMax
       simp only [List.length_cons] at hlen
       omega
   · obtain ⟨A,B,hRun,hSep,hCut⟩ := hcut
     let AB := orientedImages W A B
     have hInside : Inside G W AB.1 AB.2 := orientedImages_inside G W A B hSep
     have hBA : AB.2.card≤ AB.1.card := orientedImages_card W A B
     have hCost := orientedImages_charge G W A B (fun v => ((x v).value:ℝ)) K (flowGammaValue x ell:ℝ)
       (by simpa only [ratCode_value,inducedCodes] using hCut)
     have hCharge : vertexSum (fun v => ((x v).value:ℝ)) (AB.1∩AB.2)≤ F*AB.2.card := by
       rw [hF]
       exact SeparatorPotential.cut_charge G W AB.1 AB.2 (fun v => ((x v).value:ℝ)) K (flowGammaValue x ell:ℝ) hK.le hgR hm hInside hCost
     obtain ⟨s,hr,hs⟩ := flow_body_active U P timeP hP G x delta ell W S false [] (true::(mask A++mask B)) t hLarge hx hkQ hRun
     change Runs P (flowRecord G x delta ell false W S false [])
       (flowLoopBits (flowCutResponse ((false,(flowInput G x delta++encodeNat ell,(mask W,(mask S,(false,[]))))),true::(mask A++mask B)))) s at hr
     rw [flowCutResponse_correct] at hr
     change Runs P (flowRecord G x delta ell false W S false []) (flowRecord G x delta ell false (AB.1\AB.2) (S∪(AB.1∩AB.2)) false []) s at hr
     have hClock : s≤ timeP.eval (timeU.eval N+5*V+2*N+12) := hs.trans (eval_monotone timeP (by
       change t+5*(flowRecord G x delta ell false W S false []).length+
         2*(flowInput (activeGraph G W) (inducedCodes W x) (ratCode (flowGammaValue x ell))).length+12≤ _
       omega))
     refine ⟨_,NativeCompiler.runs_mono _ _ _ hr hClock,Or.inl ?_⟩
     refine ⟨AB.1\AB.2,S∪(AB.1∩AB.2),rfl,refine_cut G S W AB.1 AB.2 hInv hInside hBA,
       SeparatorPotential.potential_step G S W AB.1 AB.2 (fun v => ((x v).value:ℝ)) F hInv hInside hMass hCharge,?_⟩
     have hh := kept_smaller G W AB.1 AB.2 hInside
     omega
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FlowGoodStep
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ActiveTransport ComponentRefinement SeparationTransport PolynomialTimeBounds ProgramComposition

 theorem flow_good_step (U P : Program) (K : ℝ) (timeU timeP : Polynomial ℕ)
     (h7 : FlowSevenContract U K timeU) (hP : FlowBodyContract U P timeP) (hK : 0< K)
     {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (delta : RationalCode) (ell : ℕ)
     (F : ℝ) (J N V : ℕ)
     (hn : 2≤ n) (hx : ∀v,0≤(x v).value) (hk : 0< vertexSum (fun v => ((x v).value:ℝ)) Finset.univ)
     (hgamma : 0< flowGammaValue x ell) (hF : F=K*n*logTwo n/(flowGammaValue x ell:ℝ))
     (hF0 : 0≤ F) (hFinal : F*n≤(delta.value:ℝ)*vertexSum (fun v => ((x v).value:ℝ)) Finset.univ)
     (hInput : ∀W : Finset (Fin n),(flowInput (activeGraph G W) (inducedCodes W x) (ratCode (flowGammaValue x ell))).length+1≤ N)
     (hJ : N+StackSpace.bound U.machine.tm*timeU.eval N≤ J)
     (hV : 4*((flowInput G x delta++encodeNat ell).length+1)+5+J≤ V)
     (i : ℕ) (L : List Bool) (hGood : FlowGood G x delta ell F J i L) :
     ∃L',Runs P L L' (timeP.eval (timeU.eval N+5*V+2*N+12)) ∧ FlowGood G x delta ell F J (i+1) L' := by
   have hSize : L.length≤ V := (FlowGood.size G x delta ell F J i L hGood).trans hV
   rcases hGood with hActive|hBalanced|hFlow
   · obtain ⟨W,S,rfl,hInv,hMass,hRank⟩ := hActive
     by_cases hSmall : 3*W.card≤2*n
     · obtain ⟨t,hr,ht⟩ := flow_body_small U P timeP hP G x delta ell W S false [] hSmall
       change Runs P (flowRecord G x delta ell false W S false []) (flowRecord G x delta ell true W S false []) t at hr
       have hClock : t≤ timeP.eval (timeU.eval N+5*V+2*N+12) := ht.trans (eval_monotone timeP (by
         change 5*(flowRecord G x delta ell false W S false []).length+10≤ _
         omega))
       refine ⟨_,NativeCompiler.runs_mono _ _ _ hr hClock,Or.inr (Or.inl ?_)⟩
       refine ⟨W,S,rfl,terminal G S W hInv hSmall,?_⟩
       have hw0 : (0:ℝ)≤ W.card := Nat.cast_nonneg _
       have hm := mul_nonneg hF0 hw0
       exact (show vertexSum (fun v => ((x v).value:ℝ)) S≤ F*n by nlinarith only [hMass,hm]).trans hFinal
     · exact flow_active_turn U P K timeU timeP h7 hP hK G x delta ell F J i N V W S hn hx hk hgamma hF hInv hMass hRank
         (by omega) (hInput W) hSize hJ
   · obtain ⟨W,S,rfl,hLight⟩ := hBalanced
     obtain ⟨t,hr,ht⟩ := flow_body_done U P timeP hP G x delta ell W S false []
     have hClock : t≤ timeP.eval (timeU.eval N+5*V+2*N+12) := ht.trans (eval_monotone timeP (by
       change 5*(flowRecord G x delta ell true W S false []).length+10≤ _
       omega))
     exact ⟨_,NativeCompiler.runs_mono _ _ _ hr hClock,Or.inr (Or.inl ⟨W,S,rfl,hLight⟩)⟩
   · obtain ⟨W,S,f,rfl,hLaw,hLen⟩ := hFlow
     obtain ⟨t,hr,ht⟩ := flow_body_done U P timeP hP G x delta ell W S true (encodeSparsePaths f)
     have hClock : t≤ timeP.eval (timeU.eval N+5*V+2*N+12) := ht.trans (eval_monotone timeP (by
       change 5*(flowRecord G x delta ell true W S true (encodeSparsePaths f)).length+10≤ _
       omega))
     exact ⟨_,NativeCompiler.runs_mono _ _ _ hr hClock,Or.inr (Or.inr ⟨W,S,f,rfl,hLaw,hLen⟩)⟩
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GoodRunSequence
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main
 theorem good_run_sequence (P : Program) (T : ℕ) (Good : ℕ → List Bool → Prop) (initial : List Bool)
     (hinit : Good 0 initial)
     (hstep : ∀i L,Good i L → ∃L',Runs P L L' T ∧ Good (i+1) L') :
     ∃v : ℕ → List Bool,v 0=initial ∧ (∀i,Good i (v i)) ∧ ∀i,Runs P (v i) (v (i+1)) T := by
   let next (i : ℕ) (s : {L : List Bool // Good i L}) : {L : List Bool // Good (i+1) L} :=
     ⟨Classical.choose (hstep i s.val s.property),(Classical.choose_spec (hstep i s.val s.property)).2⟩
   let states : (i : ℕ) → {L : List Bool // Good i L} := Nat.rec ⟨initial,hinit⟩ next
   refine ⟨fun i => (states i).val,rfl,fun i => (states i).property,?_⟩
   intro i
   exact (Classical.choose_spec (hstep i (states i).val (states i).property)).1
end EdgeSublinearMWIS.Main
end

-- Solutions.FlowProgram
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ActiveTransport ComponentRefinement SeparationTransport PolynomialTimeBounds ProgramComposition

 theorem flow_program (U : Program) (K : ℝ) (timeU : Polynomial ℕ)
     (hK : 0< K) (h7 : FlowSevenContract U K timeU) :
     ∃ (M : Program) (time : Polynomial ℕ),
       ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (delta : RationalCode) (ell : ℕ),
         2≤ n → (∀v,0≤(x v).value) → 0< vertexSum (fun v => ((x v).value:ℝ)) Finset.univ →
         0< delta.value → delta.value<1 → (3*K+1)*(delta.value:ℝ)⁻¹*logTwo n≤ ell →
         ∃t,t≤ time.eval ((flowInput G x delta++encodeNat ell).length+1) ∧
           ((∃S : Finset (Fin n),Runs M (flowInput G x delta++encodeNat ell) (false::mask S) t ∧
             Light G Finset.univ S delta.value (fun v => ((x v).value:ℝ))) ∨
            ∃(W : Finset (Fin n)) (f : List (List (Fin n)×ℚ)),
              Runs M (flowInput G x delta++encodeNat ell) (true::(mask W++encodeSparsePaths f)) t ∧
              PathOutcome G (fun v => ((x v).value:ℝ)) ell W (realPaths f)) := by
   obtain ⟨Body,timeP,hBody⟩ := flow_body_program U
   obtain ⟨Repeat,hRepeat⟩ := bounded_native_iteration Body
   obtain ⟨Pre,Apre,p,hApre,hp,hPre⟩ := TreeToTM2.realizer_poly_program flowInitialInputRealizer flowInitialInput_polynomial
   obtain ⟨Post,Cpost,r,hCpost,hr,hPost⟩ := TreeToTM2.realizer_poly_program flowFinishBitsRealizer flowFinishBits_polynomial
   obtain ⟨A,q,hA,hq,hActiveSize⟩ := flow_active_size
   let Q : Polynomial ℕ := Polynomial.C A*Polynomial.X^q
   let J : Polynomial ℕ := Q+Polynomial.C (StackSpace.bound U.machine.tm)*(timeU.comp Q)
   let V : Polynomial ℕ := Polynomial.C 4*Polynomial.X+Polynomial.C 5+J
   let Clock : Polynomial ℕ := timeP.comp (timeU.comp Q+Polynomial.C 5*V+Polynomial.C 2*Q+Polynomial.C 12)
   let Reps : Polynomial ℕ := Polynomial.C 10*(Polynomial.X+Polynomial.C 1)*(Clock+V+Polynomial.C 1)
   let Init : Polynomial ℕ := Polynomial.C Apre*Polynomial.X^p
   let Finish : Polynomial ℕ := Polynomial.C Cpost*(V+Polynomial.C 1)^r
   let AB := sequence Pre Repeat
   let M := sequence AB Post
   obtain ⟨K1,hK1,hSeq1⟩ := sequence_runs_linear Pre Repeat
   obtain ⟨K2,hK2,hSeq2⟩ := sequence_runs_linear AB Post
   let Time : Polynomial ℕ := Polynomial.C K2*(Polynomial.C K1*(Init+Reps+Polynomial.X)+Finish+Polynomial.X)
   refine ⟨M,Time,?_⟩
   intro n G x delta ell hn hx hk hd hd1 hell
   let base := flowInput G x delta++encodeNat ell
   let b := base.length+1
   let F := K*n*logTwo n/(flowGammaValue x ell:ℝ)
   have hParams := flow_parameters n K (vertexSum (fun v => ((x v).value:ℝ)) Finset.univ) delta.value ell hn hK hk (by exact_mod_cast hd) hell
   dsimp only at hParams
   rw [← flowGammaValue_cast x ell] at hParams
   have hg : 0< flowGammaValue x ell := by exact_mod_cast hParams.2.1
   have hF0 : 0≤ F := hParams.2.2.1
   have hFinal : F*n≤(delta.value:ℝ)*vertexSum (fun v => ((x v).value:ℝ)) Finset.univ := hParams.2.2.2
   have hkQ := flow_total_positive x hk
   have hInput (W : Finset (Fin n)) :
       (flowInput (activeGraph G W) (inducedCodes W x) (ratCode (flowGammaValue x ell))).length+1≤ Q.eval b := by
     have hh := hActiveSize n G x delta ell false false W ∅ []
     rw [flowActivePayload_correct G x delta ell false W ∅ false [] hx hkQ] at hh
     simpa only [Q,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,flowGammaValue] using hh
   have hJ : Q.eval b+StackSpace.bound U.machine.tm*timeU.eval (Q.eval b)≤ J.eval b := by
     simp only [J,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_comp]
     rfl
   have hV : 4*((flowInput G x delta++encodeNat ell).length+1)+5+J.eval b≤ V.eval b := by
     simp only [V,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
     rfl
   have hClock : timeP.eval (timeU.eval (Q.eval b)+5*V.eval b+2*Q.eval b+12)=Clock.eval b := by
     simp only [Clock,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
   let Good := FlowGood G x delta ell F (J.eval b)
   have hStep (i : ℕ) (L : List Bool) (hGood : Good i L) :
       ∃L',Runs Body L L' (Clock.eval b) ∧ Good (i+1) L' := by
     rw [← hClock]
     exact flow_good_step U Body K timeU timeP h7 hBody hK G x delta ell F (J.eval b) (Q.eval b) (V.eval b)
       hn hx hk hg rfl hF0 hFinal hInput hJ hV i L hGood
   obtain ⟨v,hv0,hGood,hRun⟩ := good_run_sequence Body (Clock.eval b) Good (flowInitialBits base)
     (FlowGood.initial G x delta ell F (J.eval b)) hStep
   have hSizes (i : ℕ) (hi : i≤ n) : (v i).length≤ V.eval b := (FlowGood.size G x delta ell F (J.eval b) i (v i) (hGood i)).trans hV
   have hRep := hRepeat v n (Clock.eval b) (V.eval b) (fun i hi => hRun i) hSizes
   rw [hv0,← flowInitialInput_correct G x delta ell] at hRep
   have hnSize : n≤ b := flow_base_order_bound G x delta ell
   have hRepClock : 10*(n+1)*(Clock.eval b+V.eval b+1)≤ Reps.eval b := by
     simp only [Reps,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X]
     exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 10 (Nat.add_le_add_right hnSize 1))
   have hRep := NativeCompiler.runs_mono _ _ _ hRep hRepClock
   have hPreClock : Apre*(base.length+1)^p=Init.eval b := by simp only [Init,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X];rfl
   have hPreRun := hPre base
   rw [hPreClock] at hPreRun
   have hAB := hSeq1 base (flowInitialInput base) (v n) (Init.eval b) (Reps.eval b) hPreRun hRep
   have hPostRun := hPost (v n)
   have hPostClock : Cpost*((v n).length+1)^r≤ Finish.eval b := by
     simp only [Finish,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add]
     exact Nat.mul_le_mul_left Cpost (Nat.pow_le_pow_left (Nat.add_le_add_right (hSizes n le_rfl) 1) r)
   have hPostRun := NativeCompiler.runs_mono _ _ _ hPostRun hPostClock
   have hM := hSeq2 base (v n) (flowFinishBits (v n))
     (K1*(Init.eval b+Reps.eval b+base.length+1)) (Finish.eval b) hAB hPostRun
   let t := K2*(K1*(Init.eval b+Reps.eval b+base.length+1)+Finish.eval b+base.length+1)
   have hTime : t≤ Time.eval b := by
     simp only [Time,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X]
     dsimp only [t,b]
     simp only [Nat.add_assoc]
     rfl
   refine ⟨t,hTime,?_⟩
   rcases FlowGood.finish G x delta ell F (J.eval b) (v n) (hGood n) hFinal with hSep|hLaw
   · obtain ⟨S,hOut,hLight⟩ := hSep
     rw [hOut] at hM
     exact Or.inl ⟨S,hM,hLight⟩
   · obtain ⟨W,f,hOut,hPath⟩ := hLaw
     rw [hOut] at hM
     exact Or.inr ⟨W,f,hM,hPath⟩
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.Reduce_lemma_8
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.RawStack

theorem solution :
    ∃ (M : Program) (c₀ : ℝ) (time : Polynomial ℕ), 0 < c₀ ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode)
        (δ : RationalCode) (ell : ℕ),
        2 ≤ n → (∀ v, 0 ≤ (x v).value) →
        0 < vertexSum (fun v => ((x v).value : ℝ)) Finset.univ →
        0 < δ.value → δ.value < 1 → c₀ * (δ.value : ℝ)⁻¹ * logTwo n ≤ ell →
        ∃ t : ℕ, t ≤ time.eval ((flowInput G x δ ++ encodeNat ell).length + 1) ∧
          ((∃ S : Finset (Fin n),
              Runs M (flowInput G x δ ++ encodeNat ell) (false :: mask S) t ∧
              Light G Finset.univ S δ.value (fun v => ((x v).value : ℝ))) ∨
            ∃ (W : Finset (Fin n)) (f : List (List (Fin n) × ℚ)),
              Runs M (flowInput G x δ ++ encodeNat ell)
                (true :: (mask W ++ encodeSparsePaths f)) t ∧
              PathOutcome G (fun v => ((x v).value : ℝ)) ell W (realPaths f)) := by
  obtain ⟨U,K,timeU,hK,h7⟩ := EdgeSublinearMWIS.Main.lemma_7
  obtain ⟨M,time,hM⟩ := flow_program U K timeU hK h7
  exact ⟨M,3*K+1,time,by linarith,hM⟩
end
