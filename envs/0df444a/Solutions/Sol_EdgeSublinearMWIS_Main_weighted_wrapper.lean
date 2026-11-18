-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.weighted_wrapper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T21:03:47.112214+00:00
-- url     : https://prove2.me/submissions/260ea51f-7e5e-471e-8b20-5f3cd99f4380

import Mathlib.Data.Nat.Bits
import Mathlib.Tactic
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_OAIThreeMachineSched02
import Mathlib
import Definitions.Def_EdgeSublinearMWIS_Main_WeightedExecution
import Definitions.Def_EdgeSublinearMWIS_Main_WeightedReduction
import Definitions.Def_EdgeSublinearMWIS_Main_AlgorithmContracts
import Definitions.Def_EdgeSublinearMWIS_Main_BitExecution

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

-- Solutions.TreeStackCompiler
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Classical

/- Reused compiler proofs from the accepted public OAI.ThreeMachine.main_theorem
    submission, under the platform Apache-2.0 license. -/

section
-- module StackMachine
namespace OAI

section

namespace ThreeMachine.StackCompiler

theorem head_stackTape (xs : List Bool) : unsymbol (stackTape xs).head = xs.head? := by
  cases xs with
  | nil => rfl
  | cons b xs => exact unsymbol_symbol b

theorem tape_two_phases (a : Action) (xs : List Bool) :
    applyTape (phaseTwo a (middleTape a xs).head) (middleTape a xs) = stackTape (a.apply xs) := by
  cases a with
  | stay => simp [applyTape, phaseTwo, middleTape, phaseOne, Action.apply]
  | pop =>
    change (((stackTape xs).write 0).move .right).write
      (((stackTape xs).write 0).move .right).head = stackTape xs.tail
    rw [Turing.Tape.write_self]
    simp only [stackTape, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.write_mk',
      Turing.Tape.move_right_mk', Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
      blank_cons]
    cases xs <;> rfl
  | push b =>
    change (((stackTape xs).write (stackTape xs).head).move .left).write (symbol b) =
      stackTape (b :: xs)
    rw [Turing.Tape.write_self]
    simp only [stackTape, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.move_left_mk',
      Turing.Tape.write_mk', Turing.ListBlank.tail_mk,
      List.tail_nil, List.tail_cons, List.map_cons, Turing.ListBlank.cons_mk]

section Compilation
variable {k : ℕ} {Q : Type} [Fintype Q] (P : Program k Q)

theorem step_ready {c : TapeCfg (k := k) (Q := Q)} {s : State k Q}
    (h : Relates P c s) :
    (compile P).step c =
      (P.transition s.control (fun j => (s.store j).head?)).map (fun qa => middleCfg qa s.store) := by
  have ht : (fun j => unsymbol (c.tapes j).head) = fun j => (s.store j).head? := by
    funext j
    rw [h.2 j, head_stackTape]
  unfold Machine.step compile
  simp only [h.1, ht]
  cases he : P.transition s.control (fun j => (s.store j).head?) with
  | none => rfl
  | some qa =>
    apply congrArg some
    congr 1
    funext j
    dsimp only
    rw [h.2 j]
    rfl

theorem step_middle (qa : Q × Actions k) (s : Store k) :
    (compile P).step (middleCfg qa s) =
      some (readyCfg ⟨qa.1,fun j => (qa.2 j).apply (s j)⟩) := by
  unfold Machine.step compile middleCfg
  simp only [read_numberControl]
  apply congrArg some
  congr 1
  funext j
  exact tape_two_phases (qa.2 j) (s j)

theorem halted_iff {c : TapeCfg (k := k) (Q := Q)} {s : State k Q}
    (h : Relates P c s) : (compile P).step c = none ↔ P.step s = none := by
  rw [step_ready P h]
  unfold Program.step
  cases P.transition s.control (fun j => (s.store j).head?) <;> simp

theorem two_steps {c : TapeCfg (k := k) (Q := Q)} {s : State k Q}
    (h : Relates P c s) :
    Relates P ((fun d => ((compile P).step d).getD d)^[2] c) ((P.step s).getD s) := by
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [step_ready P h]
  cases he : P.transition s.control (fun j => (s.store j).head?) with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    rw [step_ready P h, he]
    simpa [Program.step, he] using h
  | some qa =>
    simp only [Option.map_some, Option.getD_some, step_middle]
    simp [Program.step, he]

theorem simulate {c : TapeCfg (k := k) (Q := Q)} {s : State k Q}
    (h : Relates P c s) (n : ℕ) :
    Relates P ((fun d => ((compile P).step d).getD d)^[2*n] c)
      ((fun d => (P.step d).getD d)^[n] s) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm (2*n) 2, Function.iterate_add_apply]
    simpa only [Function.iterate_succ_apply'] using two_steps P ih

theorem relates_initial (input : List Bool) :
    Relates P ((compile P).initial input) ⟨P.initial, initialStore input⟩ := by
  refine ⟨read_zero P, ?_⟩
  intro i
  change Turing.Tape.mk₁ (if i = 0 then input.map bitSymbol else []) =
    Turing.Tape.mk₁ ((if i = 0 then input else []).map symbol)
  split_ifs <;> rfl

theorem simulate_initial (input : List Bool) (n : ℕ) :
    Relates P ((compile P).run input (2*n)) (P.run (initialStore input) n) :=
  simulate P (relates_initial P input) n

theorem compile_produces (input out : List Bool) (bound : ℕ)
    (h : ∃ n ≤ bound, P.step (P.run (initialStore input) n) = none ∧
      (P.run (initialStore input) n).store 0 = out) :
    (compile P).Produces input out (2*bound) := by
  obtain ⟨n,hn,hh,ho⟩ := h
  have hs := simulate_initial P input n
  refine ⟨2*n, by omega, (halted_iff P hs).mpr hh, ?_⟩
  rw [hs.2 0, ho]
  exact Turing.Tape.mk'_right₀ _ _

end Compilation
namespace Program
variable {k : ℕ} {Q R S : Type}

theorem Exec.iterate {P : Program k Q} {s t : State k Q} {n : ℕ}
    (h : Exec P s n t) : (fun c => (P.step c).getD c)^[n] s = t := by
  induction h with
  | halt => rfl
  | next he _ ih => simpa only [Function.iterate_succ_apply, he, Option.getD_some] using ih

theorem Exec.halted {P : Program k Q} {s t : State k Q} {n : ℕ}
    (h : Exec P s n t) : P.step t = none := by
  induction h with
  | halt h => exact h
  | next _ _ ih => exact ih

theorem Exec.continue {P : Program k Q} {P' : Program k R} (f : Q → R)
    (hs : ∀ s t, P.step s = some t →
      P'.step (State.mapControl f s) = some (State.mapControl f t))
    {s t : State k Q} {u : State k R} {n m : ℕ} (h : Exec P s n t)
    (ht : Exec P' (State.mapControl f t) m u) :
    Exec P' (State.mapControl f s) (n+m) u := by
  induction h with
  | halt => simpa only [Nat.zero_add] using ht
  | next he _ ih => simpa only [Nat.add_right_comm] using Exec.next (hs _ _ he) (ih ht)

theorem lift_step (P : Program k Q) (P' : Program k R) (f : Q → R)
    (h : ∀ q heads q' a, P.transition q heads = some (q',a) →
      P'.transition (f q) heads = some (f q',a))
    (s t : State k Q) (he : P.step s = some t) :
    P'.step (State.mapControl f s) = some (State.mapControl f t) := by
  unfold step at he
  cases hh : P.transition s.control (fun i => (s.store i).head?) with
  | none => simp [hh] at he
  | some qa =>
    have het : t = ⟨qa.1,fun i => (qa.2 i).apply (s.store i)⟩ := by
      simpa [hh] using he.symm
    subst t
    simp [step, State.mapControl, h _ _ _ _ hh]

theorem seq_left_step (P : Program k Q) (P' : Program k R)
    (s t : State k Q) (h : P.step s = some t) :
    (seq P P').step (State.mapControl Sum.inl s) = some (State.mapControl Sum.inl t) := by
  apply lift_step P (seq P P') Sum.inl _ s t h
  intro q heads q' a ha
  simp [seq,ha]

theorem seq_right_exec (P : Program k Q) {P' : Program k R}
    {s t : State k R} {n : ℕ} (h : Exec P' s n t) :
    Exec (seq P P') (State.mapControl Sum.inr s) n (State.mapControl Sum.inr t) := by
  induction h with
  | halt he =>
    apply Exec.halt
    unfold step at he ⊢
    cases hh : P'.transition s.control (fun i => (s.store i).head?) <;> simp_all [seq,State.mapControl]
  | next he _ ih =>
    apply Exec.next _ ih
    apply lift_step P' (seq P P') Sum.inr _ _ _ he
    intro q heads q' a ha
    simp [seq, ha]

theorem seq_exec {P : Program k Q} {P' : Program k R} {s t : Store k}
    {q : Q} {r : R} {n m : ℕ} (h : Exec P ⟨P.initial,s⟩ n ⟨q,t⟩)
    {u : Store k} (h' : Exec P' ⟨P'.initial,t⟩ m ⟨r,u⟩) :
    Exec (seq P P') ⟨(seq P P').initial,s⟩ (n+m+1) ⟨Sum.inr r,u⟩ := by
  have hh := h.halted
  have hs : (seq P P').step ⟨Sum.inl q,t⟩ = some ⟨Sum.inr P'.initial,t⟩ := by
    unfold step at hh ⊢
    cases ht : P.transition q (fun i => (t i).head?) <;> simp_all [seq, stayActions,Action.apply]
  have hx := h.continue Sum.inl (seq_left_step P P') (Exec.next hs (seq_right_exec P h'))
  simpa only [State.mapControl, seq, Nat.add_assoc] using hx

theorem instruction_exec (a : Heads k → Actions k) (s : Store k) :
    Exec (instruction a) ⟨false,s⟩ 1
      ⟨true,fun i => (a (fun j => (s j).head?) i).apply (s i)⟩ := by
  apply Exec.next (by rfl)
  exact Exec.halt rfl

theorem loop_body_step (test : Heads k → Bool) (P : Program k Q)
    (s t : State k Q) (h : P.step s = some t) :
    (loop test P).step (State.mapControl some s) = some (State.mapControl some t) := by
  apply lift_step P (loop test P) some _ s t h
  intro q heads q' a ha
  simp [loop,ha]

theorem loop_stop (test : Heads k → Bool) (P : Program k Q) (s : Store k)
    (h : test (fun i => (s i).head?) = false) :
    Exec (loop test P) ⟨none,s⟩ 0 ⟨none,s⟩ := by
  exact Exec.halt (by simp [step,loop,h])

theorem loop_iterate (test : Heads k → Bool) {P : Program k Q} {s t u : Store k}
    {q : Q} {n m : ℕ} (hs : test (fun i => (s i).head?) = true)
    (h : Exec P ⟨P.initial,s⟩ n ⟨q,t⟩)
    (hrest : Exec (loop test P) ⟨none,t⟩ m ⟨none,u⟩) :
    Exec (loop test P) ⟨none,s⟩ (n+m+2) ⟨none,u⟩ := by
  have hstart : (loop test P).step ⟨none,s⟩ = some ⟨some P.initial,s⟩ := by
    simp [step,loop,hs,stayActions,Action.apply]
  have hhalt := h.halted
  have hend : (loop test P).step ⟨some q,t⟩ = some ⟨none,t⟩ := by
    unfold step at hhalt ⊢
    cases ht : P.transition q (fun i => (t i).head?) <;>
      simp_all [loop,stayActions,Action.apply]
  have hb := h.continue some (loop_body_step test P) (Exec.next hend hrest)
  convert Exec.next hstart hb using 1
  omega

end Program
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
namespace Program
variable {k : ℕ}

theorem transfer_instruction {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (xs : List Bool) (s : Store k) (hs : s src = b :: xs) :
    Exec (instruction (transferActions src dst)) ⟨false,s⟩ 1
      ⟨true,transferOnce src dst b xs s⟩ := by
  have h := instruction_exec (transferActions src dst) s
  convert h using 1
  congr 1
  funext i
  by_cases hi : i = src
  · subst i
    simp [transferOnce, transferActions, hne, hs, Action.apply]
  · by_cases hd : i = dst
    · subst i
      simp [transferOnce, transferActions, hne.symm, hs, Action.apply]
    · simp [transferOnce, transferActions,hi,hd,Action.apply]

theorem transfer_result_once {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (xs : List Bool) (s : Store k) (hs : s src = b::xs) :
    transferResult src dst (transferOnce src dst b xs s) = transferResult src dst s := by
  funext i
  by_cases hi : i = dst
  · subst i
    simp [transferResult,transferOnce,hne,hs,List.reverse_cons,List.append_assoc]
  · by_cases hsrc : i = src
    · subst i
      simp [transferResult,transferOnce,hne]
    · simp [transferResult,transferOnce,hi,hsrc]

theorem transfer_exec {src dst : Fin (k+1)} (hne : src ≠ dst) (s : Store k) :
    Exec (transfer src dst) ⟨none,s⟩ (3*(s src).length) ⟨none,transferResult src dst s⟩ := by
  generalize he : s src = xs
  induction xs generalizing s with
  | nil =>
    have hr : transferResult src dst s = s := by
      funext i
      by_cases hd : i = dst
      · subst i; simp [transferResult,he]
      · by_cases hs : i = src
        · subst i; simp [transferResult,he,hne]
        · simp [transferResult,hd,hs]
    rw [hr]
    exact loop_stop _ _ s (by simp [he])
  | cons b xs ih =>
    let s' := transferOnce src dst b xs s
    have hs' : s' src = xs := by simp [s',transferOnce,hne]
    have hrest := ih s' hs'
    rw [transfer_result_once hne b xs s he] at hrest
    have hbody := transfer_instruction hne b xs s he
    have hx := loop_iterate (fun h => (h src).isSome) (by simp [he]) hbody hrest
    convert hx using 1 <;> first | rfl | simp only [List.length_cons]; omega

end Program
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ}

theorem pop_instruction (src : Fin (k+1)) (s : Store k) :
    Exec (instruction (fun _ => popActions src)) ⟨false,s⟩ 1
      ⟨true,Function.update s src (s src).tail⟩ := by
  convert instruction_exec (fun _ => popActions src) s using 1
  congr 1
  funext i
  by_cases h : i = src <;> simp [popActions,Action.apply,h]

theorem clear_exec (src : Fin (k+1)) (s : Store k) :
    Exec (clear src) ⟨none,s⟩ (3*(s src).length) ⟨none,Function.update s src []⟩ := by
  generalize he : s src = xs
  induction xs generalizing s with
  | nil =>
    have hr : Function.update s src [] = s := by rw [← he]; exact Function.update_eq_self _ _
    rw [hr]
    exact loop_stop _ _ s (by simp [he])
  | cons b xs ih =>
    let s' := Function.update s src xs
    have hrest := ih s' (by simp [s'])
    have hu : Function.update s' src [] = Function.update s src [] := by simp [s']
    rw [hu] at hrest
    have hbody : Exec (instruction (fun _ => popActions src)) ⟨false,s⟩ 1 ⟨true,s'⟩ := by
      simpa only [he,List.tail_cons] using pop_instruction src s
    have hx := loop_iterate (fun h => (h src).isSome) (by simp [he]) hbody hrest
    convert hx using 1 <;> first | rfl | simp only [List.length_cons]; omega

theorem spread_instruction {src dst₁ dst₂ : Fin (k+1)}
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₃ : dst₁ ≠ dst₂)
    (b : Bool) (xs : List Bool) (s : Store k) (hs : s src = b :: xs) :
    Exec (instruction (spreadActions src dst₁ dst₂)) ⟨false,s⟩ 1
      ⟨true,spreadOnce src dst₁ dst₂ b xs s⟩ := by
  convert instruction_exec (spreadActions src dst₁ dst₂) s using 1
  congr 1
  funext i
  by_cases hi : i = src
  · subst i; simp [spreadOnce,spreadActions,h₁,h₂,hs,Action.apply]
  · by_cases hdi : i = dst₁
    · subst i; simp [spreadOnce,spreadActions,h₁.symm,h₃,hs,Action.apply]
    · by_cases hdj : i = dst₂
      · subst i; simp [spreadOnce,spreadActions,h₂.symm,hs,Action.apply]
      · simp [spreadOnce,spreadActions,hi,hdi,hdj,Action.apply]

theorem spread_result_once {src dst₁ dst₂ : Fin (k+1)}
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₃ : dst₁ ≠ dst₂)
    (b : Bool) (xs : List Bool) (s : Store k) (hs : s src = b::xs) :
    spreadResult src dst₁ dst₂ (spreadOnce src dst₁ dst₂ b xs s) = spreadResult src dst₁ dst₂ s := by
  funext i
  by_cases hi : i = dst₂
  · subst i
    simp [spreadResult,spreadOnce,h₁,h₂,hs,List.reverse_cons,List.append_assoc]
  · by_cases hd : i = dst₁
    · subst i
      simp [spreadResult,spreadOnce,h₁,h₂,h₃,hs,List.reverse_cons,List.append_assoc]
    · by_cases hsrc : i = src
      · subst i; simp [spreadResult,spreadOnce,h₁,h₂]
      · simp [spreadResult,spreadOnce,hi,hd,hsrc]

theorem spread_exec {src dst₁ dst₂ : Fin (k+1)}
    (h₁ : src ≠ dst₁) (h₂ : src ≠ dst₂) (h₃ : dst₁ ≠ dst₂) (s : Store k) :
    Exec (spread src dst₁ dst₂) ⟨none,s⟩ (3*(s src).length) ⟨none,spreadResult src dst₁ dst₂ s⟩ := by
  generalize he : s src = xs
  induction xs generalizing s with
  | nil =>
    have hr : spreadResult src dst₁ dst₂ s = s := by
      funext i
      by_cases hd₂ : i = dst₂
      · subst i; simp [spreadResult,he]
      · by_cases hd₁ : i = dst₁
        · subst i; simp [spreadResult,he,h₃]
        · by_cases hs : i = src
          · subst i; simp [spreadResult,he,h₁,h₂]
          · simp [spreadResult,hd₁,hd₂,hs]
    rw [hr]
    exact loop_stop _ _ s (by simp [he])
  | cons b xs ih =>
    let s' := spreadOnce src dst₁ dst₂ b xs s
    have hs' : s' src = xs := by simp [s',spreadOnce,h₁,h₂]
    have hrest := ih s' hs'
    rw [spread_result_once h₁ h₂ h₃ b xs s he] at hrest
    have hbody := spread_instruction h₁ h₂ h₃ b xs s he
    have hx := loop_iterate (fun h => (h src).isSome) (by simp [he]) hbody hrest
    convert hx using 1 <;> first | rfl | simp only [List.length_cons]; omega

theorem prepend_exec {src dst tmp : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ tmp) (h₃ : dst ≠ tmp)
    (s : Store k) (htmp : s tmp = []) :
    Exec (prepend src dst tmp) ⟨(prepend src dst tmp).initial,s⟩
      (6*(s src).length+1) ⟨Sum.inr none,Function.update s dst (s src ++ s dst)⟩ := by
  have hx := seq_exec (transfer_exec h₂ s)
    (spread_exec h₂.symm h₃.symm h₁ (transferResult src tmp s))
  have hl : (transferResult src tmp s tmp).length = (s src).length := by simp [transferResult,htmp]
  have he : spreadResult tmp src dst (transferResult src tmp s) =
      Function.update s dst (s src ++ s dst) := by
    funext i
    by_cases hd : i = dst
    · subst i; simp [spreadResult,transferResult,htmp,h₃,h₁.symm]
    · by_cases hsrc : i = src
      · subst i; simp [spreadResult,transferResult,htmp,h₂,h₁]
      · by_cases ht : i = tmp
        · subst i; simp [spreadResult,transferResult,htmp,h₂.symm,h₃.symm]
        · simp [spreadResult,transferResult,hd,hsrc,ht]
  rw [he,hl] at hx
  convert hx using 1 <;> first | rfl | omega

end ThreeMachine.StackCompiler.Program

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ}

theorem copy_exec {src dst tmp : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ tmp) (h₃ : dst ≠ tmp)
    (s : Store k) (htmp : s tmp = []) :
    Exec (copy src dst tmp) ⟨(copy src dst tmp).initial,s⟩
      (3*(s dst).length+6*(s src).length+2)
      ⟨Sum.inr (Sum.inr none),Function.update s dst (s src)⟩ := by
  have hx := seq_exec (clear_exec dst s)
    (prepend_exec h₁ h₂ h₃ (Function.update s dst []) (by simp [h₃.symm,htmp]))
  simpa [copy,h₁,Nat.add_assoc] using hx

end ThreeMachine.StackCompiler.Program

end

end OAI
end

section
-- module TreeData
namespace OAI

section

namespace ThreeMachine.StackCompiler

namespace Data

end Data

namespace Program
variable {k : ℕ}

theorem scan_instruction {src dst ct : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ ct) (h₃ : dst ≠ ct)
    (s : Store k) (b : Bool) (rest : List Bool) (hs : s src = b :: rest) :
    Exec (instruction (scanActions src dst ct)) ⟨false,s⟩ 1 ⟨true,scanOnce src dst ct s b rest⟩ := by
  convert instruction_exec (scanActions src dst ct) s using 1
  congr 1
  funext i
  by_cases hi : i = ct
  · subst i; cases b <;> simp [scanActions,scanOnce,hs,h₂.symm,h₃.symm,Action.apply]
  · by_cases hd : i = dst
    · subst i; simp [scanActions,scanOnce,hs,hi,h₁.symm,Action.apply]
    · by_cases hsrc : i = src
      · subst i; simp [scanActions,scanOnce,hs,h₁,h₂,Action.apply]
      · simp [scanActions,scanOnce,hi,hd,hsrc,Action.apply]

theorem scanned_scanned {src dst ct : Fin (k+1)}
    (h₃ : dst ≠ ct) (s : Store k) (rest mid w₁ w₂ : List Bool) (c d : ℕ) :
    scanned src dst ct (scanned src dst ct s mid w₁ d) rest w₂ c =
      scanned src dst ct s rest (w₁ ++ w₂) c := by
  funext i
  by_cases hc : i = ct
  · subst i; simp [scanned]
  · by_cases hd : i = dst
    · subst i; simp [scanned,h₃,List.reverse_append,List.append_assoc]
    · by_cases hs : i = src
      · subst i; simp [scanned,hc,hd]
      · simp [scanned,hc,hd,hs]

theorem scan_tree_continue {src dst ct : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ ct) (h₃ : dst ≠ ct) (d : Data) :
    ∀ (s t : Store k) (rest : List Bool) (c m : ℕ),
      s src = d.encode ++ rest → s ct = List.replicate (c+1) true →
      Exec (scan src dst ct) ⟨none,scanned src dst ct s rest d.encode c⟩ m ⟨none,t⟩ →
      Exec (scan src dst ct) ⟨none,s⟩ (3*d.size+m) ⟨none,t⟩ := by
  induction d with
  | nil =>
    intro s t rest c m hs hc hrest
    have hsrc : s src = false :: rest := by simpa using hs
    have he : scanOnce src dst ct s false rest = scanned src dst ct s rest [false] c := by
      simp [scanOnce,scanned,hc,List.replicate_succ]
    have hbody := scan_instruction h₁ h₂ h₃ s false rest hsrc
    rw [he] at hbody
    have hx := loop_iterate (fun h => (h ct).isSome) (by simp [hc,List.replicate_succ]) hbody hrest
    convert hx using 1 <;> first | rfl | simp only [Data.size_nil]; omega
  | pair a b iha ihb =>
    intro s t rest c m hs hc hrest
    let s₁ := scanOnce src dst ct s true (a.encode ++ b.encode ++ rest)
    have hs₁ : s₁ src = a.encode ++ (b.encode ++ rest) := by
      simp [s₁,scanOnce,h₁,h₂,List.append_assoc]
    have hc₁ : s₁ ct = List.replicate (c+2) true := by
      simp [s₁,scanOnce,hc,List.replicate_succ]
    let s₂ := scanned src dst ct s₁ (b.encode ++ rest) a.encode (c+1)
    have hs₂ : s₂ src = b.encode ++ rest := by simp [s₂,scanned,h₁,h₂]
    have hc₂ : s₂ ct = List.replicate (c+1) true := by simp [s₂,scanned]
    have hend : scanned src dst ct s₂ rest b.encode c =
        scanned src dst ct s rest (Data.pair a b).encode c := by
      rw [show s₂ = scanned src dst ct s₁ (b.encode ++ rest) a.encode (c+1) by rfl,
        scanned_scanned h₃]
      funext i
      by_cases hi : i = ct
      · subst i; simp [scanned]
      · by_cases hd : i = dst
        · subst i; simp [scanned,s₁,scanOnce,h₃,List.reverse_cons,List.reverse_append,
            Data.encode,List.append_assoc]
        · by_cases hsrc : i = src
          · subst i; simp [scanned,hi,hd]
          · simp [scanned,s₁,scanOnce,hi,hd,hsrc]
    have hafterB := ihb s₂ t rest c m hs₂ hc₂ (by rwa [hend])
    have hafterA := iha s₁ t (b.encode ++ rest) (c+1) (3*b.size+m) hs₁ hc₁ hafterB
    have hsrc : s src = true :: (a.encode ++ b.encode ++ rest) := by
      simpa [Data.encode,List.append_assoc] using hs
    have hbody := scan_instruction h₁ h₂ h₃ s true _ hsrc
    have hx := loop_iterate (fun h => (h ct).isSome) (by simp [hc,List.replicate_succ]) hbody hafterA
    convert hx using 1 <;> first | rfl | rw [Data.size_pair]; omega

theorem scan_tree {src dst ct : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ ct) (h₃ : dst ≠ ct)
    (d : Data) (s : Store k) (rest : List Bool)
    (hs : s src = d.encode ++ rest) (hc : s ct = [true]) :
    Exec (scan src dst ct) ⟨none,s⟩ (3*d.size)
      ⟨none,scanned src dst ct s rest d.encode 0⟩ := by
  have hstop : Exec (scan src dst ct) ⟨none,scanned src dst ct s rest d.encode 0⟩ 0
      ⟨none,scanned src dst ct s rest d.encode 0⟩ :=
    loop_stop _ _ _ (by simp [scanned])
  simpa using scan_tree_continue h₁ h₂ h₃ d s _ rest 0 0 hs (by simpa using hc) hstop

end Program
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ} {Q R : Type}

theorem Exec.runs {P : Program k Q} {s t : Store k} {n : ℕ} {q : Q}
    (h : Exec P ⟨P.initial,s⟩ n ⟨q,t⟩) : P.Runs s t n := ⟨n,le_rfl,q,h⟩

theorem Runs.mono {P : Program k Q} {s t : Store k} {n m : ℕ}
    (h : P.Runs s t n) (hnm : n ≤ m) : P.Runs s t m := by
  obtain ⟨t',ht',q,hq⟩ := h
  exact ⟨t',ht'.trans hnm,q,hq⟩

theorem Runs.computes {P : Program k Q} {s t : Store k} {n : ℕ}
    (h : P.Runs s t n) : P.Computes s t n := by
  obtain ⟨m,hm,q,hq⟩ := h
  refine ⟨m,hm,?_,?_⟩
  · exact congrArg State.store hq.iterate
  · unfold run
    rw [hq.iterate]
    exact hq.halted

theorem Runs.seq {P : Program k Q} {P' : Program k R} {s t u : Store k} {n m : ℕ}
    (h : P.Runs s t n) (h' : P'.Runs t u m) : (seq P P').Runs s u (n+m+1) := by
  obtain ⟨n',hn',q,hq⟩ := h
  obtain ⟨m',hm',r,hr⟩ := h'
  exact (seq_exec hq hr).runs.mono (by omega)

theorem branch_left_exec (test : Heads k → Bool) {P : Program k Q} (P' : Program k R)
    {s t : State k Q} {n : ℕ} (h : Exec P s n t) :
    Exec (branch test P P') (State.mapControl (some ∘ Sum.inl) s) n
      (State.mapControl (some ∘ Sum.inl) t) := by
  induction h with
  | halt he =>
    apply Exec.halt
    unfold step at he ⊢
    cases hh : P.transition s.control (fun i => (s.store i).head?) <;>
      simp_all [branch,State.mapControl]
  | next he _ ih =>
    apply Exec.next _ ih
    apply lift_step P (branch test P P') (some ∘ Sum.inl) _ _ _ he
    intro q heads q' a ha
    simp [branch,ha]

theorem branch_right_exec (test : Heads k → Bool) (P : Program k Q) {P' : Program k R}
    {s t : State k R} {n : ℕ} (h : Exec P' s n t) :
    Exec (branch test P P') (State.mapControl (some ∘ Sum.inr) s) n
      (State.mapControl (some ∘ Sum.inr) t) := by
  induction h with
  | halt he =>
    apply Exec.halt
    unfold step at he ⊢
    cases hh : P'.transition s.control (fun i => (s.store i).head?) <;>
      simp_all [branch,State.mapControl]
  | next he _ ih =>
    apply Exec.next _ ih
    apply lift_step P' (branch test P P') (some ∘ Sum.inr) _ _ _ he
    intro q heads q' a ha
    simp [branch,ha]

theorem Runs.branch_left (test : Heads k → Bool) {P : Program k Q} (P' : Program k R)
    {s t : Store k} {n : ℕ} (h : P.Runs s t n) (ht : test (fun i => (s i).head?) = true) :
    (branch test P P').Runs s t (n+1) := by
  obtain ⟨m,hm,q,hq⟩ := h
  have hs : (branch test P P').step ⟨none,s⟩ = some ⟨some (.inl P.initial),s⟩ := by
    simp [step,branch,ht,stayActions,Action.apply]
  exact ⟨m+1,by omega,some (.inl q),Exec.next hs (branch_left_exec test P' hq)⟩

theorem Runs.branch_right (test : Heads k → Bool) (P : Program k Q) {P' : Program k R}
    {s t : Store k} {n : ℕ} (h : P'.Runs s t n) (ht : test (fun i => (s i).head?) = false) :
    (branch test P P').Runs s t (n+1) := by
  obtain ⟨m,hm,q,hq⟩ := h
  have hs : (branch test P P').step ⟨none,s⟩ = some ⟨some (.inr P'.initial),s⟩ := by
    simp [step,branch,ht,stayActions,Action.apply]
  exact ⟨m+1,by omega,some (.inr q),Exec.next hs (branch_right_exec test P hq)⟩

theorem move_exec {src dst tmp : Fin (k+1)}
    (h₁ : src ≠ dst) (h₂ : src ≠ tmp) (h₃ : dst ≠ tmp)
    (s : Store k) (htmp : s tmp = []) :
    Exec (move src dst tmp) ⟨(move src dst tmp).initial,s⟩
      (3*(s dst).length+6*(s src).length+2)
      ⟨Sum.inr (Sum.inr none),Function.update (Function.update s src []) dst (s src)⟩ := by
  let s₁ := Function.update s dst []
  let s₂ := transferResult src tmp s₁
  have hx := seq_exec (clear_exec dst s)
    (seq_exec (transfer_exec h₂ s₁) (transfer_exec h₃.symm s₂))
  have hl₁ : s₁ src = s src := by simp [s₁,h₁]
  have hl₂ : (s₂ tmp).length = (s src).length := by simp [s₂,s₁,transferResult,h₁,h₃.symm,htmp]
  have he : transferResult tmp dst s₂ = Function.update (Function.update s src []) dst (s src) := by
    funext i
    by_cases hd : i = dst
    · subst i; simp [transferResult,s₂,s₁,h₃,h₃.symm,htmp,h₁,h₁.symm]
    · by_cases ht : i = tmp
      · subst i; simp [transferResult,s₂,s₁,h₃.symm,htmp,h₁,h₂.symm]
      · by_cases hsrc : i = src
        · subst i; simp [transferResult,s₂,s₁,h₁,h₂]
        · simp [transferResult,s₂,s₁,hd,ht,hsrc]
  rw [he,hl₁,hl₂] at hx
  convert hx using 1 <;> first | rfl | omega

end ThreeMachine.StackCompiler.Program

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ}

theorem push_exec (dst : Fin (k+1)) (b : Bool) (s : Store k) :
    Exec (push dst b) ⟨false,s⟩ 1 ⟨true,Function.update s dst (b :: s dst)⟩ := by
  have he : (fun i => (if i = dst then Action.push b else Action.stay).apply (s i)) =
      Function.update s dst (b :: s dst) := by
    funext i
    by_cases hi : i = dst <;> simp [hi,Action.apply]
  simpa only [push,he] using instruction_exec (fun _ i => if i = dst then .push b else .stay) s

theorem setNil_runs (dst : Fin (k+1)) (s : Store k) :
    (setNil dst).Runs s (Function.update s dst Data.nil.encode) (3*(s dst).length+2) := by
  have h := (clear_exec dst s).runs.seq (push_exec dst false (Function.update s dst [])).runs
  simpa [setNil] using h

theorem setPair_runs {dst a b tmp buf : Fin (k+1)}
    (hd : dst ≠ tmp) (hd' : dst ≠ buf) (ha : a ≠ tmp) (ha' : a ≠ buf)
    (hb : b ≠ tmp) (hb' : b ≠ buf) (htb : tmp ≠ buf)
    (s : Store k) (ht : s tmp = []) (hu : s buf = []) :
    (setPair dst a b tmp buf).Runs s
      (Function.update s dst (true :: (s a ++ s b)))
      (12*(s a).length+12*(s b).length+3*(s dst).length+14) := by
  let s₁ := Function.update s tmp (s b)
  let s₂ := Function.update s tmp (s a ++ s b)
  let s₃ := Function.update s tmp (true :: (s a ++ s b))
  have h₁ : (prepend b tmp buf).Runs s s₁ (6*(s b).length+1) := by
    simpa [s₁,ht] using (prepend_exec hb hb' htb s hu).runs
  have h₂ : (prepend a tmp buf).Runs s₁ s₂ (6*(s a).length+1) := by
    have hh := (prepend_exec ha ha' htb s₁ (by simp [s₁,htb.symm,hu])).runs
    simpa [s₁,s₂,ha] using hh
  have h₃ : (push tmp true).Runs s₂ s₃ 1 := by
    simpa [s₂,s₃] using (push_exec tmp true s₂).runs
  have h₄ : (move tmp dst buf).Runs s₃ (Function.update s dst (true :: (s a ++ s b)))
      (3*(s dst).length+6*((s a).length+(s b).length+1)+2) := by
    have hh := (move_exec hd.symm htb hd' s₃ (by simp [s₃,htb.symm,hu])).runs
    have he : Function.update s₃ tmp [] = s := by
      ext i
      by_cases hi : i = tmp <;> simp [s₃,hi,ht]
    rw [he] at hh
    simpa [s₃,hd] using hh
  exact (h₁.seq (h₂.seq (h₃.seq h₄))).mono (by omega)

end ThreeMachine.StackCompiler.Program

end

end OAI
end

section
-- module RegisterMachine
namespace OAI

section

namespace ThreeMachine.StackCompiler

attribute [instance] Packed.finiteControl

namespace Packed
variable {k : ℕ}

theorem Runs.seq {P P' : Packed k} {s t u : Store k} {n m : ℕ}
    (h : P.Runs s t n) (h' : P'.Runs t u m) : (P.seq P').Runs s u (n+m+1) :=
  Program.Runs.seq h h'

theorem Runs.mono {P : Packed k} {s t : Store k} {n m : ℕ}
    (h : P.Runs s t n) (hnm : n ≤ m) : P.Runs s t m := Program.Runs.mono h hnm

end Packed

namespace Tree
variable {r : ℕ}

theorem memory_update (s : Registers r) (dst : Fin r) (d : Data) :
    memory (Function.update s dst d) = Function.update (memory s) (reg dst) d.encode := by
  funext i
  refine Fin.addCases (m := r) (n := 4) (fun i => ?_) (fun i => ?_) i
  · change memory _ (reg i) = Function.update (memory s) (reg dst) d.encode (reg i)
    by_cases hi : i = dst <;> simp [hi]
  · change memory _ (temp i) = Function.update (memory s) (reg dst) d.encode (temp i)
    simp

theorem nil_runs (dst : Fin r) (s : Registers r) :
    (nil dst).Runs (memory s) (memory (Function.update s dst .nil)) (3*(s dst).size+2) := by
  rw [memory_update]
  simpa only [nil,Packed.Runs,Packed.ofProgram,memory_reg,Data.size] using Program.setNil_runs (reg dst) (memory s)

theorem pair_runs (dst a b : Fin r) (s : Registers r) :
    (pair dst a b).Runs (memory s) (memory (Function.update s dst (.pair (s a) (s b))))
      (12*(s a).size+12*(s b).size+3*(s dst).size+14) := by
  rw [memory_update]
  simpa only [pair,Packed.Runs,Packed.ofProgram,memory_reg,Data.size,Data.encode_pair,List.cons_append] using
    Program.setPair_runs (dst := reg dst) (a := reg a) (b := reg b) (tmp := temp 0) (buf := temp 1)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (memory s) (by simp) (by simp)

end Tree
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Tree
variable {r : ℕ}

theorem work_update_temp (s : Registers r) (t : Fin 4 → List Bool) (i : Fin 4) (word : List Bool) :
    Function.update (work s t) (temp i) word = work s (Function.update t i word) := by
  funext j
  refine Fin.addCases (m := r) (n := 4) (fun j => ?_) (fun j => ?_) j
  · change Function.update (work s t) (temp i) word (reg j) = work _ _ (reg j)
    simp
  · change Function.update (work s t) (temp i) word (temp j) = work _ _ (temp j)
    by_cases hj : j = i <;> simp [hj]

theorem selectFinish_runs (head : Bool) (s : Registers r) (a b : Data) :
    (selectFinish head).Runs (work s ![b.encode,[],a.encode.reverse,[]])
      (work s ![(if head then a else b).encode,[],[],[]]) (3*a.size+3*b.size+2) := by
  cases head with
  | false =>
    have h₁ := (Program.clear_exec (temp 2) (work s ![b.encode,[],a.encode.reverse,[]])).runs
    rw [work_update_temp] at h₁
    have he : Function.update ![b.encode,[],a.encode.reverse,[]] (2 : Fin 4) [] = ![b.encode,[],[],[]] := by
      funext i; fin_cases i <;> simp
    rw [he] at h₁
    have h₂ := (Program.clear_exec (temp 2) (work s ![b.encode,[],[],[]])).runs
    rw [work_update_temp] at h₂
    have he₂ : Function.update ![b.encode,[],[],[]] (2 : Fin 4) [] = ![b.encode,[],[],[]] := by
      funext i; fin_cases i <;> simp
    rw [he₂] at h₂
    have hx := h₁.seq h₂
    exact hx.mono (by simp [Data.size]; omega)
  | true =>
    have h₁ := (Program.clear_exec (temp 0) (work s ![b.encode,[],a.encode.reverse,[]])).runs
    rw [work_update_temp] at h₁
    have he : Function.update ![b.encode,[],a.encode.reverse,[]] (0 : Fin 4) [] = ![[],[],a.encode.reverse,[]] := by
      funext i; fin_cases i <;> simp
    rw [he] at h₁
    have h₂ := (Program.transfer_exec (show (temp 2 : Fin (r+4)) ≠ temp 0 by simp)
      (work s ![[],[],a.encode.reverse,[]])).runs
    have he₂ : Program.transferResult (temp 2) (temp 0) (work s ![[],[],a.encode.reverse,[]]) =
        work s ![a.encode,[],[],[]] := by
      simp only [Program.transferResult,work_temp,Matrix.cons_val_two,Matrix.cons_val_zero,
        List.append_nil,work_update_temp]
      congr 1
      funext i; fin_cases i <;> simp
    rw [he₂] at h₂
    exact (h₁.seq h₂).mono (by simp [Data.size]; omega)

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Tree
variable {r : ℕ}

theorem selectPair_runs (head : Bool) (dst : Fin r) (s : Registers r) (a b : Data) :
    (selectPair head dst).Runs (work s ![(Data.pair a b).encode,[],[],[]])
      (memory (Function.update s dst (if head then a else b)))
      (30*(a.size+b.size+(s dst).size+1)) := by
  let s₀ := work s ![(Data.pair a b).encode,[],[],[]]
  let s₁ := work s ![a.encode++b.encode,[],[],[]]
  let s₂ := work s ![a.encode++b.encode,[],[],[true]]
  let s₃ := work s ![b.encode,[],a.encode.reverse,[]]
  let s₄ := work s ![(if head then a else b).encode,[],[],[]]
  have h₁ : (Packed.ofProgram (Program.instruction (fun _ => Program.popActions (temp 0)))).Runs s₀ s₁ 1 := by
    have hh := (Program.pop_instruction (temp 0) s₀).runs
    have he : Function.update s₀ (temp 0) (s₀ (temp 0)).tail = s₁ := by
      simp only [s₀,s₁,work_temp,Matrix.cons_val_zero,Data.encode_pair,work_update_temp]
      congr 1
      funext i; fin_cases i <;> simp
    rwa [he] at hh
  have h₂ : (Packed.ofProgram (Program.push (temp 3) true)).Runs s₁ s₂ 1 := by
    have hh := (Program.push_exec (temp 3) true s₁).runs
    have he : Function.update s₁ (temp 3) (true :: s₁ (temp 3)) = s₂ := by
      simp only [s₁,s₂,work_temp,Matrix.cons_val_three,work_update_temp]
      congr 1
      funext i; fin_cases i <;> simp
    rwa [he] at hh
  have h₃ : (Packed.ofProgram (Program.scan (temp 0) (temp 2) (temp 3))).Runs s₂ s₃ (3*a.size) := by
    have hh := (Program.scan_tree (src := temp 0) (dst := temp 2) (ct := temp 3)
      (by simp) (by simp) (by simp) a s₂ b.encode (by simp [s₂]) (by simp [s₂])).runs
    have he : Program.scanned (temp 0) (temp 2) (temp 3) s₂ b.encode a.encode 0 = s₃ := by
      simp only [Program.scanned,s₂,s₃,work_temp,Matrix.cons_val_two,
        List.replicate_zero,work_update_temp]
      congr 1
      funext i; fin_cases i <;> simp
    rwa [he] at hh
  have h₄ : (selectFinish head).Runs s₃ s₄ (3*a.size+3*b.size+2) :=
    selectFinish_runs head s a b
  have h₅ : (Packed.ofProgram (Program.move (temp 0) (reg dst) (temp 1))).Runs s₄
      (memory (Function.update s dst (if head then a else b)))
      (3*(s dst).size+6*(if head then a else b).size+2) := by
    have hh := (Program.move_exec (src := temp 0) (dst := reg dst) (tmp := temp 1)
      (by simp) (by simp) (by simp) s₄ (by simp [s₄])).runs
    have he : Function.update s₄ (temp 0) [] = memory s := by
      simp only [s₄,work_update_temp]
      have hw : Function.update ![(if head then a else b).encode,[],[],[]] (0 : Fin 4) [] = ![[],[],[],[]] := by
        funext i; fin_cases i <;> simp
      rw [hw,work_empty]
    rw [he] at hh
    simpa only [Packed.Runs,Packed.ofProgram,s₄,work_reg,work_temp,Matrix.cons_val_zero,← memory_update,Data.size] using hh
  apply (h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))).mono
  cases head <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem selectAux_runs (head : Bool) (dst : Fin r) (s : Registers r) (d : Data) :
    (selectAux head dst).Runs (work s ![d.encode,[],[],[]])
      (memory (Function.update s dst (if head then d.head else d.tail)))
      (40*(d.size+(s dst).size+1)) := by
  cases d with
  | nil =>
    have hh := (Program.move_exec (src := temp 0) (dst := reg dst) (tmp := temp 1)
      (by simp) (by simp) (by simp) (work s ![Data.nil.encode,[],[],[]]) (by simp)).runs
    have he : Function.update (work s ![Data.nil.encode,[],[],[]]) (temp 0) [] = memory s := by
      rw [work_update_temp]
      have hw : Function.update ![Data.nil.encode,[],[],[]] (0 : Fin 4) [] = ![[],[],[],[]] := by
        funext i; fin_cases i <;> simp
      rw [hw,work_empty]
    rw [he] at hh
    have hx := hh.branch_right (fun h => (h (temp 0)).getD false) (selectPair head dst).program (by simp)
    have hout : (if head then Data.nil.head else Data.nil.tail) = Data.nil := by cases head <;> rfl
    rw [hout,memory_update]
    simpa only [selectAux,Packed.Runs,Packed.branch,Packed.ofProgram,work_temp,Matrix.cons_val_zero] using
      hx.mono (m := 40*(Data.nil.size+(s dst).size+1)) (by simp [Data.size]; omega)
  | pair a b =>
    have hh := selectPair_runs head dst s a b
    have hx := Program.Runs.branch_left (fun h => (h (temp 0)).getD false)
      (Program.move (temp 0) (reg dst) (temp 1)) hh (by simp [Data.encode_pair])
    exact hx.mono (by simp [Data.size_pair]; omega)

theorem select_runs (head : Bool) (dst src : Fin r) (s : Registers r) :
    (select head dst src).Runs (memory s)
      (memory (Function.update s dst (if head then (s src).head else (s src).tail)))
      (50*((s src).size+(s dst).size+1)) := by
  have h₁ := (Program.copy_exec (src := reg src) (dst := temp 0) (tmp := temp 1)
    (by simp) (by simp) (by simp) (memory s) (by simp)).runs
  have he : Function.update (memory s) (temp 0) (memory s (reg src)) = work s ![(s src).encode,[],[],[]] := by
    rw [memory_reg,← work_empty,work_update_temp]
    congr 1
    funext i; fin_cases i <;> simp
  rw [he] at h₁
  have h₂ := selectAux_runs head dst s (s src)
  exact (h₁.seq h₂).mono (by simp [Data.size]; omega)

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Program
variable {k : ℕ} {Q : Type}

theorem Runs.loop_stop (test : Heads k → Bool) (P : Program k Q) (s : Store k)
    (hs : test (fun i => (s i).head?) = false) : (loop test P).Runs s s 0 :=
  (Program.loop_stop test P s hs).runs

theorem Runs.loop_iterate (test : Heads k → Bool) {P : Program k Q}
    {s t u : Store k} {n m : ℕ} (h : P.Runs s t n) (h' : (loop test P).Runs t u m)
    (hs : test (fun i => (s i).head?) = true) : (loop test P).Runs s u (n+m+2) := by
  obtain ⟨n',hn,q,hq⟩ := h
  obtain ⟨m',hm,r,hr⟩ := h'
  have hnone : r = none := by
    have hh := hr.halted
    cases r with
    | none => rfl
    | some q =>
      unfold step at hh
      cases he : P.transition q (fun i => (u i).head?) <;> simp_all [loop]
  subst r
  exact (Program.loop_iterate test hs hq hr).runs.mono (by omega)

end ThreeMachine.StackCompiler.Program

namespace ThreeMachine.StackCompiler.Tree
variable {r : ℕ}

theorem skip_runs (s : Registers r) : skip.Runs (memory s) (memory s) 1 := by
  have hh := (Program.instruction_exec (k := r+3) (fun _ => Program.stayActions) (memory s)).runs
  simpa only [skip,Packed.Runs,Packed.ofProgram,Program.stayActions,Action.apply] using hh

theorem copy_runs (dst src : Fin r) (s : Registers r) :
    (copy dst src).Runs (memory s) (memory (Function.update s dst (s src)))
      (3*(s dst).size+6*(s src).size+2) := by
  by_cases he : dst = src
  · subst src
    simpa [copy] using (skip_runs s).mono (by omega : 1 ≤ 3*(s dst).size+6*(s dst).size+2)
  · rw [memory_update]
    unfold copy
    rw [ite_eq_right he]
    have hh := (Program.copy_exec (src := reg src) (dst := reg dst) (tmp := temp 0)
      (by simpa using Ne.symm he) (by simp) (by simp) (memory s) (by simp)).runs
    simpa only [memory_reg,Data.size,Packed.Runs,Packed.ofProgram] using hh

namespace Code

end Code

theorem Eval.compile {p : Code (Fin r)} {s t : Registers r} {n : ℕ} (h : Eval p s t n) :
    p.compile.Runs (memory s) (memory t) (150*n) := by
  induction h with
  | skip s => exact (skip_runs s).mono (by omega)
  | nil dst s =>
    apply (nil_runs dst s).mono
    omega
  | pair dst a b s =>
    apply (pair_runs dst a b s).mono
    omega
  | select head dst src s =>
    apply (select_runs head dst src s).mono
    omega
  | copy dst src s =>
    apply (copy_runs dst src s).mono
    omega
  | seq _ _ ih ih' => exact (ih.seq ih').mono (by omega)
  | @branch_true src p q s t n hs _ ih =>
    exact (Program.Runs.branch_left _ q.compile.program ih (by simpa using hs)).mono (by omega)
  | @branch_false src p q s t n hs _ ih =>
    exact (Program.Runs.branch_right _ p.compile.program ih (by simpa using hs)).mono (by omega)
  | @loop_stop src p s hs =>
    exact (Program.Runs.loop_stop _ p.compile.program (memory s) (by simpa using hs)).mono (by omega)
  | @loop_step src p s t u n m hs _ _ ih ih' =>
    exact (Program.Runs.loop_iterate _ ih ih' (by simpa using hs)).mono (by omega)

end ThreeMachine.StackCompiler.Tree

end

end OAI
end

section
-- module RoutineCompiler
namespace OAI

section

namespace ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
theorem overlay_of_agree (f : V → W) (s : V → Data) (base : W → Data)
    (h : ∀ i, base (f i) = s i) : overlay f s base = base := by
  funext j
  by_cases hj : ∃ a, f a = j
  · unfold overlay Function.extend
    simp only [dite_eq_left hj]
    rw [← h]
    congr 1
    exact Classical.choose_spec hj
  · exact overlay_out s base hj

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree

attribute [instance] Routine.finiteVars Routine.decVars

namespace Routine
variable {f g : Data → Data} {charge charge' : Data → ℕ}

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

namespace Routine
variable {f g : Data → Data} {c d : Data → ℕ}

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler
open ThreeMachine.StackCompiler.Tree

variable {V : Type} [DecidableEq V]

namespace Routine
variable {f g : Data → Data} {c d : Data → ℕ}

end Routine
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Tree
variable {V : Type} [DecidableEq V]

end ThreeMachine.StackCompiler.Tree

end

end OAI
end

section
-- module MachineBridge
namespace OAI

section

namespace ThreeMachine.StackCompiler.Packed
variable {k : ℕ}

theorem halt_runs (s : Store k) : halt.Runs s s 0 :=
  ⟨0,le_rfl,(),Program.Exec.halt rfl⟩

theorem pushWord_runs (dst : Fin (k+1)) (bs : List Bool) (s : Store k) :
    (pushWord dst bs).Runs s (Function.update s dst (bs ++ s dst)) (2*bs.length) := by
  induction bs with
  | nil => simpa only [pushWord,List.nil_append,Function.update_eq_self,List.length_nil,Nat.mul_zero] using halt_runs s
  | cons b bs ih =>
    have hp : (ofProgram (Program.push dst b)).Runs (Function.update s dst (bs ++ s dst))
        (Function.update (Function.update s dst (bs ++ s dst)) dst (b :: (bs ++ s dst))) 1 := by
      change (Program.push dst b).Runs _ _ _
      simpa only [Function.update_self] using (Program.push_exec dst b (Function.update s dst (bs ++ s dst))).runs
    have h := ih.seq hp
    simpa only [pushWord,List.length_cons,Function.update_self,Function.update_idem,
      List.cons_append,Nat.mul_add,Nat.mul_one,Nat.add_assoc] using h

theorem pop_runs (src : Fin (k+1)) (s : Store k) :
    (pop src).Runs s (Function.update s src (s src).tail) 1 :=
  (Program.pop_instruction src s).runs

theorem popN_runs (src : Fin (k+1)) (n : ℕ) (s : Store k) :
    (popN src n).Runs s (Function.update s src ((s src).drop n)) (2*n) := by
  induction n generalizing s with
  | zero => simpa only [popN,List.drop_zero,Function.update_eq_self,Nat.mul_zero] using halt_runs s
  | succ n ih =>
    have h := (pop_runs src s).seq (ih (Function.update s src (s src).tail))
    have h' := h.mono (show 1+2*n+1 ≤ 2*(n+1) by omega)
    simpa only [popN,Function.update_self,Function.update_idem,List.drop_tail] using h'

end ThreeMachine.StackCompiler.Packed

namespace ThreeMachine.StackCompiler.Raw
open Packed
variable {k : ℕ}

theorem encoded_cons (b : Bool) (xs : List Bool) :
    (enc (b :: xs)).encode = boolChunk b ++ (enc xs).encode := rfl

theorem encodeBody_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (bs : List Bool) (s : Store k) (hs : s src = b :: bs) :
    (encodeBody src dst).Runs s
      (Function.update (Function.update s src bs) dst (boolChunk b ++ s dst)) 12 := by
  have h := (Packed.pop_runs src s).seq
    (Packed.pushWord_runs dst (boolChunk b) (Function.update s src (s src).tail))
  simp only [hs,List.tail_cons,Function.update_of_ne hne.symm] at h
  cases b with
  | false =>
    exact (Program.Runs.branch_right _ _ h (by simp [hs])).mono (by decide)
  | true =>
    exact (Program.Runs.branch_left _ _ h (by simp [hs])).mono (by decide)

theorem encodeLoop_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (bs ys : List Bool) (s : Store k) (hs : s src = bs) (hd : s dst = (enc ys).encode) :
    (encodeLoop src dst).Runs s
      (Function.update (Function.update s src []) dst (enc (bs.reverse ++ ys)).encode)
      (14*bs.length) := by
  induction bs generalizing ys s with
  | nil =>
    have he : Function.update (Function.update s src []) dst (enc ([] ++ ys)).encode = s := by
      rw [List.nil_append,← hd]; ext i
      by_cases hi : i = dst <;> by_cases hj : i = src <;> simp_all
    rw [List.reverse_nil,he]
    exact Program.Runs.loop_stop _ _ s (by simp [hs])
  | cons b bs ih =>
    let t := Function.update (Function.update s src bs) dst (boolChunk b ++ s dst)
    have hb : (encodeBody src dst).Runs s t 12 := encodeBody_runs hne b bs s hs
    have ht : t src = bs := by simp [t,hne]
    have hd' : t dst = (enc (b :: ys)).encode := by simp only [t,Function.update_self,hd,encoded_cons]
    have hr := ih (b :: ys) t ht hd'
    have he : Function.update (Function.update t src []) dst (enc (bs.reverse ++ b :: ys)).encode =
        Function.update (Function.update s src []) dst (enc ((b :: bs).reverse ++ ys)).encode := by
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
      ext i
      by_cases hi : i = dst <;> by_cases hj : i = src <;> simp_all [t]
    rw [he] at hr
    exact (Program.Runs.loop_iterate _ hb hr (by simp [hs])).mono (by simp only [List.length_cons]; omega)

end ThreeMachine.StackCompiler.Raw

namespace ThreeMachine.StackCompiler.Raw
open Packed
variable {k : ℕ}

theorem decodeAfterTag_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (rest : List Bool) (s : Store k) (hs : s src = (enc b).encode ++ rest) :
    (decodeAfterTag src dst).Runs s
      (Function.update (Function.update s src rest) dst (b :: s dst)) 10 := by
  cases b with
  | false =>
    have h := Program.Runs.seq (Packed.popN_runs src 1 s)
      (Program.push_exec dst false (Function.update s src ((s src).drop 1))).runs
    have he : (enc false).encode = [false] := rfl
    simp only [hs,he,List.singleton_append,List.drop_succ_cons,List.drop_zero,
      Function.update_of_ne hne.symm] at h
    exact (Program.Runs.branch_right _ _ h (by simp [hs])).mono (by omega)
  | true =>
    have h := Program.Runs.seq (Packed.popN_runs src 3 s)
      (Program.push_exec dst true (Function.update s src ((s src).drop 3))).runs
    have he : (enc true).encode = [true,false,false] := rfl
    simp only [hs,he,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,
      Function.update_of_ne hne.symm] at h
    exact (Program.Runs.branch_left _ _ h (by simp [hs])).mono (by omega)

theorem decodeBody_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (b : Bool) (bs : List Bool) (s : Store k) (hs : s src = (enc (b :: bs)).encode) :
    (decodeBody src dst).Runs s
      (Function.update (Function.update s src (enc bs).encode) dst (b :: s dst)) 12 := by
  have ht : (Function.update s src (s src).tail) src = (enc b).encode ++ (enc bs).encode := by
    simp only [Function.update_self,hs,encoded_cons,boolChunk,List.cons_append,List.tail_cons]
  have h := (Packed.pop_runs src s).seq (decodeAfterTag_runs hne b (enc bs).encode _ ht)
  simpa only [decodeBody,Function.update_idem,Function.update_of_ne hne.symm,Nat.reduceAdd] using h

theorem decodeLoop_runs {src dst : Fin (k+1)} (hne : src ≠ dst)
    (bs : List Bool) (s : Store k) (hs : s src = (enc bs).encode) :
    (decodeLoop src dst).Runs s
      (Function.update (Function.update s src [false]) dst (bs.reverse ++ s dst))
      (14*bs.length) := by
  induction bs generalizing s with
  | nil =>
    have he : Function.update (Function.update s src [false]) dst ([] ++ s dst) = s := by
      rw [List.nil_append]; ext i
      by_cases hi : i = dst <;> by_cases hj : i = src <;> simp_all
    rw [List.reverse_nil,he]
    exact Program.Runs.loop_stop _ _ s (by change (s src).head?.getD false = _; rw [hs]; rfl)
  | cons b bs ih =>
    let t := Function.update (Function.update s src (enc bs).encode) dst (b :: s dst)
    have hb : (decodeBody src dst).Runs s t 12 := decodeBody_runs hne b bs s hs
    have hr := ih t (by simp [t,hne])
    have he : Function.update (Function.update t src [false]) dst (bs.reverse ++ t dst) =
        Function.update (Function.update s src [false]) dst ((b :: bs).reverse ++ s dst) := by
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
      ext i
      by_cases hi : i = dst <;> by_cases hj : i = src <;> simp_all [t]
    rw [he] at hr
    exact (Program.Runs.loop_iterate _ hb hr (by change (s src).head?.getD false = _; rw [hs]; rfl)).mono
      (by simp only [List.length_cons]; omega)

end ThreeMachine.StackCompiler.Raw

namespace ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] in
theorem overlay_zero (f : V → W) : overlay f (zeroStore V) (zeroStore W) = zeroStore W :=
  overlay_of_agree f _ _ (fun _ => rfl)

theorem overlay_start {f : V → W} (hf : Function.Injective f) (input : V) (x : Data) :
    overlay f (start input x) (zeroStore W) = start (f input) x := by
  rw [start,overlay_update hf,overlay_zero]
  rfl

theorem overlay_finish {f : V → W} (hf : Function.Injective f) (a b : V) (x y : Data) :
    overlay f (finish a b x y) (zeroStore W) = finish (f a) (f b) x y := by
  rw [finish,overlay_update hf,overlay_start hf]
  rfl

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Routine
open ThreeMachine.StackCompiler.Tree
variable {f : Data → Data} {charge : Data → ℕ}
variable (R : Routine f charge)

theorem number_injective : Function.Injective R.number :=
  (Fin.succ_injective _).comp (Fintype.equivFin R.Vars).injective

theorem numberedCode_runs (x : Data) :
    R.numberedCode.compile.Runs (memory (start (R.number R.input) x))
      (memory (finish (R.number R.input) (R.number R.output) x (f x))) (150*charge x) := by
  obtain ⟨n,hn,he⟩ := R.correct x
  have hh := (he.rename R.number_injective (zeroStore (Fin (Fintype.card R.Vars+1)))).compile
  rw [overlay_start R.number_injective,overlay_finish R.number_injective] at hh
  exact hh.mono (Nat.mul_le_mul_left 150 hn)

theorem initRegs_runs (s : Store (Fintype.card R.Vars+4)) :
    R.initRegs.Runs s (fun j => if j.val < Fintype.card R.Vars+1 then false :: s j else s j) 1 := by
  have he : (fun j => (if j.val < Fintype.card R.Vars+1 then Action.push false else Action.stay).apply (s j)) =
      (fun j => if j.val < Fintype.card R.Vars+1 then false :: s j else s j) := by
    funext j
    split_ifs <;> rfl
  simpa only [initRegs,Packed.Runs,Packed.ofProgram,he] using
    (Program.instruction_exec (fun _ j =>
      if j.val < Fintype.card R.Vars+1 then Action.push false else .stay) s).runs

theorem inputProgram_runs (bs : List Bool) :
    R.inputProgram.Runs (initialStore bs)
      (memory (start (R.number R.input) (enc bs))) (17*bs.length+3) := by
  let s : Store (Fintype.card R.Vars+4) := Function.update (fun _ => []) (temp 0) bs.reverse
  have ht : (Packed.ofProgram (Program.transfer 0 (temp 0))).Runs
      (initialStore bs) s (3*bs.length) := by
    have h := (Program.transfer_exec (Ne.symm R.temp_ne_zero) (initialStore bs)).runs
    have he : Program.transferResult 0 (temp 0) (initialStore bs) = s := by
      funext i
      by_cases hi : i = temp 0 <;> by_cases hz : i = 0 <;>
        simp_all [Program.transferResult,initialStore,s,R.temp_ne_zero,Ne.symm R.temp_ne_zero]
    simpa only [Packed.Runs,Packed.ofProgram,initialStore,ite_true,he] using h
  let t : Store (Fintype.card R.Vars+4) :=
    fun j => if j.val < Fintype.card R.Vars+1 then false :: s j else s j
  have hi : R.initRegs.Runs s t 1 := R.initRegs_runs s
  have hts : t (temp 0) = bs.reverse := by simp [t,s,temp]
  have htd : t (reg (R.number R.input)) = (enc ([] : List Bool)).encode := by
    have hv : (reg (R.number R.input)).val < Fintype.card R.Vars+1 := (R.number R.input).isLt
    simp only [t,ite_eq_left hv,s,Function.update_of_ne (reg_ne_temp _ _)]
    rfl
  have he := Raw.encodeLoop_runs (temp_ne_reg _ _) bs.reverse [] t hts htd
  have hfinal : Function.update (Function.update t (temp 0) [])
      (reg (R.number R.input)) (enc (bs.reverse.reverse ++ [])).encode =
      memory (start (R.number R.input) (enc bs)) := by
    simp only [List.reverse_reverse,List.append_nil]
    funext j
    refine Fin.addCases (m := Fintype.card R.Vars+1) (n := 4) (fun i => ?_) (fun i => ?_) j
    · change Function.update (Function.update t (temp 0) []) (reg (R.number R.input))
        (enc bs).encode (reg i) = memory (start (R.number R.input) (enc bs)) (reg i)
      by_cases hh : i = R.number R.input
      · subst i; simp
      · have hv : (reg i).val < Fintype.card R.Vars+1 := i.isLt
        simp only [Function.update_of_ne (show reg i ≠ reg (R.number R.input) by simpa using hh),
          memory_reg,start_other _ hh,t,ite_eq_left hv,s,
          Function.update_of_ne (reg_ne_temp _ _)]
        rfl
    · change Function.update (Function.update t (temp 0) []) (reg (R.number R.input))
        (enc bs).encode (temp i) = memory (start (R.number R.input) (enc bs)) (temp i)
      by_cases hh : i = 0
      · subst i; simp
      · have hv : ¬(temp (r := Fintype.card R.Vars+1) i).val < Fintype.card R.Vars+1 := by
          simp only [temp,Fin.val_natAdd]; omega
        simp only [Function.update_of_ne (temp_ne_reg _ _),memory_temp,
          Function.update_of_ne (show (temp i : Fin (Fintype.card R.Vars+1+4)) ≠ temp 0 by simpa using hh),
          t,ite_eq_right hv,s]
  rw [hfinal] at he
  exact (ht.seq (hi.seq he)).mono (by simp only [List.length_reverse]; omega)

theorem outputProgram_runs (bs out : List Bool) :
    ∃ t, R.outputProgram.Runs
      (memory (finish (R.number R.input) (R.number R.output) (enc bs) (enc out))) t
      (17*out.length+3) ∧ t 0 = out := by
  let s := memory (finish (R.number R.input) (R.number R.output) (enc bs) (enc out))
  have hzero : s 0 = [false] := by
    change memory _ (reg (0 : Fin (Fintype.card R.Vars+1))) = _
    simp only [memory_reg,finish,Function.update_of_ne (Ne.symm (R.number_ne_zero R.output)),
      start_other _ (Ne.symm (R.number_ne_zero R.input))]
    rfl
  have hd := Raw.decodeLoop_runs (reg_ne_temp _ 0) out s
    (show s (reg (R.number R.output)) = (enc out).encode by simp [s])
  let u := Function.update (Function.update s (reg (R.number R.output)) [false])
    (temp 0) (out.reverse ++ s (temp 0))
  have hu : u 0 = [false] := by
    simp only [u,Function.update_of_ne (Ne.symm R.temp_ne_zero),
      Function.update_of_ne (Ne.symm (R.reg_number_ne_zero R.output)),hzero]
  have hv : u (temp 0) = out.reverse := by simp [u,s]
  let v := Function.update u 0 []
  have hp : (Packed.pop 0).Runs u v 1 := by
    simpa only [hu,List.tail_cons,List.tail_nil] using Packed.pop_runs 0 u
  have ht := (Program.transfer_exec R.temp_ne_zero v).runs
  have hvt : v (temp 0) = out.reverse := by simp [v,R.temp_ne_zero,hv]
  have hvz : v 0 = [] := by simp [v]
  rw [hvt,List.length_reverse] at ht
  have ht' : (Packed.ofProgram (Program.transfer (temp 0) 0)).Runs v
      (Program.transferResult (temp 0) 0 v) (3*out.length) := ht
  refine ⟨Program.transferResult (temp 0) 0 v,?_,?_⟩
  · exact (hd.seq (hp.seq ht')).mono (by omega)
  · simp [Program.transferResult,hvt,hvz]

theorem rawProgram_runs (bs out : List Bool) (h : f (enc bs) = enc out) :
    ∃ t, R.rawProgram.Runs (initialStore bs) t
      (1000*(charge (enc bs)+bs.length+out.length+1)) ∧ t 0 = out := by
  have hi := R.inputProgram_runs bs
  have hc := R.numberedCode_runs (enc bs)
  rw [h] at hc
  obtain ⟨t,ho,ht⟩ := R.outputProgram_runs bs out
  exact ⟨t,(hi.seq (hc.seq ho)).mono (by omega),ht⟩

include R in
theorem exists_rawMachine : ∃ k q g, ∃ M : Machine k q g,
    ∀ bs out, f (enc bs) = enc out →
      M.Produces bs out (2000*(charge (enc bs)+bs.length+out.length+1)) := by
  refine ⟨_,_,_,compile R.rawProgram.program,?_⟩
  intro bs out h
  obtain ⟨t,ht,ho⟩ := R.rawProgram_runs bs out h
  have hh := ht.computes
  obtain ⟨n,hn,hs,hh⟩ := hh
  have he := compile_produces R.rawProgram.program bs out
    (1000*(charge (enc bs)+bs.length+out.length+1)) ⟨n,hn,hh,by rw [hs,ho]⟩
  simpa only [← Nat.mul_assoc] using he

end ThreeMachine.StackCompiler.Routine
end

end OAI
end

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

-- Solutions.TreeToTM2
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.TreeToTM2
open Turing.TM2
variable {κ Λ : Type} [DecidableEq κ]
abbrev Heads (κ : Type) := κ → Option Bool
abbrev StmtB (κ Λ : Type) := Stmt (fun _ : κ => Bool) Λ (Heads κ)

 def readHeads : List κ → StmtB κ Λ → StmtB κ Λ
   | [],next => next
   | i::L,next => .peek i (fun h b => Function.update h i b) (readHeads L next)

 theorem readHeads_aux (L : List κ) (next : StmtB κ Λ) (h : Heads κ) (S : κ → List Bool) :
    stepAux (readHeads L next) h S = stepAux next (fun i => if i∈L then (S i).head? else h i) S := by
  induction L generalizing h with
  | nil => simp [readHeads]
  | cons i L ih =>
    simp only [readHeads,stepAux,ih]
    congr 1
    funext j
    by_cases hj : j=i <;> by_cases hm : j∈L <;> simp [hj,hm]

 def actionCode (i : κ) (a : Heads κ → OAI.ThreeMachine.StackCompiler.Action) (next : StmtB κ Λ) : StmtB κ Λ :=
   .branch (fun h => match a h with | .stay => true | _ => false) next
     (.branch (fun h => match a h with | .pop => true | _ => false)
       (.pop i (fun h _ => h) next)
       (.push i (fun h => match a h with | .push b => b | _ => false) next))

 theorem actionCode_aux (i : κ) (a : Heads κ → OAI.ThreeMachine.StackCompiler.Action) (next : StmtB κ Λ)
    (h : Heads κ) (S : κ → List Bool) :
    stepAux (actionCode i a next) h S=stepAux next h (Function.update S i ((a h).apply (S i))) := by
  unfold actionCode
  cases he : a h <;> simp [stepAux,he,OAI.ThreeMachine.StackCompiler.Action.apply]

 def actionsCode : List κ → (Heads κ → κ → OAI.ThreeMachine.StackCompiler.Action) → StmtB κ Λ → StmtB κ Λ
   | [],_,next => next
   | i::L,a,next => actionCode i (fun h => a h i) (actionsCode L a next)

 theorem actionsCode_aux (L : List κ) (hL : L.Nodup) (a : Heads κ → κ → OAI.ThreeMachine.StackCompiler.Action)
    (next : StmtB κ Λ) (h : Heads κ) (S : κ → List Bool) :
    stepAux (actionsCode L a next) h S =
      stepAux next h (fun i => if i∈L then (a h i).apply (S i) else S i) := by
  induction L generalizing S with
  | nil => simp [actionsCode]
  | cons i L ih =>
    rw [actionsCode,actionCode_aux,ih (List.nodup_cons.mp hL).2]
    congr 1
    funext j
    by_cases hj : j=i
    · subst j
      simp [(List.nodup_cons.mp hL).1]
    · simp [hj]

variable {k : ℕ} {Q : Type} [Fintype Q]
abbrev Label (k : ℕ) (Q : Type) := Q ⊕ Fin (k+2)

 def defaultActions (h : Heads (Fin (k+1))) : Fin (k+1) → OAI.ThreeMachine.StackCompiler.Action := fun _ => .stay
 def choice (P : OAI.ThreeMachine.StackCompiler.Program k Q) (q : Q) (h : Heads (Fin (k+1))) : Q × OAI.ThreeMachine.StackCompiler.Actions k :=
   (P.transition q h).getD (q,fun _ => .stay)

 def source (P : OAI.ThreeMachine.StackCompiler.Program k Q) (q : Q) : StmtB (Fin (k+1)) (Label k Q) :=
   readHeads (List.finRange (k+1))
     (.branch (fun h => (P.transition q h).isSome)
       (actionsCode (List.finRange (k+1)) (fun h => (choice P q h).2)
         (.goto (fun h => .inl (choice P q h).1)))
       (.goto (fun _ => .inr 0)))

 theorem source_some (P : OAI.ThreeMachine.StackCompiler.Program k Q) (q q' : Q) (a : OAI.ThreeMachine.StackCompiler.Actions k)
    (h : Heads (Fin (k+1))) (S : OAI.ThreeMachine.StackCompiler.Store k)
    (he : P.transition q (fun i => (S i).head?)=some (q',a)) :
    stepAux (source P q) h S=⟨some (.inl q'),(fun i => (S i).head?),fun i => (a i).apply (S i)⟩ := by
  rw [source,readHeads_aux]
  simp only [List.mem_finRange,ite_true]
  simp only [stepAux,he,Option.isSome_some,cond_true]
  rw [actionsCode_aux _ (List.nodup_finRange _)]
  simp only [List.mem_finRange,ite_true,stepAux,choice,he,Option.getD_some]

 theorem source_none (P : OAI.ThreeMachine.StackCompiler.Program k Q) (q : Q) (h : Heads (Fin (k+1))) (S : OAI.ThreeMachine.StackCompiler.Store k)
    (he : P.transition q (fun i => (S i).head?)=none) :
    stepAux (source P q) h S=⟨some (.inr 0),(fun i => (S i).head?),S⟩ := by
  rw [source,readHeads_aux]
  simp only [List.mem_finRange,ite_true,stepAux,he,Option.isSome_none,cond_false]

end EdgeSublinearMWIS.Main.TreeToTM2
end

-- Solutions.TreeTM2Cleanup
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.TreeToTM2
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
variable {k : ℕ} {Q : Type}

 def clearStmt (j : Fin (k+2)) : StmtB (Fin (k+1)) (Label k Q) :=
   if hj : j.val< k+1 then
     if j.val=0 then .goto (fun _ => .inr ⟨j.val+1,by omega⟩)
     else let i : Fin (k+1) := ⟨j.val,hj⟩
       .pop i (fun h b => Function.update h i b)
         (.branch (fun h => (h i).isSome) (.goto (fun _ => .inr j))
           (.goto (fun _ => .inr ⟨j.val+1,by omega⟩)))
   else .load (fun _ => fun _ => none) .halt

 def code (P : OAI.ThreeMachine.StackCompiler.Program k Q) : Label k Q → StmtB (Fin (k+1)) (Label k Q)
   | .inl q => source P q
   | .inr j => clearStmt j

 theorem clear_stack (P : OAI.ThreeMachine.StackCompiler.Program k Q) (j : Fin (k+2))
    (hj : j.val< k+1) (hj0 : j.val≠0) (S : Fin (k+1) → List Bool) (h : Heads (Fin (k+1)))
    (L : List Bool) (hs : S ⟨j.val,hj⟩=L) :
    run (code P) (cfg (some (.inr j)) h S) (L.length+1)=
      some (cfg (some (.inr ⟨j.val+1,by omega⟩))
        (Function.update h ⟨j.val,hj⟩ none) (Function.update S ⟨j.val,hj⟩ [])) := by
  let i : Fin (k+1) := ⟨j.val,hj⟩
  induction L generalizing h S with
  | nil =>
    rw [List.length_nil,zero_add,run_one]
    simp [step,cfg,code,clearStmt,hj,hj0,stepAux,hs]
  | cons b L ih =>
    have hstep : step (code P) (cfg (some (.inr j)) h S)=
        some (cfg (some (.inr j)) (Function.update h i (some b)) (Function.update S i L)) := by
      simp [step,cfg,code,clearStmt,hj,hj0,stepAux,hs,i]
    have hs' : Function.update S i L i=L := Function.update_self _ _ _
    rw [List.length_cons,run_first,hstep,Option.bind_some]
    have hh := ih (Function.update S i L) (Function.update h i (some b)) hs'
    simpa only [i,Function.update_idem] using hh

 def remaining (j : ℕ) (S : Fin (k+1) → List Bool) : ℕ :=
   ∑ i : Fin (k+1),if j ≤ i.val ∧ i.val≠0 then (S i).length else 0
 def cleaned (j : ℕ) (S : Fin (k+1) → List Bool) : Fin (k+1) → List Bool :=
   fun i => if i.val< j ∨ i.val=0 then S i else []

 theorem remaining_zero (S : Fin (k+1) → List Bool) : remaining 0 S=remaining 1 S := by
   unfold remaining
   apply Finset.sum_congr rfl
   intro i hi
   by_cases h0 : i.val=0 <;> simp [h0] <;> omega

 theorem remaining_step (j : ℕ) (hj : j< k+1) (hj0 : j≠0) (S : Fin (k+1) → List Bool) :
    remaining j S=(S ⟨j,hj⟩).length+remaining (j+1) (Function.update S ⟨j,hj⟩ []) := by
   let i : Fin (k+1) := ⟨j,hj⟩
   have hp : ∀ x : Fin (k+1),
       (if j≤ x.val ∧ x.val≠0 then (S x).length else 0)=
       (if x=i then (S i).length else 0)+
       (if j+1≤ x.val ∧ x.val≠0 then ((Function.update S i []) x).length else 0) := by
     intro x
     by_cases he : x=i
     · subst x; simp [i,hj0]
     · have hval : x.val≠j := by intro h; apply he; exact Fin.ext h
       by_cases hlo : j≤ x.val
       · have hnext : j+1≤ x.val := by omega
         simp [hlo,hnext,he,show x.val≠0 by omega]
       · have hn : ¬j+1≤ x.val := by omega
         simp [hlo,hn,he]
   unfold remaining
   simp_rw [hp,Finset.sum_add_distrib]
   simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
   rfl



 theorem clear_run (P : OAI.ThreeMachine.StackCompiler.Program k Q) (j : Fin (k+2))
    (S : Fin (k+1) → List Bool) (h : Heads (Fin (k+1))) :
    ∃ t,t≤ remaining j.val S+2*(k+2-j.val) ∧
      run (code P) (cfg (some (.inr j)) h S) t=
        some (cfg none (fun _ => none) (cleaned j.val S)) := by
  induction hm : k+1-j.val using Nat.strong_induction_on generalizing j S h with
  | h z ih =>
    by_cases hlast : j.val=k+1
    · refine ⟨1,by omega,?_⟩
      rw [run_one]
      have hn : ¬j.val< k+1 := by omega
      simp only [step,cfg,code,clearStmt,dif_neg hn,stepAux]
      congr 2
      funext i
      simp [cleaned,show i.val< j.val by omega]
    · have hj : j.val< k+1 := by have := j.isLt; omega
      let j' : Fin (k+2) := ⟨j.val+1,by omega⟩
      have hj' : k+1-j'.val< z := by dsimp [j']; omega
      by_cases hj0 : j.val=0
      · obtain ⟨t,ht,hr⟩ := ih (k+1-j'.val) hj' j' S h rfl
        have hs : step (code P) (cfg (some (.inr j)) h S)=some (cfg (some (.inr j')) h S) := by
          simp [step,cfg,code,clearStmt,hj,hj0,j']
        refine ⟨t+1,?_,?_⟩
        · have he : remaining j.val S=remaining j'.val S := by simpa [hj0,j'] using remaining_zero S
          rw [he]
          dsimp [j'] at ht ⊢
          omega
        · rw [run_first,hs,Option.bind_some,hr]
          congr 2
          funext i
          simp only [cleaned]
          have he : (i.val< j'.val ∨ i.val=0) ↔ (i.val< j.val ∨ i.val=0) := by dsimp [j']; omega
          simp only [he]
      · let i : Fin (k+1) := ⟨j.val,hj⟩
        let S' := Function.update S i []
        let h' := Function.update h i none
        obtain ⟨t,ht,hr⟩ := ih (k+1-j'.val) hj' j' S' h' rfl
        have hs := clear_stack P j hj hj0 S h (S i) rfl
        have ht' : (S i).length+1+t ≤ remaining j.val S+2*(k+2-j.val) := by
          rw [remaining_step j.val hj hj0 S]
          dsimp [j',S',i] at ht ⊢
          omega
        refine ⟨(S i).length+1+t,ht',?_⟩
        have hh := run_trans (code P) _ _ _ ((S i).length+1) t hs hr
        convert hh using 1
        congr 2
        funext x
        by_cases hxi : x=i
        · subst x
          simp [cleaned,S',i,hj0,j']
        · have hval : x.val≠j.val := by intro he; apply hxi; exact Fin.ext he
          have he : (x.val< j'.val ∨ x.val=0) ↔ (x.val< j.val ∨ x.val=0) := by dsimp [j']; omega
          simp only [cleaned,he,S',Function.update_of_ne hxi]

end EdgeSublinearMWIS.Main.TreeToTM2
end

-- Solutions.TreeTM2Execution
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.TreeToTM2
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
variable {k : ℕ} {Q : Type} [Fintype Q]

 theorem step_some (P : OAI.ThreeMachine.StackCompiler.Program k Q)
    (s t : OAI.ThreeMachine.StackCompiler.State k Q)
    (hs : P.step s=some t) (h : Heads (Fin (k+1))) :
    step (code P) (cfg (some (.inl s.control)) h s.store)=
      some (cfg (some (.inl t.control)) (fun i => (s.store i).head?) t.store) := by
  cases he : P.transition s.control (fun i => (s.store i).head?) with
  | none => simp [OAI.ThreeMachine.StackCompiler.Program.step,he] at hs
  | some qa =>
    have ht : t=⟨qa.1,fun i => (qa.2 i).apply (s.store i)⟩ := by
      simpa [OAI.ThreeMachine.StackCompiler.Program.step,he] using hs.symm
    rw [ht]
    change some (stepAux (source P s.control) h s.store)=_
    rw [source_some P s.control qa.1 qa.2 h s.store he]
    rfl

 theorem exec_run (P : OAI.ThreeMachine.StackCompiler.Program k Q)
    {s t : OAI.ThreeMachine.StackCompiler.State k Q} {n : ℕ}
    (he : P.Exec s n t) (h : Heads (Fin (k+1))) :
    ∃ h',run (code P) (cfg (some (.inl s.control)) h s.store) n=
      some (cfg (some (.inl t.control)) h' t.store) := by
  induction he generalizing h with
  | halt hh => exact ⟨h,rfl⟩
  | @next s t u n hs he ih =>
    obtain ⟨h',hr⟩ := ih (fun i => (s.store i).head?)
    refine ⟨h',?_⟩
    rw [run_first,step_some P s t hs h,Option.bind_some]
    exact hr

 def size (S : Fin (k+1) → List Bool) : ℕ := ∑ i,(S i).length

 theorem action_size (a : OAI.ThreeMachine.StackCompiler.Action) (L : List Bool) :
    (a.apply L).length  ≤  L.length+1 := by
  cases a <;> simp [OAI.ThreeMachine.StackCompiler.Action.apply] <;> omega

 theorem step_size (P : OAI.ThreeMachine.StackCompiler.Program k Q)
    (s t : OAI.ThreeMachine.StackCompiler.State k Q) (hs : P.step s=some t) :
    size t.store  ≤  size s.store+(k+1) := by
  cases he : P.transition s.control (fun i => (s.store i).head?) with
  | none => simp [OAI.ThreeMachine.StackCompiler.Program.step,he] at hs
  | some qa =>
    have ht : t=⟨qa.1,fun i => (qa.2 i).apply (s.store i)⟩ := by
      simpa [OAI.ThreeMachine.StackCompiler.Program.step,he] using hs.symm
    rw [ht]
    have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin (k+1)))) => action_size (qa.2 i) (s.store i))
    simpa [size,Finset.sum_add_distrib] using hh

 theorem exec_size (P : OAI.ThreeMachine.StackCompiler.Program k Q)
    {s t : OAI.ThreeMachine.StackCompiler.State k Q} {n : ℕ} (he : P.Exec s n t) :
    size t.store  ≤  size s.store+(k+1)*n := by
  induction he with
  | halt hh => simp
  | @next s t u n hs he ih =>
    have hh := step_size P s t hs
    nlinarith

 theorem halt_none (P : OAI.ThreeMachine.StackCompiler.Program k Q)
    (s : OAI.ThreeMachine.StackCompiler.State k Q) (hs : P.step s=none) :
    P.transition s.control (fun i => (s.store i).head?)=none := by
  cases he : P.transition s.control (fun i => (s.store i).head?) with
  | none => rfl
  | some qa => simp [OAI.ThreeMachine.StackCompiler.Program.step,he] at hs

 theorem full_run (P : OAI.ThreeMachine.StackCompiler.Program k Q)
    {s t : OAI.ThreeMachine.StackCompiler.State k Q} {n : ℕ} (he : P.Exec s n t)
    (h : Heads (Fin (k+1))) :
    ∃ m,m ≤ size s.store+(k+2)*n+2*k+5 ∧
      run (code P) (cfg (some (.inl s.control)) h s.store) m=
        some (cfg none (fun _ => none) (fun i => if i=0 then t.store 0 else [])) := by
  obtain ⟨h',hr⟩ := exec_run P he h
  have hn := halt_none P t he.halted
  have hs : step (code P) (cfg (some (.inl t.control)) h' t.store)=
      some (cfg (some (.inr 0)) (fun i => (t.store i).head?) t.store) := by
    change some (stepAux (source P t.control) h' t.store)=_
    rw [source_none P t.control h' t.store hn]
    rfl
  obtain ⟨m,hm,hclear⟩ := clear_run P 0 t.store (fun i => (t.store i).head?)
  have hremaining : remaining 0 t.store  ≤  size t.store := by
    unfold remaining size
    apply Finset.sum_le_sum
    intro i hi
    split_ifs <;> omega
  have hsize := exec_size P he
  refine ⟨n+1+m,by dsimp at hm; nlinarith,?_⟩
  have h1 := run_trans (code P) _ _ _ n 1 hr (by rw [run_one]; exact hs)
  have h2 := run_trans (code P) _ _ _ (n+1) m h1 hclear
  convert h2 using 1
  congr 2
  funext i
  by_cases hi : i=0
  · subst i; simp [cleaned]
  · have hiv : i.val ≠ 0 := by intro hh; apply hi; exact Fin.ext hh
    simp [cleaned,hi,hiv]

end EdgeSublinearMWIS.Main.TreeToTM2
end

-- Solutions.TreeTM2Program
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.TreeToTM2
open EdgeSublinearMWIS.Main.RawStack
variable {k : ℕ} {Q : Type} [Fintype Q]

 def tm (P : OAI.ThreeMachine.StackCompiler.Program k Q) : Turing.FinTM2 where
   K := Fin (k+1)
   k₀ := 0
   k₁ := 0
   Γ := fun _ => Bool
   Λ := Label k Q
   main := .inl P.initial
   σ := Heads (Fin (k+1))
   initialState := fun _ => none
   m := code P

 def program (P : OAI.ThreeMachine.StackCompiler.Program k Q) : Program where
   machine := ⟨tm P,Equiv.refl _,Equiv.refl _⟩
   finiteAlphabet _ := by change Finite Bool; infer_instance

 theorem program_runs (P : OAI.ThreeMachine.StackCompiler.Program k Q)
    (input output : List Bool) (T : ℕ)
    (he : ∃ S,P.Runs (OAI.ThreeMachine.StackCompiler.initialStore input) S T ∧ S 0=output) :
    Runs (program P) input output (input.length+(k+2)*T+2*k+5) := by
   obtain ⟨S,hRun,hout⟩ := he
   obtain ⟨n,hn,q,hExec⟩ := hRun
   have hsize : size (OAI.ThreeMachine.StackCompiler.initialStore (k:=k) input)=input.length := by
     unfold size OAI.ThreeMachine.StackCompiler.initialStore
     simp_rw [apply_ite,List.length_nil]
     simp
   obtain ⟨m,hm,hr⟩ := full_run P hExec (fun _ => none)
   rw [hsize] at hm
   have hstart : Turing.initList (tm P) input=cfg (some (.inl P.initial)) (fun _ => none)
       (OAI.ThreeMachine.StackCompiler.initialStore input) := by
     rfl
   have hfinish : Turing.haltList (tm P) output=cfg none (fun _ => none)
       (fun i : Fin (k+1) => if i=0 then S 0 else []) := by
     rw [hout]
     rfl
   have hr' : run (tm P).m (Turing.initList (tm P) input) m=some (Turing.haltList (tm P) output) := by
     rw [hstart,hfinish]
     exact hr
   obtain ⟨hout'⟩ := RawStack.outputs (tm := tm P) input output m hr'
   have hbound : m ≤ input.length+(k+2)*T+2*k+5 := hm.trans (by nlinarith)
   have hh : Nonempty (Turing.TM2OutputsInTime (tm P) input (some output) (input.length+(k+2)*T+2*k+5)) :=
     ⟨{ hout' with steps_le_m := hout'.steps_le_m.trans hbound }⟩
   change Nonempty (Turing.TM2OutputsInTime (tm P) (input.map id) (some (output.map id)) (input.length+(k+2)*T+2*k+5))
   dsimp only [tm] at hh ⊢
   simpa only [List.map_id] using hh
   

end EdgeSublinearMWIS.Main.TreeToTM2
end

-- Solutions.RoutineProgram
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.TreeToTM2
open OAI.ThreeMachine.StackCompiler

 theorem runs_mono (P : EdgeSublinearMWIS.Main.Program) (input output : List Bool) {t u : ℕ}
    (ht : EdgeSublinearMWIS.Main.Runs P input output t) (htu : t≤ u) :
    EdgeSublinearMWIS.Main.Runs P input output u := by
  obtain ⟨h⟩ := ht
  exact ⟨{h with steps_le_m := h.steps_le_m.trans htu}⟩

 def routineProgram {f : Data → Data} {charge : Data → ℕ} (R : Routine f charge) : EdgeSublinearMWIS.Main.Program :=
   program R.rawProgram.program

 def routineFactor {f : Data → Data} {charge : Data → ℕ} (R : Routine f charge) : ℕ :=
   2000*(Fintype.card R.Vars+7)

 theorem routine_runs {f : Data → Data} {charge : Data → ℕ} (R : Routine f charge)
    (input output : List Bool) (hf : f (enc input)=enc output) :
    EdgeSublinearMWIS.Main.Runs (routineProgram R) input output
      (routineFactor R*(charge (enc input)+input.length+output.length+1)) := by
  obtain ⟨S,hS,hout⟩ := R.rawProgram_runs input output hf
  have hr := program_runs R.rawProgram.program input output
    (1000*(charge (enc input)+input.length+output.length+1)) ⟨S,hS,hout⟩
  apply runs_mono _ _ _ hr
  let z := charge (enc input)+input.length+output.length+1
  have hz : 1≤ z := by dsimp [z]; omega
  have hL : input.length≤ z := by dsimp [z]; omega
  change input.length+(Fintype.card R.Vars+4+2)*(1000*z)+2*(Fintype.card R.Vars+4)+5 ≤ routineFactor R*z
  unfold routineFactor
  nlinarith

end EdgeSublinearMWIS.Main.TreeToTM2
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
   let F := routineFactor R.routine
   refine ⟨routineProgram R.routine,F*(2*C*5^q+2),q+1,?_,by omega,?_⟩
   · dsimp [F,routineFactor]; positivity
   · intro input
     have hRun := routine_runs R.routine input (f input) (R.correct input)
     apply runs_mono _ _ _ hRun
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

-- Solutions.ScaleRoundingWords
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev ScaleInput := ℕ×(FractionWords×FractionWords)
 def scaleWords (s : ScaleInput) : FractionWords := fractionDiv
   (fractionMul s.2,(multiply [false,true] (natBits s.1),[true]))
 def twiceOrder : Realizer (fun s : ScaleInput => multiply [false,true] (natBits s.1)) :=
   ((Realizer.constant [false,true]).pair (Realizer.fst.comp naturalWordRealizer)).comp multiplyRealizer
 def scaleWordsRealizer : Realizer scaleWords :=
   ((Realizer.snd.comp fractionMulRealizer).pair (twiceOrder.pair (Realizer.constant [true]))).comp fractionDivRealizer
 theorem twiceOrder_polynomial : PolyBound twiceOrder :=
   polynomial_comp (polynomial_pair (linear_polynomial (linear_constant [false,true]))
     (polynomial_comp (linear_polynomial linear_fst) naturalWord_polynomial)) multiply_polynomial
 theorem scaleWords_polynomial : PolyBound scaleWordsRealizer :=
   polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) fractionMul_polynomial)
     (polynomial_pair twiceOrder_polynomial (linear_polynomial (linear_constant [true])))) fractionDiv_polynomial
 theorem scaleWords_value (n : ℕ) (e m : FractionWords) :
     fractionValue (scaleWords (n,(e,m)))=fractionValue e*fractionValue m/(2*(n : ℚ)) := by
   dsimp only [scaleWords]
   rw [fractionDiv_value,fractionMul_value]
   have ht : fractionValue (multiply [false,true] (natBits n),[true])=2*(n : ℚ) := by
     simp [fractionValue,multiply_value,value_natBits,value]
   rw [ht]
 theorem scaleWords_positive (n : ℕ) (e m : FractionWords) (hn : 0< n)
     (heN : 0< value e.1) (heD : 0< value e.2) (hmN : 0< value m.1) (hmD : 0< value m.2) :
     0< value (scaleWords (n,(e,m))).1 ∧ 0< value (scaleWords (n,(e,m))).2 := by
   dsimp only [scaleWords,fractionDiv,fractionMul]
   have htwo : value [false,true]=2 := by decide
   have hone : value [true]=1 := by decide
   simp only [multiply_value,value_natBits,htwo,hone]
   constructor <;> positivity

 def roundingCounts (weights : List FractionWords) (tau : FractionWords) : List (List Bool) :=
   weights.map (fun w => quotientWords (w,tau))
 def roundingCountsRealizer : Realizer (fun s : List FractionWords×FractionWords => roundingCounts s.1 s.2) :=
   mapEnvironment quotientWordsRealizer
 theorem roundingCounts_polynomial : PolyBound roundingCountsRealizer := polynomial_mapEnvironment quotientWords_polynomial
 theorem roundingCounts_value (weights : List FractionWords) (tau : FractionWords)
     (hw : ∀w∈weights,0< value w.2) (ht : 0< value tau.1) :
     (roundingCounts weights tau).map value=weights.map (fun w => ⌊fractionValue w/fractionValue tau⌋₊) := by
   rw [roundingCounts,List.map_map]
   apply List.map_congr_left
   intro w hw'
   exact quotientWords_value w tau (hw w hw') ht

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RawRounding
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def clippedStream (s : WeightedRaw) : List FractionWords := s.2.2.1.map clipWords
 def clippedStreamRealizer : Realizer clippedStream := weightsProjection.comp (mapList clipWordsRealizer)
 def accuracyProjection : Realizer (fun s : WeightedRaw => s.2.2.2.2) :=
   ((Realizer.snd.comp Realizer.snd).comp Realizer.snd).comp Realizer.snd
 def maximumStreamRealizer : Realizer (fun s : WeightedRaw => maximumFraction (clippedStream s)) :=
   clippedStreamRealizer.comp maximumFractionRealizer
 def scaleStreamRealizer : Realizer (fun s : WeightedRaw => scaleWords (s.1,(s.2.2.2.2,maximumFraction (clippedStream s)))) :=
   (Realizer.fst.pair (accuracyProjection.pair maximumStreamRealizer)).comp scaleWordsRealizer
 def rawRounding (s : WeightedRaw) : FractionWords×List (List Bool) :=
   let W := clippedStream s
   let tau := scaleWords (s.1,(s.2.2.2.2,maximumFraction W))
   (tau,roundingCounts W tau)
 def rawRoundingRealizer : Realizer rawRounding :=
   scaleStreamRealizer.pair ((clippedStreamRealizer.pair scaleStreamRealizer).comp roundingCountsRealizer)
 theorem clippedStream_polynomial : PolyBound clippedStreamRealizer :=
   polynomial_comp (linear_polynomial (linear_comp (linear_comp linear_snd linear_snd) linear_fst))
     (polynomial_mapList clipWords_polynomial)
 theorem accuracyProjection_linear : Linear accuracyProjection :=
   linear_comp (linear_comp (linear_comp linear_snd linear_snd) linear_snd) linear_snd
 theorem maximumStream_polynomial : PolyBound maximumStreamRealizer := polynomial_comp clippedStream_polynomial maximumFraction_polynomial
 theorem scaleStream_polynomial : PolyBound scaleStreamRealizer :=
   polynomial_comp (polynomial_pair (linear_polynomial linear_fst)
     (polynomial_pair (linear_polynomial accuracyProjection_linear) maximumStream_polynomial)) scaleWords_polynomial
 theorem rawRounding_polynomial : PolyBound rawRoundingRealizer :=
   polynomial_pair scaleStream_polynomial (polynomial_comp (polynomial_pair clippedStream_polynomial scaleStream_polynomial) roundingCounts_polynomial)

 def codedWeights {n : ℕ} (w : Fin n → RationalCode) : List FractionWords := ((List.ofFn w).map codeWords).map clipWords
 theorem codedWeights_den {n : ℕ} (w : Fin n → RationalCode) : ∀a∈codedWeights w,0< value a.2 := by
   intro a ha
   obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ha
   obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
   simpa only [clipWords,codeWords,value_natBits] using q.positive
 theorem codedWeights_values {n : ℕ} (w : Fin n → RationalCode) : (codedWeights w).map fractionValue=List.ofFn (clippedValues w) := by
   simp only [codedWeights,List.map_map,List.map_ofFn,Function.comp_def,fractionValue_code,clippedValues]
   rfl
 theorem maximumStream_value {n : ℕ} (w : Fin n → RationalCode) :
     0< value (maximumFraction (codedWeights w)).2 ∧
     fractionValue (maximumFraction (codedWeights w))=maximumWeight (clippedValues w) := by
   have hh := maximumFraction_value (codedWeights w) (codedWeights_den w)
   rw [codedWeights_values] at hh
   exact hh
 theorem accuracy_unsigned_value (ε : RationalCode) (he : 0≤ε.value) : fractionValue (codeWords ε).2=ε.value := by
   have hd : (0 : ℚ)<ε.denominator := by exact_mod_cast ε.positive
   have hn : (0 : ℤ)≤ε.numerator := by
     have hh := (le_div_iff₀ hd).mp he
     simp only [zero_mul] at hh
     exact_mod_cast hh
   have hnn : ¬ε.numerator<0 := by omega
   have h := fractionValue_code ε
   simpa only [clipWords,codeWords,decide_eq_false hnn,Bool.false_eq_true,if_false,
     clippedCode,max_eq_left hn] using h

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RawRoundingCorrect
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack

 theorem fraction_numerator_pos (s : FractionWords) (h : 0< fractionValue s) : 0< value s.1 := by
   by_contra hn
   have hz : value s.1=0 := by omega
   simp [fractionValue,hz] at h

 theorem rawRounding_correct {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode)
     (tau : ℚ) (t : Fin n → ℕ) (hr : weightRounding (clippedValues w) ε.value=some (tau,t)) :
     fractionValue (rawRounding (weightedParse (weightedInput G w ε))).1=tau ∧
     ((rawRounding (weightedParse (weightedInput G w ε))).2).map value=List.ofFn t ∧
     0< value (rawRounding (weightedParse (weightedInput G w ε))).1.1 ∧
     0< value (rawRounding (weightedParse (weightedInput G w ε))).1.2 := by
   unfold weightRounding at hr
   split_ifs at hr with hbad
   simp only [not_or,not_not] at hbad
   rcases hbad with ⟨hn,hM,he,he1,hw⟩
   have hmax : 0 < maximumWeight (clippedValues w) := lt_of_not_ge hM
   have heps : 0<ε.value := lt_of_not_ge he
   have hpair := Option.some.inj hr
   have htau : ε.value*maximumWeight (clippedValues w)/(2*(n : ℚ))=tau := congrArg Prod.fst hpair
   have ht : (fun v => ⌊clippedValues w v/(ε.value*maximumWeight (clippedValues w)/(2*(n : ℚ)))⌋₊)=t := congrArg Prod.snd hpair
   have hmv := maximumStream_value w
   have hev := accuracy_unsigned_value ε heps.le
   have heN : 0< value (codeWords ε).2.1 := fraction_numerator_pos _ (by rw [hev]; exact heps)
   have heD : 0< value (codeWords ε).2.2 := by simpa only [codeWords,value_natBits] using ε.positive
   have hmN : 0< value (maximumFraction (codedWeights w)).1 := fraction_numerator_pos _ (by rw [hmv.2]; exact hmax)
   have hpositive := scaleWords_positive n (codeWords ε).2 (maximumFraction (codedWeights w))
     (by omega) heN heD hmN hmv.1
   have hscale : fractionValue (scaleWords (n,((codeWords ε).2,maximumFraction (codedWeights w))))=tau := by
     rw [scaleWords_value,hev,hmv.2,htau]
   rw [weightedParse_correct]
   change fractionValue (scaleWords (n,((codeWords ε).2,maximumFraction (codedWeights w))))=tau ∧
     (roundingCounts (codedWeights w) (scaleWords (n,((codeWords ε).2,maximumFraction (codedWeights w))))).map value=List.ofFn t ∧ _
   refine ⟨hscale,?_,hpositive⟩
   rw [roundingCounts_value _ _ (codedWeights_den w) hpositive.1,hscale]
   have heq : (codedWeights w).map (fun s => ⌊fractionValue s/tau⌋₊)=
       ((codedWeights w).map fractionValue).map (fun z => ⌊z/tau⌋₊) := by rw [List.map_map]; rfl
   rw [heq,codedWeights_values,List.map_ofFn]
   have ht' : (fun v => ⌊clippedValues w v/tau⌋₊)=t := by rwa [htau] at ht
   simpa only [Function.comp_def,ht']

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.HalfAccuracyCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
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

 def halfWords (s : SignedWords) : SignedWords := (s.1,(s.2.1,multiply [false,true] s.2.2))
 def halfWordsRealizer : Realizer halfWords := Realizer.fst.pair ((Realizer.snd.comp Realizer.fst).pair
   (((Realizer.constant [false,true]).pair (Realizer.snd.comp Realizer.snd)).comp multiplyRealizer))
 theorem halfWords_polynomial : PolyBound halfWordsRealizer :=
   polynomial_pair (linear_polynomial linear_fst)
     (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_fst))
       (polynomial_comp (polynomial_pair (linear_polynomial (linear_constant [false,true]))
         (linear_polynomial (linear_comp linear_snd linear_snd))) multiply_polynomial))
 theorem halfWords_code (q : RationalCode) : halfWords (codeWords q)=codeWords (halfAccuracy q) := by
   have he : multiply [false,true] (natBits q.denominator)=natBits (2*q.denominator) := by
     rw [canonical_eq_natBits (multiply [false,true] (natBits q.denominator)) (by exact trim_idem _),multiply_value,value_natBits]
     rfl
   simp only [halfWords,codeWords,halfAccuracy,he]
   rfl
 def halfBitsRealizer : Realizer (fun s : SignedWords => rawRationalBits (halfWords s)) := halfWordsRealizer.comp rawRationalBitsRealizer
 theorem halfBits_polynomial : PolyBound halfBitsRealizer := polynomial_comp halfWords_polynomial rawRationalBits_polynomial
 theorem halfBits_code (q : RationalCode) : rawRationalBits (halfWords (codeWords q))=(halfAccuracy q).bits := by
   rw [halfWords_code,rawRationalBits_code]

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

-- Solutions.PostprocessCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev CountParseInput := List Bool×ℕ
 def contextNatural : Realizer (fun x : CountParseInput => readNatural x.1.tail) := (Realizer.fst.comp BinaryAdder.tailBits).comp readNaturalRealizer
 def contextWords : Realizer (fun x : CountParseInput => (readWords (readNatural x.1.tail).1 (readNatural x.1.tail).2).1) :=
   (((contextNatural.comp Realizer.fst).pair (contextNatural.comp Realizer.snd)).comp readWordsRealizer).comp Realizer.fst
 def boundedWordValue : Realizer (fun x : List Bool×ℕ => cappedValue x.1 x.2) := cappedValueRealizer
 def parseCounts (ctx : List Bool) (cap : ℕ) : ℕ×List ℕ :=
   let p := readNatural ctx.tail
   (p.1,((readWords p.1 p.2).1).map (fun w => cappedValue w cap))
 def parseCountsRealizer : Realizer (fun s : CountParseInput => parseCounts s.1 s.2) :=
   (contextNatural.comp Realizer.fst).pair ((contextWords.pair Realizer.snd).comp (mapEnvironment boundedWordValue))
 theorem contextNatural_polynomial : PolyBound contextNatural := polynomial_comp
   (linear_polynomial (linear_comp linear_fst BinaryAdder.tailBits_linear)) readNatural_polynomial
 theorem contextWords_polynomial : PolyBound contextWords := polynomial_comp (polynomial_comp
   (polynomial_pair (polynomial_comp contextNatural_polynomial (linear_polynomial linear_fst))
     (polynomial_comp contextNatural_polynomial (linear_polynomial linear_snd))) readWords_polynomial) (linear_polynomial linear_fst)
 theorem parseCounts_polynomial : PolyBound parseCountsRealizer :=
   polynomial_pair (polynomial_comp contextNatural_polynomial (linear_polynomial linear_fst))
     (polynomial_comp (polynomial_pair contextWords_polynomial (linear_polynomial linear_snd)) (polynomial_mapEnvironment cappedValue_polynomial))

 def postWord : Realizer (fun L : List Bool => (readWord L).1) := readWordRealizer.comp Realizer.fst
 def postRemainder : Realizer (fun L : List Bool => (readWord L).2) := readWordRealizer.comp Realizer.snd
 def postCounts : Realizer (fun L : List Bool => parseCounts (readWord L).1 L.length) :=
   (postWord.pair listLength).comp parseCountsRealizer
 def postProjection : Realizer (fun L : List Bool => projectMask (parseCounts (readWord L).1 L.length).1
     (parseCounts (readWord L).1 L.length).2 (readWord L).2) :=
   ((postCounts.comp Realizer.fst).pair ((postCounts.comp Realizer.snd).pair postRemainder)).comp projectMaskRealizer
 def postprocess (L : List Bool) : List Bool :=
   let p := readWord L
   if p.1.headD false then let c := parseCounts p.1 L.length; projectMask c.1 c.2 p.2 else p.1.tail
 def postprocessRealizer : Realizer postprocess :=
   (((postWord.comp BinaryAdder.headBit).pair Realizer.id).comp (postProjection.choose (postWord.comp BinaryAdder.tailBits)))
 theorem postprocess_polynomial : PolyBound postprocessRealizer := by
   have hw : PolyBound postWord := polynomial_comp readWord_polynomial (linear_polynomial linear_fst)
   have hr : PolyBound postRemainder := polynomial_comp readWord_polynomial (linear_polynomial linear_snd)
   have hc : PolyBound postCounts := polynomial_comp (polynomial_pair hw listLength_polynomial) parseCounts_polynomial
   have hp : PolyBound postProjection := polynomial_comp (polynomial_pair (polynomial_comp hc (linear_polynomial linear_fst))
     (polynomial_pair (polynomial_comp hc (linear_polynomial linear_snd)) hr)) projectMask_polynomial
   exact polynomial_comp (polynomial_pair (polynomial_comp hw (linear_polynomial BinaryAdder.headBit_linear)) (linear_polynomial linear_id))
     (polynomial_choose hp (polynomial_comp hw (linear_polynomial BinaryAdder.tailBits_linear)))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PreprocessGuard
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def zeroWordRealizer : Realizer (fun A : List Bool => (trim A).isEmpty) :=
   ((trimRealizer.comp nonemptyBits).comp Realizer.not).congr (fun A => by simp only [Function.comp_apply,Bool.not_not])
 theorem zeroWord_polynomial : PolyBound zeroWordRealizer := by
   unfold zeroWordRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp trim_polynomial (linear_polynomial nonempty_linear)) (linear_polynomial linear_not)
 def smallCase (s : WeightedRaw) : Bool := decide (s.1≤1) || (trim (maximumFraction (clippedStream s)).1).isEmpty
 def smallOrder : Realizer (fun s : WeightedRaw => decide (s.1≤1)) := (Realizer.fst.pair (Realizer.constant 1)).comp Realizer.le
 def smallMaximum : Realizer (fun s : WeightedRaw => (trim (maximumFraction (clippedStream s)).1).isEmpty) :=
   (maximumStreamRealizer.comp Realizer.fst).comp zeroWordRealizer
 def smallCaseRealizer : Realizer smallCase := (smallOrder.pair smallMaximum).comp Realizer.or
 theorem smallCase_polynomial : PolyBound smallCaseRealizer :=
   polynomial_comp (polynomial_pair
     (polynomial_comp (polynomial_pair (linear_polynomial linear_fst) (linear_polynomial (linear_constant (1 : ℕ)))) nat_le_polynomial)
     (polynomial_comp (polynomial_comp maximumStream_polynomial (linear_polynomial linear_fst)) zeroWord_polynomial))
     (linear_polynomial linear_or)
 def guardedWords (s : WeightedRaw) : List (List Bool) := if smallCase s then [] else (rawRounding s).2
 def guardedWordsRealizer : Realizer guardedWords :=
   ((smallCaseRealizer.pair Realizer.id).comp (Realizer.nil.choose (rawRoundingRealizer.comp Realizer.snd)))
 theorem guardedWords_polynomial : PolyBound guardedWordsRealizer := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : WeightedRaw => ([] : List (List Bool)))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   exact polynomial_comp (polynomial_pair smallCase_polynomial (linear_polynomial linear_id))
     (polynomial_choose (linear_polynomial hn) (polynomial_comp rawRounding_polynomial (linear_polynomial linear_snd)))
 theorem zeroWord_iff (A : List Bool) : (trim A).isEmpty=true ↔ value A=0 := by
   constructor
   · intro h
     have hn : trim A=[] := List.isEmpty_iff.mp h
     rw [← trim_value,hn]
     rfl
   · intro h
     by_cases hn : trim A=[]
     · simp [hn]
     · have hp := BinaryGcd.value_positive (trim A) (trim_idem A) hn
       rw [trim_value,h] at hp
       omega
 theorem fraction_nonpos_iff (s : FractionWords) (hd : 0< value s.2) : fractionValue s≤0 ↔ value s.1=0 := by
   have hdq : (0 : ℚ)< value s.2 := by exact_mod_cast hd
   dsimp only [fractionValue]
   rw [div_le_iff₀ hdq]
   simp only [zero_mul]
   constructor
   · intro h
     have hn : value s.1≤0 := by exact_mod_cast h
     omega
   · intro h; simp [h]
 theorem smallCase_correct {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode) :
     smallCase (weightedParse (weightedInput G w ε))=true ↔ n≤1 ∨ maximumWeight (clippedValues w)≤0 := by
   rw [weightedParse_correct]
   change (decide (n≤1) || (trim (maximumFraction (codedWeights w)).1).isEmpty)=true ↔ _
   rw [Bool.or_eq_true,decide_eq_true_eq,zeroWord_iff,← fraction_nonpos_iff _ (maximumStream_value w).1,(maximumStream_value w).2]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PostprocessSemantics
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack

 theorem parseCounts_correct (n : ℕ) (ws : List (List Bool)) (cap : ℕ) (hlen : ws.length=n)
     (hc : ∀w∈ws,value w≤ cap) :
     parseCounts (true::(encodeNat n++wordArrayBits ws)) cap=(n,ws.map value) := by
   have hn : n≤(encodeNat n++wordArrayBits ws).length+1 := by
     have h := wordArrayBits_length ws
     simp only [List.length_append]
     omega
   have hw := readWords_bits ws []
   simp only [List.append_nil] at hw
   rw [hlen] at hw
   dsimp only [parseCounts]
   rw [List.tail_cons,readNatural_encoded n _ hn,hw]
   congr 1
   apply List.map_congr_left
   intro w hw
   rw [cappedValue_eq,Nat.min_eq_right (hc w hw)]

 theorem postprocess_small (output : List Bool) : postprocess (prefixBits (false::output))=output := by
   have hw := readWord_prefix (false::output) []
   simp only [List.append_nil] at hw
   rw [postprocess,hw]
   rfl

 theorem postprocess_large {n : ℕ} (t : Fin n → ℕ) (ws : List (List Bool))
     (hws : ws.map value=List.ofFn t) (J : Finset (Fin (totalCopies t))) (rest : List Bool) :
     postprocess (prefixBits (true::(encodeNat n++wordArrayBits ws))++(mask J++rest))=
       mask (originalVertices t J) := by
   let ctx := true::(encodeNat n++wordArrayBits ws)
   let L := prefixBits ctx++(mask J++rest)
   have hlen : ws.length=n := by have hh := congrArg List.length hws; simpa only [List.length_map,List.length_ofFn] using hh
   have hsum : (ws.map value).sum=totalCopies t := by rw [hws,List.sum_ofFn]; rfl
   have hcap : totalCopies t≤ L.length := by
     dsimp only [L]
     simp only [List.length_append,mask,List.length_ofFn]
     omega
   have hc : ∀w∈ws,value w≤ L.length := by
     intro w hw
     have hh := value_le_sum ws w hw
     rw [hsum] at hh
     omega
   have hp := parseCounts_correct n ws L.length hlen hc
   change postprocess L=_
   dsimp only [postprocess,L]
   rw [readWord_prefix]
   change projectMask (parseCounts ctx (prefixBits ctx++(mask J++rest)).length).1
     (parseCounts ctx (prefixBits ctx++(mask J++rest)).length).2 (mask J++rest)=_
   change projectMask (parseCounts ctx L.length).1 (parseCounts ctx L.length).2 (mask J++rest)=_
   rw [hp,hws,projectMask_correct]

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

-- Solutions.DecodeExpansion
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
variable {α : Type} [Coding α]

 def decodeSecondRealizer : Realizer (fun s : α×List (List Bool) => (s.1,s.2.map value)) :=
   Realizer.fst.pair (Realizer.snd.comp decodeWordsRealizer)
 theorem decodeSecond_expanded : Expanded (decodeSecondRealizer (α:=α)) (fun s => (s.2.map value).sum) := by
   obtain ⟨C,q,hC,hR⟩ := decodeWords_time
   refine ⟨C+200,q+1,by omega,?_⟩
   rintro ⟨a,ws⟩
   let z := volume (a,ws)+(ws.map value).sum+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hlen := length_volume ws
   have hbase : volume ws+(ws.map value).sum+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hinput : volume (a,ws)+volume a+volume ws≤3*z := by dsimp [z]; simp only [volume_pair]; omega
   have hNat : volume (ws.map value)≤3*z := by rw [natList_volume,List.length_map]; dsimp [z]; simp only [volume_pair]; omega
   have hq : z^q≤ z^(q+1) := Nat.pow_le_pow_right hz (by omega)
   have hp : z≤ z^(q+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+1)
   have ht := (hR ws).trans ((Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q)).trans (Nat.mul_le_mul_left C hq))
   constructor
   · dsimp only [decodeSecondRealizer]
     rw [Realizer.time_pair,Realizer.time_comp,Realizer.time_fst,Realizer.time_snd]
     change volume (a,ws)+2+(volume (a,ws)+2+decodeWordsRealizer.time ws+10*(volume ws+1))+
       20*(volume (a,ws)+volume a+volume (ws.map value)+1)≤(C+200)*z^(q+1)
     nlinarith only [ht,hinput,hNat,hp,hz]
   · change volume (a,ws.map value)≤(C+200)*z^(q+1)
     simp only [volume_pair]
     nlinarith only [hinput,hNat,hp,hz]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PreprocessCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev PreState := WeightedRaw×List ℕ
 def preOrder : Realizer (fun x : PreState => x.1.1) := Realizer.fst.comp Realizer.fst
 def preBits : Realizer (fun x : PreState => x.1.2.1) := (Realizer.fst.comp Realizer.snd).comp Realizer.fst
 def preAccuracy : Realizer (fun x : PreState => x.1.2.2.2) := ((Realizer.fst.comp Realizer.snd).comp Realizer.snd).comp Realizer.snd
 def preSmall : Realizer (fun x : PreState => smallCase x.1) := Realizer.fst.comp smallCaseRealizer
 def preSmallOrder : Realizer (fun x : PreState => decide (x.1.1≤1)) := Realizer.fst.comp smallOrder
 def preDirectMask : Realizer (fun x : PreState => x.1.2.2.1.map (fun s => !s.1)) :=
   (Realizer.fst.comp weightsProjection).comp (mapList nonnegativeInput)
 def preZeros : Realizer (fun x : PreState => List.replicate x.1.1 false) :=
   (preOrder.pair (Realizer.constant false)).comp replicateList
 def smallAnswer (s : WeightedRaw) : List Bool := if s.1≤1 then s.2.2.1.map (fun s => !s.1) else List.replicate s.1 false
 def preAnswer : Realizer (fun x : PreState => smallAnswer x.1) :=
   ((preSmallOrder.pair Realizer.id).comp (preDirectMask.choose preZeros)).congr (fun x => by simp [smallAnswer])
 def preSmallContext : Realizer (fun x : PreState => false::smallAnswer x.1) := preAnswer.comp falseCons
 def preWordContext : Realizer (fun x : PreState => encodeNat x.1.1++wordArrayBits (guardedWords x.1)) :=
   ((preOrder.comp naturalCodeRealizer).pair ((Realizer.fst.comp guardedWordsRealizer).comp wordArrayBitsRealizer)).comp appendBits
 def preLargeContext : Realizer (fun x : PreState => true::(encodeNat x.1.1++wordArrayBits (guardedWords x.1))) := preWordContext.comp prependTrue
 def contextBits (s : WeightedRaw) : List Bool :=
   if smallCase s then false::smallAnswer s else true::(encodeNat s.1++wordArrayBits (guardedWords s))
 def preContext : Realizer (fun x : PreState => contextBits x.1) := (preSmall.pair Realizer.id).comp (preSmallContext.choose preLargeContext)
 def preGraph : Realizer (fun x : PreState => roundedGraphCode (x.1.1,(x.1.2.1,x.2))) :=
   (preOrder.pair (preBits.pair Realizer.snd)).comp roundedGraphRealizer
 def preUnweightedInput : Realizer (fun x : PreState => roundedGraphCode (x.1.1,(x.1.2.1,x.2))++rawRationalBits (halfWords x.1.2.2.2)) :=
   (preGraph.pair (preAccuracy.comp halfBitsRealizer)).comp appendBits
 def smallPayload : Realizer (fun x : PreState => false::prefixBits (contextBits x.1)) := (preContext.comp prefixRealizer).comp falseCons
 def largePayload : Realizer (fun x : PreState => true::(prefixBits (contextBits x.1)++
     (roundedGraphCode (x.1.1,(x.1.2.1,x.2))++rawRationalBits (halfWords x.1.2.2.2)))) :=
   (((preContext.comp prefixRealizer).pair preUnweightedInput).comp appendBits).comp prependTrue
 def afterPreprocess (s : PreState) : List Bool :=
   if smallCase s.1 then false::prefixBits (contextBits s.1) else true::(prefixBits (contextBits s.1)++
     (roundedGraphCode (s.1.1,(s.1.2.1,s.2))++rawRationalBits (halfWords s.1.2.2.2)))
 def afterPreprocessRealizer : Realizer afterPreprocess := (preSmall.pair Realizer.id).comp (smallPayload.choose largePayload)

 theorem afterPreprocess_polynomial : PolyBound afterPreprocessRealizer := by
   have hn : PolyBound preOrder := linear_polynomial (linear_comp linear_fst linear_fst)
   have hb : PolyBound preBits := linear_polynomial (linear_comp (linear_comp linear_fst linear_snd) linear_fst)
   have he : PolyBound preAccuracy := linear_polynomial (linear_comp (linear_comp (linear_comp linear_fst linear_snd) linear_snd) linear_snd)
   have hs : PolyBound preSmall := polynomial_comp (linear_polynomial linear_fst) smallCase_polynomial
   have hso : PolyBound preSmallOrder := polynomial_comp (linear_polynomial linear_fst)
     (polynomial_comp (polynomial_pair (linear_polynomial linear_fst) (linear_polynomial (linear_constant (1 : ℕ)))) nat_le_polynomial)
   have hd : PolyBound preDirectMask := polynomial_comp
     (linear_polynomial (linear_comp linear_fst (linear_comp (linear_comp linear_snd linear_snd) linear_fst)))
     (polynomial_mapList (linear_polynomial (linear_comp linear_fst linear_not)))
   have hz : PolyBound preZeros := polynomial_comp (polynomial_pair hn (linear_polynomial (linear_constant false))) replicateList_polynomial
   have ha : PolyBound preAnswer := by
     unfold preAnswer
     apply polynomial_congr
     exact polynomial_comp (polynomial_pair hso (linear_polynomial linear_id)) (polynomial_choose hd hz)
   have hcSmall : PolyBound preSmallContext := polynomial_comp ha (linear_polynomial falseCons_linear)
   have hcWords : PolyBound preWordContext := polynomial_comp
     (polynomial_pair (polynomial_comp hn naturalCode_polynomial)
       (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) guardedWords_polynomial) wordArrayBits_polynomial)) appendBits_polynomial
   have hcLarge : PolyBound preLargeContext := polynomial_comp hcWords (linear_polynomial prependTrue_linear)
   have hc : PolyBound preContext := polynomial_comp (polynomial_pair hs (linear_polynomial linear_id)) (polynomial_choose hcSmall hcLarge)
   have hg : PolyBound preGraph := polynomial_comp (polynomial_pair hn (polynomial_pair hb (linear_polynomial linear_snd))) roundedGraph_polynomial
   have hu : PolyBound preUnweightedInput := polynomial_comp (polynomial_pair hg (polynomial_comp he halfBits_polynomial)) appendBits_polynomial
   have hps : PolyBound smallPayload := polynomial_comp (polynomial_comp hc prefix_polynomial) (linear_polynomial falseCons_linear)
   have hpl : PolyBound largePayload := polynomial_comp (polynomial_comp (polynomial_pair (polynomial_comp hc prefix_polynomial) hu) appendBits_polynomial)
     (linear_polynomial prependTrue_linear)
   exact polynomial_comp (polynomial_pair hs (linear_polynomial linear_id)) (polynomial_choose hps hpl)

 def parseGuardedRealizer : Realizer (fun L : List Bool => (weightedParse L,guardedWords (weightedParse L))) :=
   weightedParseRealizer.pair (weightedParseRealizer.comp guardedWordsRealizer)
 theorem parseGuarded_polynomial : PolyBound parseGuardedRealizer :=
   polynomial_pair weightedParse_polynomial (polynomial_comp weightedParse_polynomial guardedWords_polynomial)
 def preprocessing (L : List Bool) : List Bool := afterPreprocess (weightedParse L,(guardedWords (weightedParse L)).map value)
 def preprocessingRealizer : Realizer preprocessing := (parseGuardedRealizer.comp decodeSecondRealizer).comp afterPreprocessRealizer
 def expansionSize (L : List Bool) : ℕ := ((guardedWords (weightedParse L)).map value).sum
 theorem preprocessing_expanded : Expanded preprocessingRealizer expansionSize :=
   expanded_comp (polynomial_comp_expanded parseGuarded_polynomial decodeSecond_expanded) afterPreprocess_polynomial

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PreprocessSemantics
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack

 theorem preprocessing_small (L : List Bool) (hs : smallCase (weightedParse L)=true) :
     preprocessing L=false::prefixBits (false::smallAnswer (weightedParse L)) := by
   simp only [preprocessing,guardedWords,hs,if_true,List.map_nil,afterPreprocess,contextBits]
 theorem expansionSize_small (L : List Bool) (hs : smallCase (weightedParse L)=true) : expansionSize L=0 := by
   simp only [expansionSize,guardedWords,hs,if_true,List.map_nil,List.sum_nil]
 theorem smallAnswer_direct {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode) (hn : n≤1) :
     smallAnswer (weightedParse (weightedInput G w ε))=mask (directVertices w) := by
   rw [smallAnswer]
   have hn' : (weightedParse (weightedInput G w ε)).1≤1 := by rw [weightedParse_correct]; exact hn
   rw [if_pos hn',directMask_correct]
 theorem smallAnswer_empty {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode) (hn : 2≤ n) :
     smallAnswer (weightedParse (weightedInput G w ε))=mask (∅ : Finset (Fin n)) := by
   rw [smallAnswer,weightedParse_correct,if_neg (by omega : ¬n≤1)]
   simp [mask]
 theorem rounding_not_small {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode)
     (tau : ℚ) (t : Fin n → ℕ) (hr : weightRounding (clippedValues w) ε.value=some (tau,t)) :
     smallCase (weightedParse (weightedInput G w ε))=false := by
   have hnot : ¬(n≤1 ∨ maximumWeight (clippedValues w)≤0) := by
     intro hs
     have hb : n≤1 ∨ maximumWeight (clippedValues w)≤0 ∨ ε.value≤0 ∨ 1≤ε.value ∨ ¬(∀v,0≤ clippedValues w v) := by
       rcases hs with h|h
       · exact Or.inl h
       · exact Or.inr (Or.inl h)
     simp only [weightRounding,hb,if_true,reduceCtorEq] at hr
   cases hs : smallCase (weightedParse (weightedInput G w ε)) with
   | false => rfl
   | true => exact False.elim (hnot ((smallCase_correct G w ε).mp hs))
 theorem guardedWords_large {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode)
     (tau : ℚ) (t : Fin n → ℕ) (hr : weightRounding (clippedValues w) ε.value=some (tau,t)) :
     (guardedWords (weightedParse (weightedInput G w ε))).map value=List.ofFn t := by
   simp only [guardedWords,rounding_not_small G w ε tau t hr,Bool.false_eq_true,if_false]
   exact (rawRounding_correct G w ε tau t hr).2.1
 theorem expansionSize_large {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode)
     (tau : ℚ) (t : Fin n → ℕ) (hr : weightRounding (clippedValues w) ε.value=some (tau,t)) :
     expansionSize (weightedInput G w ε)=totalCopies t := by
   rw [expansionSize,guardedWords_large G w ε tau t hr,List.sum_ofFn]
   rfl
 theorem preprocessing_large {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode)
     (tau : ℚ) (t : Fin n → ℕ) (hr : weightRounding (clippedValues w) ε.value=some (tau,t)) :
     preprocessing (weightedInput G w ε)=true::(prefixBits
       (true::(encodeNat n++wordArrayBits (guardedWords (weightedParse (weightedInput G w ε)))) )++
         unweightedInput (roundedGraph G t) (halfAccuracy ε)) := by
   have hs := rounding_not_small G w ε tau t hr
   have hc := guardedWords_large G w ε tau t hr
   dsimp only [preprocessing]
   rw [hc]
   dsimp only [afterPreprocess]
   simp only [hs,Bool.false_eq_true,if_false]
   dsimp only [contextBits]
   simp only [hs,Bool.false_eq_true,if_false]
   rw [weightedParse_correct]
   rw [roundedGraphCode_correct,halfBits_code]
   rfl

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ExpandedProgram
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.TreeToTM2
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem realizer_expanded_program {f : List Bool → List Bool} (R : Realizer f) (N : List Bool → ℕ) (hR : Expanded R N) :
     ∃ (P : EdgeSublinearMWIS.Main.Program) (K q : ℕ),0< K ∧ 0< q ∧
       ∀ input, Runs P input (f input) (K*(input.length+N input+1)^q) := by
   obtain ⟨C,q,hC,hR⟩ := hR
   let F := routineFactor R.routine
   refine ⟨routineProgram R.routine,F*(2*C*5^q+2),q+1,?_,by omega,?_⟩
   · dsimp [F,routineFactor]; positivity
   · intro input
     have hRun := routine_runs R.routine input (f input) (R.correct input)
     apply runs_mono _ _ _ hRun
     let z := input.length+N input+1
     have hz : 1≤ z := by dsimp [z]; omega
     have hv := EdgeSublinearMWIS.Main.BinaryAdder.volume_bits input
     have hi : volume input+N input+1≤5*z := by dsimp [z]; omega
     have hp := Nat.pow_le_pow_left hi q
     rw [mul_pow] at hp
     have hq : z^q≤ z^(q+1) := Nat.pow_le_pow_right hz (by omega)
     have hqp : (volume input+N input+1)^q≤5^q*z^(q+1) := hp.trans (Nat.mul_le_mul_left _ hq)
     have ht := ((hR input).1).trans (Nat.mul_le_mul_left C hqp)
     have ho := ((hR input).2).trans (Nat.mul_le_mul_left C hqp)
     have hl := length_volume (f input)
     have hze : z≤ z^(q+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+1)
     have hin : input.length+1≤ z^(q+1) := (show input.length+1≤ z by dsimp [z]; omega).trans hze
     have hs : R.time input+input.length+(f input).length+1≤(2*C*5^q+2)*z^(q+1) := by
       nlinarith only [ht,ho,hl,hin]
     change F*(R.time input+input.length+(f input).length+1)≤ F*(2*C*5^q+2)*z^(q+1)
     simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left F hs

end EdgeSublinearMWIS.Main.TreeToTM2
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

-- Solutions.ContextCall
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 inductive Extra where | raw | context | count | consume | temp deriving Fintype,DecidableEq
 inductive CallPhase where | count | context | out | into | emitContext | prefix deriving Fintype,DecidableEq
 abbrev CallK (U : Program) := U.machine.tm.K⊕Extra
 abbrev CallΓ (U : Program) : CallK U → Type := StackSum U.machine.tm.Γ (fun _ : Extra => Bool)
 abbrev CallΛ (U : Program) := U.machine.tm.Λ⊕CallPhase
 abbrev Callσ (U : Program) := U.machine.tm.σ×Option Bool
 def callCarry {U : Program} (v : Callσ U) (a : Option Bool) : Callσ U := (v.1,a)
 def callNext {U : Program} (p : CallPhase) : Stmt (CallΓ U) (CallΛ U) (Callσ U) :=
   .load (fun v => callCarry v none) (.goto (fun _ => .inr p))
 def callCode (U : Program) : CallΛ U → Stmt (CallΓ U) (CallΛ U) (Callσ U)
   | .inl l => extendStmt .emitContext (U.machine.tm.m l)
   | .inr .count =>
     .pop (.inr .raw) (fun v a => callCarry v a)
       (.branch (fun v => v.2.getD false)
         (.push (.inr .count) (fun _ => true) (.push (.inr .consume) (fun _ => true) (callNext .count)))
         (callNext .context))
   | .inr .context =>
     .pop (.inr .consume) (fun v a => callCarry v a)
       (.branch (fun v => v.2.isSome)
         (.pop (.inr .raw) (fun v a => callCarry v a)
           (.push (.inr .context) (fun v => v.2.getD false) (callNext .context)))
         (callNext .out))
   | .inr .out =>
     .pop (.inr .raw) (fun v a => callCarry v a)
       (.branch (fun v => v.2.isSome)
         (.push (.inr .temp) (fun v => v.2.getD false) (callNext .out))
         (callNext .into))
   | .inr .into =>
     .pop (.inr .temp) (fun v a => callCarry v a)
       (.branch (fun v => v.2.isSome)
         (.push (.inl U.machine.tm.k₀) (fun v => U.machine.inputAlphabet.symm (v.2.getD false)) (callNext .into))
         (.load (fun _ => (U.machine.tm.initialState,none)) (.goto (fun _ => .inl U.machine.tm.main))))
   | .inr .emitContext =>
     .pop (.inr .context) (fun v a => callCarry v a)
       (.branch (fun v => v.2.isSome)
         (.push (.inl U.machine.tm.k₁) (fun v => U.machine.outputAlphabet.symm (v.2.getD false)) (callNext .emitContext))
         (.push (.inl U.machine.tm.k₁) (fun _ => U.machine.outputAlphabet.symm false) (callNext .prefix)))
   | .inr .prefix =>
     .pop (.inr .count) (fun v a => callCarry v a)
       (.branch (fun v => v.2.isSome)
         (.push (.inl U.machine.tm.k₁) (fun _ => U.machine.outputAlphabet.symm true) (callNext .prefix))
         (.load (fun _ => (U.machine.tm.initialState,none)) .halt))

 noncomputable instance callAlphabet (U : Program) (k : CallK U) : Fintype (CallΓ U k) :=
   @Fintype.ofFinite _ (by cases k with | inl k => exact U.finiteAlphabet k | inr k => change Finite Bool; infer_instance)
 def callTM (U : Program) : Turing.FinTM2 where
   K := CallK U
   Γ := CallΓ U
   Λ := CallΛ U
   σ := Callσ U
   k₀ := .inr .raw
   k₁ := .inl U.machine.tm.k₁
   initialState := (U.machine.tm.initialState,none)
   main := .inr .count
   m := callCode U
 def callWithContext (U : Program) : Program where
   machine := ⟨callTM U,(by change Bool ≃ Bool; exact Equiv.refl _),
     (by change U.machine.tm.Γ U.machine.tm.k₁ ≃ Bool; exact U.machine.outputAlphabet)⟩
   finiteAlphabet k := by cases k with | inl k => exact U.finiteAlphabet k | inr k => change Finite Bool; infer_instance

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ContextState
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

 def extraStore (R C N D T : List Bool) : Extra → List Bool
   | .raw => R
   | .context => C
   | .count => N
   | .consume => D
   | .temp => T
 def callCfg (U : Program) (p : CallPhase) (S : ∀k,List (U.machine.tm.Γ k)) (R C N D T : List Bool) : (callTM U).Cfg :=
   cfg (some (.inr p)) (U.machine.tm.initialState,none) (extendStore S (extraStore R C N D T))
 theorem update_extend_right {κ μ : Type} [DecidableEq κ] [DecidableEq μ] {Γ : κ → Type} {Δ : μ → Type}
     (S : ∀k,List (Γ k)) (E : ∀k,List (Δ k)) (e : μ) (L : List (Δ e)) :
     Function.update (extendStore S E) (.inr e) L=extendStore S (Function.update E e L) := by
   funext k
   cases k with
   | inl k => simp [Function.update,extendStore]
   | inr j =>
     by_cases h : j=e
     · subst j; simp [Function.update,extendStore]
     · simp [Function.update,extendStore,h]

 theorem count_step_true (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R C N D T : List Bool) :
     step (callCode U) (callCfg U .count S (true::R) C N D T)=
       some (callCfg U .count S R C (true::N) (true::D) T) := by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.getD_some,cond_true]
   simp only [update_extend_right,Function.update_of_ne (by decide : Extra.count≠Extra.raw),
     Function.update_of_ne (by decide : Extra.consume≠Extra.raw),Function.update_of_ne (by decide : Extra.consume≠Extra.count)]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]

 theorem count_step_false (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R C N D T : List Bool) :
     step (callCode U) (callCfg U .count S (false::R) C N D T)=some (callCfg U .context S R C N D T) := by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.getD_some,cond_false]
   rw [update_extend_right]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ContextSteps
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

 theorem context_step_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b d : Bool) (R C N D T : List Bool) :
     step (callCode U) (callCfg U .context S (b::R) C N (d::D) T)=
       some (callCfg U .context S R (b::C) N D T) := by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true,Option.getD_some]
   simp only [update_extend_right,Function.update_of_ne (by decide : Extra.raw≠Extra.consume),
     Function.update_of_ne (by decide : Extra.context≠Extra.consume),Function.update_of_ne (by decide : Extra.context≠Extra.raw)]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 theorem context_step_nil (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R C N T : List Bool) :
     step (callCode U) (callCfg U .context S R C N [] T)=some (callCfg U .out S R C N [] T) := by
   simp [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extraStore,extendStore,Function.update]
 theorem call_out_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b : Bool) (R C N D T : List Bool) :
     step (callCode U) (callCfg U .out S (b::R) C N D T)=some (callCfg U .out S R C N D (b::T)) := by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true,Option.getD_some]
   simp only [update_extend_right,Function.update_of_ne (by decide : Extra.temp≠Extra.raw)]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 theorem call_out_nil (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (C N D T : List Bool) :
     step (callCode U) (callCfg U .out S [] C N D T)=some (callCfg U .into S [] C N D T) := by
   simp [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extraStore,extendStore,Function.update]

 theorem call_into_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b : Bool) (R C N D T : List Bool) :
     step (callCode U) (callCfg U .into S R C N D (b::T))=some (callCfg U .into
       (Function.update S U.machine.tm.k₀ (U.machine.inputAlphabet.symm b::S U.machine.tm.k₀)) R C N D T) := by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true,Option.getD_some]
   rw [update_extend_right]
   simp only [extendStore_inl]
   rw [update_extend]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 theorem call_into_nil (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R C N D : List Bool) :
     step (callCode U) (callCfg U .into S R C N D [])=
       some (extendCfg .emitContext (none : Option Bool) (extraStore R C N D [])
         (cfg (some U.machine.tm.main) U.machine.tm.initialState S)) := by
   simp [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extraStore,extendStore,Function.update,extendCfg]

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ContextEmission
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

 theorem emit_context_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b : Bool) (R C N D T : List Bool) :
     step (callCode U) (callCfg U .emitContext S R (b::C) N D T)=some (callCfg U .emitContext
       (Function.update S U.machine.tm.k₁ (U.machine.outputAlphabet.symm b::S U.machine.tm.k₁)) R C N D T) := by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true,Option.getD_some]
   rw [update_extend_right]
   simp only [extendStore_inl]
   rw [update_extend]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 theorem emit_context_nil (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R N D T : List Bool) :
     step (callCode U) (callCfg U .emitContext S R [] N D T)=some (callCfg U .prefix
       (Function.update S U.machine.tm.k₁ (U.machine.outputAlphabet.symm false::S U.machine.tm.k₁)) R [] N D T) := by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_nil,List.tail_nil,Option.isSome_none,cond_false]
   rw [update_extend_right]
   simp only [extendStore_inl]
   rw [update_extend]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 theorem prefix_step_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b : Bool) (R C N D T : List Bool) :
     step (callCode U) (callCfg U .prefix S R C (b::N) D T)=some (callCfg U .prefix
       (Function.update S U.machine.tm.k₁ (U.machine.outputAlphabet.symm true::S U.machine.tm.k₁)) R C N D T) := by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true]
   rw [update_extend_right]
   simp only [extendStore_inl]
   rw [update_extend]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 def callHaltCfg (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R C D T : List Bool) : (callTM U).Cfg :=
   cfg none (U.machine.tm.initialState,none) (extendStore S (extraStore R C [] D T))
 theorem prefix_step_nil (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R C D T : List Bool) :
     step (callCode U) (callCfg U .prefix S R C [] D T)=some (callHaltCfg U S R C D T) := by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_nil,List.tail_nil,Option.isSome_none,cond_false,callHaltCfg]
   rw [update_extend_right]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]

 theorem callHalt_only (U : Program) (output : List Bool) :
     callHaltCfg U (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) [] [] [] []=
       Turing.haltList (callTM U) (output.map U.machine.outputAlphabet.symm) := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change extendStore (onlyStack U.machine.tm.k₁ _) (extraStore [] [] [] [] [])=(Turing.haltList (callTM U) _).stk
   rw [haltList_store]
   funext k
   cases k with
   | inl k =>
     by_cases h : k=U.machine.tm.k₁
     · subst k; simp [onlyStack,Function.update,extendStore,callTM]
     · simp [onlyStack,Function.update,extendStore,callTM,h]
   | inr e => cases e <;> simp [onlyStack,Function.update,extendStore,callTM,extraStore]

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ContextReadLoops
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

 theorem count_loop (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (n : ℕ) (rest C N D T : List Bool) :
     run (callCode U) (callCfg U .count S (List.replicate n true++false::rest) C N D T) (n+1)=
       some (callCfg U .context S rest C (List.replicate n true++N) (List.replicate n true++D) T) := by
   induction n generalizing N D with
   | zero => exact count_step_false U S rest C N D T
   | succ n ih =>
     simp only [List.replicate_succ,List.cons_append]
     rw [run_first,count_step_true,Option.bind_some]
     have hh := ih (true::N) (true::D)
     have hn : ∀L : List Bool,List.replicate n true++true::L=true::(List.replicate n true++L) := by
       intro L
       calc
         _ = (List.replicate n true++[true])++L := by simp
         _ = List.replicate (n+1) true++L := by rw [List.replicate_succ']
         _ = _ := rfl
     simpa only [hn] using hh
 theorem context_loop (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (L rest C N T : List Bool) :
     run (callCode U) (callCfg U .context S (L++rest) C N (List.replicate L.length true) T) (L.length+1)=
       some (callCfg U .out S rest (L.reverse++C) N [] T) := by
   induction L generalizing C with
   | nil => exact context_step_nil U S rest C N T
   | cons b L ih =>
     simp only [List.length_cons,List.replicate_succ,List.cons_append]
     rw [run_first,context_step_cons,Option.bind_some]
     have hh := ih (b::C)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
 theorem call_out_loop (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (L C N D T : List Bool) :
     run (callCode U) (callCfg U .out S L C N D T) (L.length+1)=
       some (callCfg U .into S [] C N D (L.reverse++T)) := by
   induction L generalizing T with
   | nil => exact call_out_nil U S C N D T
   | cons b L ih =>
     rw [List.length_cons,run_first,call_out_cons,Option.bind_some]
     have hh := ih (b::T)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh

 theorem inputCfg_only (U : Program) (input : List Bool) :
     cfg (some U.machine.tm.main) U.machine.tm.initialState
       (onlyStack U.machine.tm.k₀ (input.map U.machine.inputAlphabet.symm))=
       Turing.initList U.machine.tm (input.map U.machine.inputAlphabet.symm) := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   exact (initList_store _ _).symm
 theorem call_into_loop (U : Program) (L acc R C N D : List Bool) :
     run (callCode U) (callCfg U .into (onlyStack U.machine.tm.k₀ (acc.map U.machine.inputAlphabet.symm)) R C N D L) (L.length+1)=
       some (extendCfg .emitContext (none : Option Bool) (extraStore R C N D [])
         (Turing.initList U.machine.tm ((L.reverse++acc).map U.machine.inputAlphabet.symm))) := by
   induction L generalizing acc with
   | nil =>
     have hh := call_into_nil U (onlyStack U.machine.tm.k₀ (acc.map U.machine.inputAlphabet.symm)) R C N D
     rw [inputCfg_only] at hh
     exact hh
   | cons b L ih =>
     rw [List.length_cons,run_first,call_into_cons,onlyStack_self,onlyStack_update,Option.bind_some]
     have hh := ih (b::acc)
     simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hh

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ContextWriteLoops
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

 theorem emit_context_loop (U : Program) (C output R N D T : List Bool) :
     run (callCode U) (callCfg U .emitContext
       (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) R C N D T) (C.length+1)=
       some (callCfg U .prefix (onlyStack U.machine.tm.k₁
         ((false::(C.reverse++output)).map U.machine.outputAlphabet.symm)) R [] N D T) := by
   induction C generalizing output with
   | nil =>
     have hh := emit_context_nil U (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) R N D T
     rw [onlyStack_self,onlyStack_update] at hh
     exact hh
   | cons b C ih =>
     rw [List.length_cons,run_first,emit_context_cons,onlyStack_self,onlyStack_update,Option.bind_some]
     have hh := ih (b::output)
     simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hh
 theorem prefix_loop (U : Program) (n : ℕ) (output : List Bool) :
     run (callCode U) (callCfg U .prefix (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm))
       [] [] (List.replicate n true) [] []) (n+1)=
       some (Turing.haltList (callTM U) ((List.replicate n true++output).map U.machine.outputAlphabet.symm)) := by
   induction n generalizing output with
   | zero =>
     have hh := prefix_step_nil U (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) [] [] [] []
     rw [callHalt_only] at hh
     exact hh
   | succ n ih =>
     rw [List.replicate_succ,run_first,prefix_step_cons,onlyStack_self,onlyStack_update,Option.bind_some]
     have hh := ih (true::output)
     have he : List.replicate n true++true::output=List.replicate (n+1) true++output := by
       rw [List.replicate_succ',List.append_assoc,List.singleton_append]
     simpa only [List.map_cons,he,List.replicate_succ,List.cons_append] using hh

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ContextCallRuns
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

 theorem call_start (U : Program) (ctx input : List Bool) :
     Turing.initList (callTM U) (prefixBits ctx++input)=
       callCfg U .count (fun _ => []) (List.replicate ctx.length true++false::(ctx++input)) [] [] [] [] := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   rw [initList_store]
   funext k
   cases k with
   | inl k => simp [callTM,callCfg,cfg,onlyStack,Function.update,extendStore]
   | inr e => cases e <;> simp [callTM,callCfg,cfg,onlyStack,Function.update,extendStore,extraStore,prefixBits,List.append_assoc]
 theorem call_after_halt (U : Program) (ctx output : List Bool) :
     extendCfg .emitContext (none : Option Bool) (extraStore [] ctx.reverse (List.replicate ctx.length true) [] [])
       (Turing.haltList U.machine.tm (output.map U.machine.outputAlphabet.symm))=
         callCfg U .emitContext (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm))
           [] ctx.reverse (List.replicate ctx.length true) [] [] := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change extendStore (Turing.haltList U.machine.tm _).stk _=extendStore (onlyStack U.machine.tm.k₁ _) _
   rw [haltList_store]

 theorem call_context_runs (U : Program) (ctx input output : List Bool) (T : ℕ) (hU : Runs U input output T) :
     Runs (callWithContext U) (prefixBits ctx++input) (prefixBits ctx++output)
       (T+4*ctx.length+2*input.length+6) := by
   change Nonempty (Turing.TM2OutputsInTime (callTM U) ((prefixBits ctx++input).map id)
     (some ((prefixBits ctx++output).map U.machine.outputAlphabet.symm)) (T+4*ctx.length+2*input.length+6))
   rw [List.map_id]
   obtain ⟨t,ht,hu⟩ := outputs_run U input output T hU
   let S : ∀k,List (U.machine.tm.Γ k) := fun _ => []
   let N := List.replicate ctx.length true
   have h1 := count_loop U S ctx.length (ctx++input) [] [] [] []
   simp only [List.append_nil] at h1
   rw [← call_start] at h1
   have h2 := context_loop U S ctx input [] N []
   simp only [List.append_nil] at h2
   have h3 := call_out_loop U S input ctx.reverse N [] []
   simp only [List.append_nil] at h3
   have h4 := call_into_loop U input.reverse [] [] ctx.reverse N []
   simp only [List.map_nil,onlyStack_nil,List.reverse_reverse,List.append_nil,List.length_reverse] at h4
   have h5 := run_extend .emitContext U.machine.tm.m (callCode U) (fun _ => rfl) _ _ (none : Option Bool)
     (extraStore [] ctx.reverse N [] []) t hu
   rw [call_after_halt] at h5
   have h6 := emit_context_loop U ctx.reverse output [] N [] []
   simp only [List.reverse_reverse,List.length_reverse] at h6
   have h7 := prefix_loop U ctx.length (false::(ctx++output))
   have hr := run_trans _ _ _ _ _ _ h1 h2
   have hr := run_trans _ _ _ _ _ _ hr h3
   have hr := run_trans _ _ _ _ _ _ hr h4
   have hr := run_trans _ _ _ _ _ _ hr h5
   have hr := run_trans _ _ _ _ _ _ hr h6
   have hr := run_trans _ _ _ _ _ _ hr h7
   have he : List.replicate ctx.length true++false::(ctx++output)=prefixBits ctx++output := by
     simp only [prefixBits,List.append_assoc,List.cons_append]
   rw [he] at hr
   obtain ⟨hrun⟩ := RawStack.outputs (tm:=callTM U) (prefixBits ctx++input)
     ((prefixBits ctx++output).map U.machine.outputAlphabet.symm) _ hr
   refine ⟨{hrun with steps_le_m := hrun.steps_le_m.trans ?_}⟩
   omega

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ProgramLabelMap
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
variable {κ Λ Ω σ : Type} [DecidableEq κ] {Γ : κ → Type}

 def labelCfg (inj : Λ → Ω) (c : Cfg Γ Λ σ) : Cfg Γ Ω σ := ⟨c.l.map inj,c.var,c.stk⟩
 def labelStmt (inj : Λ → Ω) : Stmt Γ Λ σ → Stmt Γ Ω σ
   | .push k f q => .push k f (labelStmt inj q)
   | .pop k f q => .pop k f (labelStmt inj q)
   | .peek k f q => .peek k f (labelStmt inj q)
   | .load f q => .load f (labelStmt inj q)
   | .branch f q r => .branch f (labelStmt inj q) (labelStmt inj r)
   | .goto f => .goto (inj ∘ f)
   | .halt => .halt
 theorem stepAux_label (inj : Λ → Ω) (q : Stmt Γ Λ σ) (v : σ) (S : ∀k,List (Γ k)) :
     stepAux (labelStmt inj q) v S=labelCfg inj (stepAux q v S) := by
   induction q generalizing v S with
   | push k f q ih => exact ih _ _
   | pop k f q ih => exact ih _ _
   | peek k f q ih => exact ih _ _
   | load f q ih => exact ih _ _
   | branch f q r iq ir =>
     cases hf : f v <;> simp only [labelStmt,stepAux,hf,cond_true,cond_false] <;> first | exact iq v S | exact ir v S
   | goto f => rfl
   | halt => rfl
 theorem step_label (inj : Λ → Ω) (code : Λ → Stmt Γ Λ σ) (target : Ω → Stmt Γ Ω σ)
     (hc : ∀l,target (inj l)=labelStmt inj (code l)) (c : Cfg Γ Λ σ) :
     step target (labelCfg inj c)=(step code c).map (labelCfg inj) := by
   rcases c with ⟨l,v,S⟩
   cases l with
   | none => rfl
   | some l => simp only [labelCfg,Option.map_some,step,hc]; exact congrArg some (stepAux_label inj (code l) v S)
 theorem run_label (inj : Λ → Ω) (code : Λ → Stmt Γ Λ σ) (target : Ω → Stmt Γ Ω σ)
     (hc : ∀l,target (inj l)=labelStmt inj (code l)) (c : Cfg Γ Λ σ) (t : ℕ) :
     RawStack.run target (labelCfg inj c) t=(RawStack.run code c t).map (labelCfg inj) := by
   induction t with
   | zero => rfl
   | succ t ih =>
     rw [RawStack.run,ih,RawStack.run]
     cases hr : RawStack.run code c t with
     | none => rfl
     | some d => simp only [Option.map_some,Option.bind_some,step_label inj code target hc,Option.map_bind]

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.GatedContextCall
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 inductive GatePhase where | gate | out | into deriving Fintype,DecidableEq
 abbrev GatedΛ (U : Program) := CallΛ U⊕GatePhase
 def gateNext {U : Program} (p : GatePhase) : Stmt (CallΓ U) (GatedΛ U) (Callσ U) :=
   .load (fun v => callCarry v none) (.goto (fun _ => .inr p))
 def gateCode (U : Program) : GatedΛ U → Stmt (CallΓ U) (GatedΛ U) (Callσ U)
   | .inl l => labelStmt Sum.inl (callCode U l)
   | .inr .gate =>
     .pop (.inr .raw) (fun v a => callCarry v a)
       (.branch (fun v => v.2.getD false)
         (.load (fun v => callCarry v none) (.goto (fun _ => .inl (.inr .count))))
         (gateNext .out))
   | .inr .out =>
     .pop (.inr .raw) (fun v a => callCarry v a)
       (.branch (fun v => v.2.isSome)
         (.push (.inr .temp) (fun v => v.2.getD false) (gateNext .out))
         (gateNext .into))
   | .inr .into =>
     .pop (.inr .temp) (fun v a => callCarry v a)
       (.branch (fun v => v.2.isSome)
         (.push (.inl U.machine.tm.k₁) (fun v => U.machine.outputAlphabet.symm (v.2.getD false)) (gateNext .into))
         (.load (fun _ => (U.machine.tm.initialState,none)) .halt))
 def gateTM (U : Program) : Turing.FinTM2 where
   K := CallK U
   Γ := CallΓ U
   Λ := GatedΛ U
   σ := Callσ U
   k₀ := .inr .raw
   k₁ := .inl U.machine.tm.k₁
   initialState := (U.machine.tm.initialState,none)
   main := .inr .gate
   m := gateCode U
 def gatedCall (U : Program) : Program where
   machine := ⟨gateTM U,(by change Bool ≃ Bool; exact Equiv.refl _),
     (by change U.machine.tm.Γ U.machine.tm.k₁ ≃ Bool; exact U.machine.outputAlphabet)⟩
   finiteAlphabet k := by cases k with | inl k => exact U.finiteAlphabet k | inr k => change Finite Bool; infer_instance

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.GatedContextSteps
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

 def gateCfg (U : Program) (p : GatePhase) (S : ∀k,List (U.machine.tm.Γ k)) (R T : List Bool) : (gateTM U).Cfg :=
   cfg (some (.inr p)) (U.machine.tm.initialState,none) (extendStore S (extraStore R [] [] [] T))
 theorem gate_init (U : Program) (input : List Bool) : Turing.initList (gateTM U) input=gateCfg U .gate (fun _ => []) input [] := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   rw [initList_store]
   funext k
   cases k with
   | inl k => simp [gateTM,gateCfg,cfg,onlyStack,Function.update,extendStore]
   | inr e => cases e <;> simp [gateTM,gateCfg,cfg,onlyStack,Function.update,extendStore,extraStore]
 theorem gate_true_step (U : Program) (input : List Bool) :
     step (gateCode U) (gateCfg U .gate (fun _ => []) (true::input) [])=
       some (labelCfg Sum.inl (Turing.initList (callTM U) input)) := by
   simp only [gateCfg,cfg,step,gateCode,stepAux,callCarry,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.getD_some,cond_true]
   rw [update_extend_right]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change extendStore (fun _ => []) (Function.update (extraStore (true::input) [] [] [] []) Extra.raw input)=
     (Turing.initList (callTM U) input).stk
   rw [initList_store]
   funext k
   cases k with
   | inl k => simp [callTM,onlyStack,Function.update,extendStore]
   | inr e => cases e <;> simp [callTM,onlyStack,Function.update,extendStore,extraStore]
 theorem gate_false_step (U : Program) (input : List Bool) :
     step (gateCode U) (gateCfg U .gate (fun _ => []) (false::input) [])=
       some (gateCfg U .out (fun _ => []) input []) := by
   simp only [gateCfg,cfg,step,gateCode,stepAux,callCarry,gateNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.getD_some,cond_false]
   rw [update_extend_right]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 theorem gated_out_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b : Bool) (R T : List Bool) :
     step (gateCode U) (gateCfg U .out S (b::R) T)=some (gateCfg U .out S R (b::T)) := by
   simp only [gateCfg,cfg,step,gateCode,stepAux,callCarry,gateNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true,Option.getD_some]
   simp only [update_extend_right,Function.update_of_ne (by decide : Extra.temp≠Extra.raw)]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 theorem gated_out_nil (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (T : List Bool) :
     step (gateCode U) (gateCfg U .out S [] T)=some (gateCfg U .into S [] T) := by
   simp [gateCfg,cfg,step,gateCode,stepAux,callCarry,gateNext,extraStore,extendStore,Function.update]
 theorem gated_into_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b : Bool) (R T : List Bool) :
     step (gateCode U) (gateCfg U .into S R (b::T))=some (gateCfg U .into
       (Function.update S U.machine.tm.k₁ (U.machine.outputAlphabet.symm b::S U.machine.tm.k₁)) R T) := by
   simp only [gateCfg,cfg,step,gateCode,stepAux,callCarry,gateNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true,Option.getD_some]
   rw [update_extend_right]
   simp only [extendStore_inl]
   rw [update_extend]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 theorem gated_into_nil (U : Program) (output : List Bool) :
     step (gateCode U) (gateCfg U .into (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) [] [])=
       some (Turing.haltList (gateTM U) (output.map U.machine.outputAlphabet.symm)) := by
   simp only [gateCfg,cfg,step,gateCode,stepAux,callCarry,gateNext,extendStore_inr,extraStore,
     List.head?_nil,List.tail_nil,Option.isSome_none,cond_false]
   rw [update_extend_right]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   rw [haltList_store]
   funext k
   cases k with
   | inl k =>
     by_cases h : k=U.machine.tm.k₁
     · subst k; simp [onlyStack,Function.update,extendStore,gateTM]
     · simp [onlyStack,Function.update,extendStore,gateTM,h]
   | inr e => cases e <;> simp [onlyStack,Function.update,extendStore,gateTM,extraStore]

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.GatedContextRuns
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

 theorem gated_out_loop (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (L T : List Bool) :
     run (gateCode U) (gateCfg U .out S L T) (L.length+1)=some (gateCfg U .into S [] (L.reverse++T)) := by
   induction L generalizing T with
   | nil => exact gated_out_nil U S T
   | cons b L ih =>
     rw [List.length_cons,run_first,gated_out_cons,Option.bind_some]
     have hh := ih (b::T)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
 theorem gated_into_loop (U : Program) (L output : List Bool) :
     run (gateCode U) (gateCfg U .into (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) [] L) (L.length+1)=
       some (Turing.haltList (gateTM U) ((L.reverse++output).map U.machine.outputAlphabet.symm)) := by
   induction L generalizing output with
   | nil => exact gated_into_nil U output
   | cons b L ih =>
     rw [List.length_cons,run_first,gated_into_cons,onlyStack_self,onlyStack_update,Option.bind_some]
     have hh := ih (b::output)
     simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hh

 theorem gated_false_runs (U : Program) (output : List Bool) :
     Runs (gatedCall U) (false::output) output (2*output.length+3) := by
   change Nonempty (Turing.TM2OutputsInTime (gateTM U) ((false::output).map id)
     (some (output.map U.machine.outputAlphabet.symm)) (2*output.length+3))
   rw [List.map_id]
   have h0 : run (gateCode U) (Turing.initList (gateTM U) (false::output)) 1=
       some (gateCfg U .out (fun _ => []) output []) := by rw [gate_init]; exact gate_false_step U output
   have h1 := gated_out_loop U (fun _ => []) output []
   simp only [List.append_nil] at h1
   have h2 := gated_into_loop U output.reverse []
   simp only [List.map_nil,onlyStack_nil,List.length_reverse,List.reverse_reverse,List.append_nil] at h2
   have hr := run_trans _ _ _ _ _ _ h0 h1
   have hr := run_trans _ _ _ _ _ _ hr h2
   obtain ⟨hrun⟩ := RawStack.outputs (tm:=gateTM U) (false::output) (output.map U.machine.outputAlphabet.symm) _ hr
   refine ⟨{hrun with steps_le_m := hrun.steps_le_m.trans ?_}⟩
   omega

 theorem gated_true_runs (U : Program) (input output : List Bool) (T : ℕ)
     (h : Runs (callWithContext U) input output T) : Runs (gatedCall U) (true::input) output (T+1) := by
   change Nonempty (Turing.TM2OutputsInTime (gateTM U) ((true::input).map id)
     (some (output.map U.machine.outputAlphabet.symm)) (T+1))
   rw [List.map_id]
   obtain ⟨t,ht,hr⟩ := outputs_run (callWithContext U) input output T h
   change run (callCode U) (Turing.initList (callTM U) (input.map id)) t=
     some (Turing.haltList (callTM U) (output.map U.machine.outputAlphabet.symm)) at hr
   rw [List.map_id] at hr
   have h0 : run (gateCode U) (Turing.initList (gateTM U) (true::input)) 1=
       some (labelCfg Sum.inl (Turing.initList (callTM U) input)) := by rw [gate_init]; exact gate_true_step U input
   have h1 := run_label Sum.inl (callCode U) (gateCode U) (fun _ => rfl) (Turing.initList (callTM U) input) t
   rw [hr,Option.map_some] at h1
   have hhalt : labelCfg Sum.inl (Turing.haltList (callTM U) (output.map U.machine.outputAlphabet.symm))=
     Turing.haltList (gateTM U) (output.map U.machine.outputAlphabet.symm) := rfl
   rw [hhalt] at h1
   have hh := run_trans _ _ _ _ _ _ h0 h1
   obtain ⟨hrun⟩ := RawStack.outputs (tm:=gateTM U) (true::input) (output.map U.machine.outputAlphabet.symm) _ hh
   refine ⟨{hrun with steps_le_m := hrun.steps_le_m.trans ?_}⟩
   omega

 theorem gated_context_runs (U : Program) (ctx input output : List Bool) (T : ℕ) (h : Runs U input output T) :
     Runs (gatedCall U) (true::(prefixBits ctx++input)) (prefixBits ctx++output)
       (T+4*ctx.length+2*input.length+7) := by
   have hh := gated_true_runs U _ _ _ (call_context_runs U ctx input output T h)
   convert hh using 1 <;> omega

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.WrapperRuntime
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack

 theorem pipeline_time_bound (A C K₁ K₂ B D p r : ℕ) (hA : 0< A) (hC : 0< C) (hK₁ : 0< K₁) (hK₂ : 0< K₂) (hp : 0< p) :
     ∃ K : ℕ,0< K ∧ ∀ (L N T payload middle tcall tab post : ℕ),
       payload≤ L+B*(A*(L+N+1)^p) → tcall≤ T+6*payload+7 →
       tab=K₁*(A*(L+N+1)^p+tcall+L+1) → middle≤ L+D*tab →
       post=C*(middle+1)^r →
       K₂*(tab+post+L+1)≤ K*(T+L+N+1)^(p+p*r+1) := by
   let F := K₁*(A*(1+6*B)+15)
   refine ⟨K₂*(F+C*(2+D*F)^r+2),by dsimp [F]; positivity,?_⟩
   intro L N T payload middle tcall tab post hpay hcall hab hmid hpost
   let z := T+L+N+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hpre : (L+N+1)^p≤ z^p := Nat.pow_le_pow_left (by dsimp [z]; omega) p
   have hzp : z≤ z^p := by simpa only [pow_one] using Nat.pow_le_pow_right hz hp
   have hin : T+7*L+8≤15*z := by dsimp [z]; omega
   have hpay' : payload≤ L+B*(A*z^p) := hpay.trans (Nat.add_le_add_left (Nat.mul_le_mul_left B (Nat.mul_le_mul_left A hpre)) L)
   have habound : tab≤ F*z^p := by
     rw [hab]
     have hinner : A*(L+N+1)^p+tcall+L+1≤(A*(1+6*B)+15)*z^p := by
       have hh := Nat.mul_le_mul_left A hpre
       nlinarith only [hh,hcall,hpay',hin,hzp]
     exact (Nat.mul_le_mul_left K₁ hinner).trans_eq (by dsimp [F]; ring)
   have hL : L+1≤ z^p := (show L+1≤ z by dsimp [z]; omega).trans hzp
   have hinput : middle+1≤(2+D*F)*z^p := by
     have hmul := Nat.mul_le_mul_left D habound
     have hone : 1≤ z^p := one_le_pow₀ hz
     nlinarith only [hmid,hmul,hL,hone]
   have hpostbound : post≤ C*(2+D*F)^r*z^(p*r) := by
     rw [hpost]
     have hh := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hinput r)
     simpa only [mul_pow,← pow_mul,Nat.mul_assoc] using hh
   have hp1 : z^p≤ z^(p+p*r+1) := Nat.pow_le_pow_right hz (by omega)
   have hr1 : z^(p*r)≤ z^(p+p*r+1) := Nat.pow_le_pow_right hz (by omega)
   have h1 : z≤ z^(p+p*r+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ p+p*r+1)
   have htab := habound.trans (Nat.mul_le_mul_left F hp1)
   have hpost' := hpostbound.trans (Nat.mul_le_mul_left (C*(2+D*F)^r) hr1)
   have hL' : L+1≤ z^(p+p*r+1) := (show L+1≤ z by dsimp [z]; omega).trans h1
   have hs : tab+post+L+1≤(F+C*(2+D*F)^r+2)*z^(p+p*r+1) := by
     nlinarith only [htab,hpost',hL']
   change _≤(K₂*(F+C*(2+D*F)^r+2))*z^(p+p*r+1)
   simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left K₂ hs

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.Sol_weighted_wrapper
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.RawStack EdgeSublinearMWIS.Main.ProgramComposition

theorem solution :
    ∃ q : ℕ, 0 < q ∧ ∀ U : Program, ∃ (P : Program) (K : ℕ), 0 < K ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode) (ε : RationalCode),
        0 < ε.value → ε.value < 1 →
        (n ≤ 1 → ∃ s, Runs P (weightedInput G w ε) (mask (directVertices w)) s ∧
          s ≤ K * ((weightedInput G w ε).length + 1) ^ q) ∧
        (2 ≤ n → maximumWeight (clippedValues w) ≤ 0 →
          ∃ s, Runs P (weightedInput G w ε) (mask (∅ : Finset (Fin n))) s ∧
            s ≤ K * ((weightedInput G w ε).length + 1) ^ q) ∧
        (∀ (τ : ℚ) (t : Fin n → ℕ), 2 ≤ n →
          weightRounding (clippedValues w) ε.value = some (τ, t) →
          ∀ (J : Finset (Fin (totalCopies t))) (u T : ℕ),
            Runs U (unweightedInput (roundedGraph G t) (halfAccuracy ε))
              (mask J ++ encodeNat u) T →
            ∃ s, Runs P (weightedInput G w ε) (mask (originalVertices t J)) s ∧
              s ≤ K * (T + (weightedInput G w ε).length + totalCopies t + 1) ^ q) := by
  obtain ⟨Pre,A,p,hA,hp,hPre⟩ := EdgeSublinearMWIS.Main.TreeToTM2.realizer_expanded_program
    preprocessingRealizer expansionSize preprocessing_expanded
  obtain ⟨Post,C,r,hC,hr,hPost⟩ := EdgeSublinearMWIS.Main.TreeToTM2.realizer_poly_program
    postprocessRealizer postprocess_polynomial
  refine ⟨p+p*r+1,by omega,?_⟩
  intro U
  let AB := sequence Pre (gatedCall U)
  let P := sequence AB Post
  obtain ⟨K₁,hK₁,hSeq₁⟩ := sequence_runs_linear Pre (gatedCall U)
  obtain ⟨K₂,hK₂,hSeq₂⟩ := sequence_runs_linear AB Post
  obtain ⟨K,hK,hBound⟩ := pipeline_time_bound A C K₁ K₂ (EdgeSublinearMWIS.Main.StackSpace.bound Pre.machine.tm)
    (EdgeSublinearMWIS.Main.StackSpace.bound AB.machine.tm) p r hA hC hK₁ hK₂ hp
  refine ⟨P,K,hK,?_⟩
  intro n G w ε he he1
  let L := weightedInput G w ε
  have pipeline (N T tc : ℕ) (mid out : List Bool) (hN : expansionSize L=N)
      (hCall : Runs (gatedCall U) (preprocessing L) mid tc)
      (hc : tc≤ T+6*(preprocessing L).length+7) (ho : postprocess mid=out) :
      ∃ s,Runs P L out s ∧ s≤ K*(T+L.length+N+1)^(p+p*r+1) := by
    let preTime := A*(L.length+N+1)^p
    let abTime := K₁*(preTime+tc+L.length+1)
    let postTime := C*(mid.length+1)^r
    have hpre := hPre L
    rw [hN] at hpre
    have hab : Runs AB L mid abTime := hSeq₁ L (preprocessing L) mid preTime tc hpre hCall
    have hpost := hPost mid
    rw [ho] at hpost
    have hfinal : Runs P L out (K₂*(abTime+postTime+L.length+1)) :=
      hSeq₂ L mid out abTime postTime hab hpost
    refine ⟨K₂*(abTime+postTime+L.length+1),hfinal,?_⟩
    exact hBound L.length N T (preprocessing L).length mid.length tc abTime postTime
      (output_length Pre L (preprocessing L) preTime hpre) hc rfl
      (output_length AB L mid abTime hab) rfl
  have runSmall (hs : smallCase (weightedParse L)=true) :
      ∃ s,Runs P L (smallAnswer (weightedParse L)) s ∧ s≤ K*(L.length+1)^(p+p*r+1) := by
    let mid := prefixBits (false::smallAnswer (weightedParse L))
    have hcall := gated_false_runs U mid
    rw [← preprocessing_small L hs] at hcall
    have hc : 2*mid.length+3≤0+6*(preprocessing L).length+7 := by
      rw [preprocessing_small L hs]
      change 2*mid.length+3≤0+6*(mid.length+1)+7
      omega
    have hh := pipeline 0 0 (2*mid.length+3) mid (smallAnswer (weightedParse L))
      (expansionSize_small L hs) hcall hc (postprocess_small _)
    simpa only [Nat.zero_add,Nat.add_zero] using hh
  refine ⟨?_,?_,?_⟩
  · intro hn
    have hs := (smallCase_correct G w ε).mpr (Or.inl hn)
    obtain ⟨s,hsrun,hstime⟩ := runSmall hs
    rw [smallAnswer_direct G w ε hn] at hsrun
    exact ⟨s,hsrun,hstime⟩
  · intro hn hm
    have hs := (smallCase_correct G w ε).mpr (Or.inr hm)
    obtain ⟨s,hsrun,hstime⟩ := runSmall hs
    rw [smallAnswer_empty G w ε hn] at hsrun
    exact ⟨s,hsrun,hstime⟩
  · intro tau t hn hround J u T hU
    let ws := guardedWords (weightedParse L)
    let ctx := true::(encodeNat n++wordArrayBits ws)
    let inp := unweightedInput (roundedGraph G t) (halfAccuracy ε)
    let mid := prefixBits ctx++(mask J++encodeNat u)
    have hpre := preprocessing_large G w ε tau t hround
    change preprocessing L=true::(prefixBits ctx++inp) at hpre
    have hcall := gated_context_runs U ctx inp (mask J++encodeNat u) T hU
    rw [← hpre] at hcall
    have hc : T+4*ctx.length+2*inp.length+7≤ T+6*(preprocessing L).length+7 := by
      rw [hpre]
      simp only [List.length_cons,List.length_append,prefixBits,List.length_replicate]
      omega
    have hpost := postprocess_large t ws (guardedWords_large G w ε tau t hround) J (encodeNat u)
    exact pipeline (totalCopies t) T (T+4*ctx.length+2*inp.length+7) mid (mask (originalVertices t J))
      (expansionSize_large G w ε tau t hround) hcall hc hpost
end
