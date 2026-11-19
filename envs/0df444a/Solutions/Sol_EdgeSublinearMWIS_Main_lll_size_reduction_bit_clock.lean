-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.lll_size_reduction_bit_clock
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:16:39.15943+00:00
-- url     : https://prove2.me/submissions/ae21c770-1682-4b58-bba5-29dcfc661a8f

import Mathlib.Data.Nat.Bits
import Mathlib.Tactic
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_OAIThreeMachineSched02
import Theorems.Thm_EdgeSublinearMWIS_Main_realizer_native_program
import Definitions.Def_EdgeSublinearMWIS_Main_WeightedExecution
import Definitions.Def_EdgeSublinearMWIS_Main_WeightedReduction
import Definitions.Def_LLLFactor_RedBasis_Setting
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Definitions.Def_LLLFactor_Reduction_Algorithm
import Theorems.Thm_LLLFactor_Reduction_gram_eq_prod_gs
import Theorems.Thm_LLLFactor_Reduction_potD_case1_lt
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib
import Theorems.Thm_LLLFactor_Reduction_step_preserves_basis
import Theorems.Thm_LLLFactor_Reduction_case2_count_le
import Definitions.Def_EdgeSublinearMWIS_Main_Ellipsoid
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Algebra.Polynomial.Eval.Defs
import Definitions.Def_EdgeSublinearMWIS_Main_RationalEllipsoids
import Definitions.Def_EdgeSublinearMWIS_Main_BinaryOracleImplementation
import Theorems.Thm_EdgeSublinearMWIS_Main_rounded_ellipsoid_estimates

section
open Matrix EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.GLS
open Cast EllipsoidRounding EllipsoidSequence EllipsoidStateSize
namespace EdgeSublinearMWIS.Main.GLS.EllipsoidSequence
theorem shapes_invariant (n : ℕ) (hn : 2 ≤ n) (a : ℕ → Fin n → ℚ)
    (ha : ∀ k, 1 ≤ realVector (a k) ⬝ᵥ realVector (a k)) (k : ℕ) :
    (realShape (shapes n a k)).PosDef ∧
    ∀ x : Fin n → ℝ,
      ((2 : ℝ) ^ (2 * k))⁻¹ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (realShape (shapes n a k) *ᵥ x) ∧
        x ⬝ᵥ (realShape (shapes n a k) *ᵥ x) ≤ (4 : ℝ) ^ k * (x ⬝ᵥ x) :=
  (EdgeSublinearMWIS.Main.rounded_ellipsoid_estimates n hn a ha).conditioned k
end EdgeSublinearMWIS.Main.GLS.EllipsoidSequence

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidSequence
theorem preserves_points_up_to (n : ℕ) (hn : 2 ≤ n) (a : ℕ → Fin n → ℚ)
    (ha : ∀ k, 1 ≤ realVector (a k) ⬝ᵥ realVector (a k)) (c₀ : Fin n → ℚ)
    (x : Fin n → ℝ) (hx : (x - realVector c₀) ⬝ᵥ (x - realVector c₀) ≤ 1)
    (k : ℕ)
    (hcut : ∀ j < k, realVector (a j) ⬝ᵥ (x - realVector (centers n a c₀ j)) ≤ 0) :
    (x - realVector (centers n a c₀ k)) ⬝ᵥ
      ((realShape (shapes n a k))⁻¹ *ᵥ (x - realVector (centers n a c₀ k))) ≤ 1 :=
  (EdgeSublinearMWIS.Main.rounded_ellipsoid_estimates n hn a ha).retained c₀ x hx k hcut
end EdgeSublinearMWIS.Main.GLS.EllipsoidSequence

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidSequence
theorem shapes_below_threshold (n : ℕ) (hn : 2 ≤ n) (a : ℕ → Fin n → ℚ)
    (ha : ∀ k, 1 ≤ realVector (a k) ⬝ᵥ realVector (a k)) (B : ℕ) :
    Real.sqrt (realShape (shapes n a (thresholdSteps n B))).det <
      (((2 : ℝ) ^ B)⁻¹) ^ n :=
  (EdgeSublinearMWIS.Main.rounded_ellipsoid_estimates n hn a ha).determinant B
end EdgeSublinearMWIS.Main.GLS.EllipsoidSequence

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize
theorem centers_magnitude (n : ℕ) (hn : 2 ≤ n) (a : ℕ → Fin n → ℚ)
    (ha : ∀ k, 1 ≤ realVector (a k) ⬝ᵥ realVector (a k))
    (k : ℕ) (i : Fin n) : |(centers n a 0 k i : ℝ)| ≤ (2 : ℝ) ^ (k + 2) :=
  (EdgeSublinearMWIS.Main.rounded_ellipsoid_estimates n hn a ha).centerMagnitude k i
end EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize
theorem shapes_entry_magnitude (n : ℕ) (hn : 2 ≤ n) (a : ℕ → Fin n → ℚ)
    (ha : ∀ k, 1 ≤ realVector (a k) ⬝ᵥ realVector (a k))
    (k : ℕ) (i j : Fin n) : |(shapes n a k i j : ℝ)| ≤ (4 : ℝ) ^ k :=
  (EdgeSublinearMWIS.Main.rounded_ellipsoid_estimates n hn a ha).shapeMagnitude k i j
end EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize
theorem shapes_height (n : ℕ) (hn : 2 ≤ n) (a : ℕ → Fin n → ℚ)
     (ha : ∀ k,1 ≤ realVector (a k) ⬝ᵥ realVector (a k)) (k : ℕ) (i j : Fin n) :
     (shapes n a k i j).num.natAbs ≤ 2^stateHeight n k ∧
       (shapes n a k i j).den ≤ 2^stateHeight n k :=
  (EdgeSublinearMWIS.Main.rounded_ellipsoid_estimates n hn a ha).shapeHeight k i j
end EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize
theorem centers_height (n : ℕ) (hn : 2 ≤ n) (a : ℕ → Fin n → ℚ)
     (ha : ∀ k,1 ≤ realVector (a k) ⬝ᵥ realVector (a k)) (k : ℕ) (i : Fin n) :
     (centers n a 0 k i).num.natAbs ≤ 2^stateHeight n k ∧
       (centers n a 0 k i).den ≤ 2^stateHeight n k :=
  (EdgeSublinearMWIS.Main.rounded_ellipsoid_estimates n hn a ha).centerHeight k i
end EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize
end


-- Solutions.RawBinary
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 
 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryAdder
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open RawStack

 
 

 

 

 

 

 

 

 

 theorem word_length (A B : List Bool) : (word A B).length=A.length+B.length+1 := by
   have hh := (iter_lists (A,(B,(false,[]))) (A.length+B.length+1)).2.2
   simpa only [word,List.length_reverse,List.length_nil,Nat.zero_add] using hh

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.BinaryTrim
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 

 

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

 

 

 


end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinarySubtract
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinarySubtract
open RawStack

 
 
 
 

 theorem bit_balance (a b c : Bool) :
     a.toNat+2*((!a && (b || c)) || (b && c)).toNat=b.toNat+c.toNat+(xor (xor a b) c).toNat := by
   cases a <;> cases b <;> cases c <;> decide

 

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

 

 

 

 
 
 
 
 
 

 

 
 
 
 

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.NativeCompilerInterface
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.NativeCompiler
 
end EdgeSublinearMWIS.Main.NativeCompiler
end

-- Solutions.RealizerLinear
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 

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

 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RealizerPolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 

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

 
 
 
 
 

 

 

 theorem signedValue_encode (z : ℤ) : signedValue (decide (z<0)) (natBits z.natAbs)=z := by
   cases z <;> simp [signedValue,value_natBits] <;> omega

 
 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.CappedBinary
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 

 
 
 
 

 

 

 
 

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

 
 

 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EncodingBounds
noncomputable section

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.EncodingBounds

 

 

 

 

 

 

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

 
 
 
 

 
 
 
 
 

 
 
 

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 
 
 
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

 

 

 

 

 

 

 

 

 



 

 

 

 

 

 



 

 

 

 

 

 

 

 

 

 

 

 

 

end EdgeSublinearMWIS.Main.WeightedHelpers
end

-- Solutions.WeightedExecutionMath
noncomputable section

open scoped BigOperators Classical
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.WeightedHelpers
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.WeightedExecutionMath

 

 

 

 

 

 

 

 

 

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

 
 
 
 
 
 
 
 
 
 
 
 

 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RawRoundingCorrect
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack

 

 

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
 
 
 theorem dropList_polynomial : PolyBound (dropList (α:=α)) := by
   unfold dropList
   apply polynomial_congr
   exact polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst))
     (polynomial_iterate (linear_polynomial tailList_linear) 0 (fun L => by simpa only [Nat.add_zero] using tailList_volume L))

 
 
 
 
 
 

 
 
 theorem countStep_fold_polynomial : PolyBound (countStep (α:=α)).fold := by
   apply polynomial_fold_bounded (linear_polynomial (linear_comp linear_snd succ_linear)) 3
   intro L k j hj
   dsimp only [Function.comp_apply]
   rw [count_fold]
   have hlen := length_volume L
   simp only [volume_nat,volume_pair,List.length_take]
   omega
 
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

 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
variable {α : Type} [OAI.ThreeMachine.StackCompiler.Coding α]
 
 
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
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 
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

 
 
 
 
 
 
 

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

 

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 
 
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

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FiniteArrayCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 theorem headList_polynomial {α : Type} [Coding α] (a : α) : PolyBound (headList a) := by
   unfold headList
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair reverse_polynomial_generic (linear_polynomial (linear_constant a)))
     (polynomial_fold_select (linear_polynomial linear_fst) (fun _ _ => Or.inl rfl))

 
 
 
 
 
 

 
 
 
 

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

 
 theorem lookupList_polynomial {α : Type} [Coding α] (a : α) : PolyBound (lookupList a) :=
   polynomial_comp dropList_polynomial (headList_polynomial a)
 
 
 
 
 
 
 
 
 
 

 
end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 
end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GenericArrayPairs
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RawStack
variable {α β : Type} [Coding α] [Coding β]

 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.FractionAddition
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 theorem sumWords_value (A B : List Bool) : value (sumWords A B)=value A+value B := by
   rw [sumWords,trim_value,BinaryAdder.word_value]
 theorem sumWords_length (A B : List Bool) : (sumWords A B).length≤ max A.length B.length+1 := by
   unfold sumWords
   apply trim_length_of_lt
   rw [BinaryAdder.word_value,pow_succ]
   have hA := (value_lt A).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.le_max_left A.length B.length))
   have hB := (value_lt B).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (Nat.le_max_right A.length B.length))
   omega
 
 theorem sumWords_polynomial : PolyBound sumWordsRealizer := polynomial_comp word_polynomial trim_polynomial

 
 

 
 
 
 
 

 
 
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

 
 
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedSumCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 theorem xorBits_linear : Linear BinaryAdder.xorBits := by
   unfold BinaryAdder.xorBits
   apply linear_congr
   exact linear_choose linear_not linear_id
 
 theorem oppositeSigns_polynomial : PolyBound oppositeSigns := linear_polynomial (linear_comp linear_fst xorBits_linear)
 
 theorem signedPairLess_polynomial : PolyBound signedPairLess := polynomial_comp (linear_polynomial linear_snd) BinarySubtract.less_polynomial
 
 theorem signedFirstDifference_polynomial : PolyBound signedFirstDifference := polynomial_pair
   (linear_polynomial (linear_comp linear_fst linear_fst)) (polynomial_comp (linear_polynomial linear_snd) BinarySubtract.difference_polynomial)
 
 theorem signedSecondDifference_polynomial : PolyBound signedSecondDifference := polynomial_pair
   (linear_polynomial (linear_comp linear_fst linear_snd))
   (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd linear_snd) (linear_comp linear_snd linear_fst))) BinarySubtract.difference_polynomial)
 
 theorem signedMixedSum_polynomial : PolyBound signedMixedSum := polynomial_comp
   (polynomial_pair signedPairLess_polynomial (linear_polynomial linear_id))
   (polynomial_choose signedSecondDifference_polynomial signedFirstDifference_polynomial)
 
 theorem signedSameSum_polynomial : PolyBound signedSameSum := polynomial_pair (linear_polynomial (linear_comp linear_fst linear_fst))
   (polynomial_comp (linear_polynomial linear_snd) sumWords_polynomial)
 
 theorem signedNumeratorSum_polynomial : PolyBound signedNumeratorSumRealizer := by
   unfold signedNumeratorSumRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair oppositeSigns_polynomial (linear_polynomial linear_id))
     (polynomial_choose signedMixedSum_polynomial signedSameSum_polynomial)

 
 
 theorem signedCrossLeft_polynomial : PolyBound signedCrossLeft := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp (linear_comp linear_fst linear_snd) linear_fst)
     (linear_comp (linear_comp linear_snd linear_snd) linear_snd))) multiply_polynomial
 theorem signedCrossRight_polynomial : PolyBound signedCrossRight := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp (linear_comp linear_snd linear_snd) linear_fst)
     (linear_comp (linear_comp linear_fst linear_snd) linear_snd))) multiply_polynomial
 
 theorem signedCommonDen_polynomial : PolyBound signedCommonDen := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp (linear_comp linear_fst linear_snd) linear_snd)
     (linear_comp (linear_comp linear_snd linear_snd) linear_snd))) multiply_polynomial
 
 
 theorem signedSumNumerator_polynomial : PolyBound signedSumNumeratorRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_pair (linear_comp linear_fst linear_fst) (linear_comp linear_snd linear_fst)))
     (polynomial_pair signedCrossLeft_polynomial signedCrossRight_polynomial)) signedNumeratorSum_polynomial
 
 
 theorem signedFractionAdd_polynomial : PolyBound signedFractionAddRealizer := polynomial_pair
   (polynomial_comp signedSumNumerator_polynomial (linear_polynomial linear_fst))
   (polynomial_pair (polynomial_comp signedSumNumerator_polynomial (linear_polynomial linear_snd)) signedCommonDen_polynomial)
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedSumMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem signedNumeratorSum_value (s : SignedPairWords) :
     signedValue (signedNumeratorSum s).1 (signedNumeratorSum s).2=
       signedValue s.1.1 s.2.1+signedValue s.1.2 s.2.2 := by
   rcases s with ⟨⟨a,b⟩,L,R⟩
   have hless : BinarySubtract.less L R=decide (value L< value R) := by
     apply Bool.eq_iff_iff.mpr
     simpa only [decide_eq_true_eq] using BinarySubtract.less_iff L R
   cases a <;> cases b <;> by_cases h : value L< value R <;>
     simp [signedNumeratorSum,signedValue,hless,h,sumWords_value,BinarySubtract.difference_value] <;> omega
 theorem signedValue_multiply (a : Bool) (L D : List Bool) :
     signedValue a (multiply L D)=signedValue a L*(value D:ℤ) := by
   cases a <;> simp [signedValue,multiply_value] <;> ring
 
 
 theorem signedSumNumerator_value (s : SignedWords×SignedWords) :
     signedValue (signedSumNumerator s).1 (signedSumNumerator s).2=
       signedValue s.1.1 s.1.2.1*(value s.2.2.2:ℤ)+signedValue s.2.1 s.2.2.1*(value s.1.2.2:ℤ) := by
   rw [signedSumNumerator,signedNumeratorSum_value,signedValue_multiply,signedValue_multiply]
 theorem signedFractionAdd_denpos (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.2) :
     0< value (signedFractionAdd (a,b)).2.2 := by
   change 0< value (multiply a.2.2 b.2.2)
   rw [multiply_value]
   exact Nat.mul_pos ha hb
 theorem signedFractionAdd_value (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.2) :
     signedFractionValue (signedFractionAdd (a,b))=signedFractionValue a+signedFractionValue b := by
   have hA : (value a.2.2:ℚ)≠0 := by exact_mod_cast ha.ne'
   have hB : (value b.2.2:ℚ)≠0 := by exact_mod_cast hb.ne'
   unfold signedFractionAdd signedFractionValue
   rw [signedSumNumerator_value,multiply_value]
   push_cast
   field_simp
   <;> ring
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedProductCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 theorem signedFractionNeg_polynomial : PolyBound signedFractionNegRealizer := linear_polynomial (linear_pair (linear_comp linear_fst linear_not) linear_snd)
 
 theorem signedProductSign_polynomial : PolyBound signedProductSign := linear_polynomial
   (linear_comp (linear_pair (linear_comp linear_fst linear_fst) (linear_comp linear_snd linear_fst)) xorBits_linear)
 
 theorem signedProductNum_polynomial : PolyBound signedProductNum := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp (linear_comp linear_fst linear_snd) linear_fst)
     (linear_comp (linear_comp linear_snd linear_snd) linear_fst))) multiply_polynomial
 
 
 theorem signedFractionMul_polynomial : PolyBound signedFractionMulRealizer := polynomial_pair signedProductSign_polynomial
   (polynomial_pair signedProductNum_polynomial signedCommonDen_polynomial)
 
 
 theorem signedFractionDiv_polynomial : PolyBound signedFractionDivRealizer := polynomial_pair signedProductSign_polynomial
   (polynomial_pair signedCrossLeft_polynomial signedCrossRight_polynomial)
 theorem signedFractionNeg_value (s : SignedWords) : signedFractionValue (signedFractionNeg s)= -signedFractionValue s := by
   rcases s with ⟨b,N,D⟩
   cases b <;> simp [signedFractionValue,signedFractionNeg,signedValue] <;> ring
 theorem signedFractionMul_value (a b : SignedWords) : signedFractionValue (signedFractionMul (a,b))=signedFractionValue a*signedFractionValue b := by
   rcases a with ⟨sa,na,da⟩
   rcases b with ⟨sb,nb,db⟩
   cases sa <;> cases sb <;> simp [signedFractionMul,signedFractionValue,signedValue,multiply_value] <;> ring
 theorem signedFractionDiv_value (a b : SignedWords) : signedFractionValue (signedFractionDiv (a,b))=signedFractionValue a/signedFractionValue b := by
   rcases a with ⟨sa,na,da⟩
   rcases b with ⟨sb,nb,db⟩
   cases sa <;> cases sb <;> simp [signedFractionDiv,signedFractionValue,signedValue,multiply_value,
     div_eq_mul_inv,mul_inv_rev,inv_inv] <;> ring
 theorem signedFractionMul_denpos (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.2) :
     0< value (signedFractionMul (a,b)).2.2 := by
   change 0< value (multiply a.2.2 b.2.2)
   rw [multiply_value]
   exact Nat.mul_pos ha hb
 theorem signedFractionDiv_denpos (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.1) :
     0< value (signedFractionDiv (a,b)).2.2 := by
   change 0< value (multiply b.2.1 a.2.2)
   rw [multiply_value]
   exact Nat.mul_pos hb ha
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedNormalize
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 theorem signedReduced_polynomial : PolyBound signedReducedRealizer :=
   polynomial_pair
     (polynomial_comp (polynomial_pair (linear_polynomial linear_fst)
       (polynomial_comp (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_fst)) trim_polynomial)
         (linear_polynomial nonempty_linear))) (linear_polynomial linear_and))
     (polynomial_comp (linear_polynomial linear_snd) normalizeWords_polynomial)
 theorem signedReduced_canonical (s : SignedWords) (hd : 0< value s.2.2) :
     signedReduced s=(decide ((signedFractionValue s).num<0),
       (natBits (signedFractionValue s).num.natAbs,natBits (signedFractionValue s).den)) := by
   rcases s with ⟨b,N,D⟩
   have hn := normalizeWords_rat b N D hd
   dsimp only [signedReduced,signedFractionValue,Prod.fst,Prod.snd]
   exact Prod.ext (rational_sign b N D hd) (Prod.ext hn.1 hn.2)
 theorem signedReduced_denpos (s : SignedWords) (hd : 0< value s.2.2) :
     0< value (signedReduced s).2.2 := by
   rw [signedReduced_canonical s hd]
   simpa only [value_natBits] using (signedFractionValue s).den_pos
 theorem signedReduced_value (s : SignedWords) (hd : 0< value s.2.2) :
     signedFractionValue (signedReduced s)=signedFractionValue s := by
   rw [signedReduced_canonical s hd]
   let q := signedFractionValue s
   change (signedValue (decide (q.num<0)) (natBits q.num.natAbs):ℚ)/value (natBits q.den)=q
   rw [signedValue_encode,value_natBits]
   exact Rat.num_div_den q
 
 
 theorem canonicalAdd_polynomial : PolyBound canonicalAddRealizer :=
   polynomial_comp signedFractionAdd_polynomial signedReduced_polynomial
 theorem canonicalAdd_denpos (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.2) :
     0< value (canonicalAdd (a,b)).2.2 := signedReduced_denpos _ (signedFractionAdd_denpos a b ha hb)
 theorem canonicalAdd_value (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.2) :
     signedFractionValue (canonicalAdd (a,b))=signedFractionValue a+signedFractionValue b := by
   rw [canonicalAdd,signedReduced_value _ (signedFractionAdd_denpos a b ha hb),signedFractionAdd_value a b ha hb]
 
 
 theorem canonicalMul_polynomial : PolyBound canonicalMulRealizer :=
   polynomial_comp signedFractionMul_polynomial signedReduced_polynomial
 theorem canonicalMul_denpos (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.2) :
     0< value (canonicalMul (a,b)).2.2 := signedReduced_denpos _ (signedFractionMul_denpos a b ha hb)
 theorem canonicalMul_value (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.2) :
     signedFractionValue (canonicalMul (a,b))=signedFractionValue a*signedFractionValue b := by
   rw [canonicalMul,signedReduced_value _ (signedFractionMul_denpos a b ha hb),signedFractionMul_value]
 
 
 theorem canonicalDiv_polynomial : PolyBound canonicalDivRealizer :=
   polynomial_comp signedFractionDiv_polynomial signedReduced_polynomial
 theorem canonicalDiv_denpos (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.1) :
     0< value (canonicalDiv (a,b)).2.2 := signedReduced_denpos _ (signedFractionDiv_denpos a b ha hb)
 theorem canonicalDiv_value (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.1) :
     signedFractionValue (canonicalDiv (a,b))=signedFractionValue a/signedFractionValue b := by
   rw [canonicalDiv,signedReduced_value _ (signedFractionDiv_denpos a b ha hb),signedFractionDiv_value]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedNormalizeBounds
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem signedNumeratorSum_length (s : SignedPairWords) :
     (signedNumeratorSum s).2.length ≤ max s.2.1.length s.2.2.length+1 := by
   unfold signedNumeratorSum
   split_ifs
   · exact (BinarySubtract.difference_length _ _).trans (by omega)
   · exact (BinarySubtract.difference_length _ _).trans (by omega)
   · exact sumWords_length _ _

 theorem signedAdd_width (a b : SignedWords) :
     fractionWidth (signedFractionAdd (a,b)).2 ≤ fractionWidth a.2+fractionWidth b.2 := by
   have hn := signedNumeratorSum_length
     ((a.1,b.1),(multiply a.2.1 b.2.2,multiply b.2.1 a.2.2))
   have h1 := multiply_length a.2.1 b.2.2
   have h2 := multiply_length b.2.1 a.2.2
   have hd := multiply_length a.2.2 b.2.2
   dsimp only [fractionWidth,signedFractionAdd,signedSumNumerator]
   dsimp only [Prod.fst,Prod.snd] at hn
   omega

 theorem normalizeWords_width (a : FractionWords) :
     fractionWidth (normalizeWords a.1 a.2)≤ fractionWidth a := by
   have h1 := (divide_lengths a.1 (BinaryGcd.gcd a.1 a.2)).1
   have h2 := (divide_lengths a.2 (BinaryGcd.gcd a.1 a.2)).1
   dsimp only [normalizeWords,fractionWidth]
   omega

 theorem canonicalAdd_width (a b : SignedWords) :
     fractionWidth (canonicalAdd (a,b)).2≤ fractionWidth a.2+fractionWidth b.2 := by
   exact (normalizeWords_width (signedFractionAdd (a,b)).2).trans (signedAdd_width a b)

 theorem signedWidth_volume (a : SignedWords) : fractionWidth a.2≤ volume a := by
   have h := fractionWidth_le_volume a.2
   have h1 := volume_bool a.1
   have hp : volume a=volume a.1+volume a.2+1 := by cases a; exact volume_pair _ _
   omega

 theorem signedVolume_width (a : SignedWords) : volume a≤14*fractionWidth a.2 := by
   have h := fractionVolume_le_width a.2
   have h1 := volume_bool a.1
   have hp : volume a=volume a.1+volume a.2+1 := by cases a; exact volume_pair _ _
   have hw : 1≤ fractionWidth a.2 := by simp [fractionWidth]
   omega

 theorem canonicalAdd_fold_width (xs : List SignedWords) (s : SignedWords) :
     fractionWidth (xs.foldl (fun s a => canonicalAdd (a,s)) s).2≤
       fractionWidth s.2+(xs.map (fun a => fractionWidth a.2)).sum := by
   induction xs generalizing s with
   | nil => simp
   | cons a xs ih =>
     rw [List.foldl_cons]
     have hh := ih (canonicalAdd (a,s))
     have ha := canonicalAdd_width a s
     simp only [List.map_cons,List.sum_cons]
     omega

 theorem signedWidths_sum (xs : List SignedWords) :
     (xs.map (fun a => fractionWidth a.2)).sum≤ volume xs := by
   induction xs with
   | nil => simp
   | cons a xs ih =>
     simp only [List.map_cons,List.sum_cons,volume_cons]
     have hh := signedWidth_volume a
     omega

 theorem canonicalAdd_fold_polynomial : PolyBound canonicalAddRealizer.fold := by
   apply polynomial_fold_bounded canonicalAdd_polynomial 14
   intro xs s j hj
   have hv := signedVolume_width ((xs.take j).foldl (fun s a => canonicalAdd (a,s)) s)
   have hw := canonicalAdd_fold_width (xs.take j) s
   have hs := signedWidth_volume s
   have hx := signedWidths_sum (xs.take j)
   have ht := take_volume_le xs j
   simp only [volume_pair]
   nlinarith

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedVectorCode
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 theorem vectorPairAt_polynomial : PolyBound vectorPairAt :=
   polynomial_pair
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) linear_fst)) (lookupList_polynomial signedZero))
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd linear_snd) linear_fst)) (lookupList_polynomial signedZero))
 
 
 theorem vectorPairs_polynomial : PolyBound vectorPairsRealizer :=
   polynomial_comp (polynomial_pair
     (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) listLength_polynomial) range_polynomial)
     (linear_polynomial linear_id)) (polynomial_mapEnvironment vectorPairAt_polynomial)
 
 
 theorem vectorProducts_polynomial : PolyBound vectorProductsRealizer :=
   polynomial_comp vectorPairs_polynomial (polynomial_mapList canonicalMul_polynomial)
 
 
 theorem signedSum_polynomial : PolyBound signedSumRealizer :=
   polynomial_comp (linear_polynomial (linear_pair linear_id (linear_constant signedZero))) canonicalAdd_fold_polynomial
 
 
 theorem signedDot_polynomial : PolyBound signedDotRealizer :=
   polynomial_comp vectorProducts_polynomial signedSum_polynomial

 theorem zero_denpos : 0< value signedZero.2.2 := by decide
 theorem zero_value : signedFractionValue signedZero=0 := by
   norm_num [signedFractionValue,signedZero,signedValue,value]

 theorem signed_fold_sum (xs : SignedVector) (s : SignedWords)
     (hx : ∀ a∈xs,0< value a.2.2) (hs : 0< value s.2.2) :
     0< value (xs.foldl (fun a b => canonicalAdd (b,a)) s).2.2 ∧
     signedFractionValue (xs.foldl (fun a b => canonicalAdd (b,a)) s)=
       signedFractionValue s+(xs.map signedFractionValue).sum := by
   induction xs generalizing s with
   | nil => simpa using hs
   | cons a xs ih =>
     have ha := hx a (by simp)
     have hh := ih (canonicalAdd (a,s)) (fun b hb => hx b (by simp [hb])) (canonicalAdd_denpos a s ha hs)
     rw [List.foldl_cons]
     constructor
     · exact hh.1
     · rw [hh.2,canonicalAdd_value a s ha hs]
       simp only [List.map_cons,List.sum_cons]
       ring

 theorem vectorPairs_ofFn {n : ℕ} (a b : Fin n → SignedWords) :
     vectorPairs (List.ofFn a,List.ofFn b)=List.ofFn (fun i => (a i,b i)) := by
   apply List.ext_getElem
   · simp [vectorPairs]
   · intro j hj hk
     have hjn : j< n := by simpa using hk
     simp only [vectorPairs,List.getElem_map,List.getElem_range]
     rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem (by simpa using hjn)]
     rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem (by simpa using hjn)]
     simp

 theorem signedDot_ofFn {n : ℕ} (a b : Fin n → SignedWords)
     (ha : ∀ i,0< value (a i).2.2) (hb : ∀ i,0< value (b i).2.2) :
     0< value (signedDot (List.ofFn a,List.ofFn b)).2.2 ∧
     signedFractionValue (signedDot (List.ofFn a,List.ofFn b))=
       ∑ i, signedFractionValue (a i)*signedFractionValue (b i) := by
   have he : vectorProducts (List.ofFn a,List.ofFn b)=List.ofFn (fun i => canonicalMul (a i,b i)) := by
     rw [vectorProducts,vectorPairs_ofFn,List.map_ofFn]
     rfl
   have hd : ∀ q∈vectorProducts (List.ofFn a,List.ofFn b),0< value q.2.2 := by
     rw [he]
     intro q hq
     obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
     exact canonicalMul_denpos _ _ (ha i) (hb i)
   have hh := signed_fold_sum (vectorProducts (List.ofFn a,List.ofFn b)) signedZero hd zero_denpos
   refine ⟨hh.1,?_⟩
   rw [signedDot,signedSum,hh.2,zero_value,zero_add,he,List.map_ofFn,List.sum_ofFn]
   apply Finset.sum_congr rfl
   intro i hi
   exact canonicalMul_value (a i) (b i) (ha i) (hb i)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedVectorArithmetic
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 theorem canonicalSub_polynomial : PolyBound canonicalSubRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial linear_fst)
     (polynomial_comp (linear_polynomial linear_snd) signedFractionNeg_polynomial)) canonicalAdd_polynomial
 theorem canonicalSub_denpos (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.2) :
     0< value (canonicalSub (a,b)).2.2 := canonicalAdd_denpos a _ ha hb
 theorem canonicalSub_value (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.2) :
     signedFractionValue (canonicalSub (a,b))=signedFractionValue a-signedFractionValue b := by
   change signedFractionValue (canonicalAdd (a,signedFractionNeg b))=_
   rw [canonicalAdd_value a (signedFractionNeg b) ha hb,signedFractionNeg_value,sub_eq_add_neg]
 theorem canonicalSub_width (a b : SignedWords) :
     fractionWidth (canonicalSub (a,b)).2≤ fractionWidth a.2+fractionWidth b.2 := canonicalAdd_width a _

 
 
 
 
 
 theorem vectorSub_polynomial : PolyBound vectorSubRealizer :=
   polynomial_comp vectorPairs_polynomial (polynomial_mapList canonicalSub_polynomial)
 
 
 theorem vectorScale_polynomial : PolyBound vectorScaleRealizer := polynomial_mapEnvironment canonicalMul_polynomial

 theorem vectorSub_length (s : SignedVector×SignedVector) : (vectorSub s).length=s.1.length := by
   simp [vectorSub,vectorPairs]
 theorem vectorSub_ofFn {n : ℕ} (a b : Fin n → SignedWords) :
     vectorSub (List.ofFn a,List.ofFn b)=List.ofFn (fun i => canonicalSub (a i,b i)) := by
   rw [vectorSub,vectorPairs_ofFn,List.map_ofFn]
   rfl
 
 theorem vectorScale_ofFn {n : ℕ} (a : Fin n → SignedWords) (b : SignedWords) :
     vectorScale (List.ofFn a,b)=List.ofFn (fun i => canonicalMul (a i,b)) := by
   rw [vectorScale,List.map_ofFn]
   rfl

 
 
 theorem gsCoefficient_polynomial : PolyBound gsCoefficientRealizer :=
   polynomial_comp (polynomial_pair signedDot_polynomial
     (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_snd)) signedDot_polynomial)) canonicalDiv_polynomial
 
 
 theorem gsProjection_polynomial : PolyBound gsProjectionRealizer :=
   polynomial_comp (polynomial_pair (linear_polynomial linear_snd) gsCoefficient_polynomial) vectorScale_polynomial

 theorem signed_num_positive_of_nonzero (s : SignedWords) (h : signedFractionValue s≠0) : 0< value s.2.1 := by
   by_contra hn
   have hz : value s.2.1=0 := by omega
   apply h
   cases hb : s.1 <;> simp [signedFractionValue,signedValue,hb,hz]

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialFoldPower
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

 theorem polynomial_fold_power {f : α×β → β} {R : Realizer f}
     (hR : PolyBound R) (E r : ℕ)
     (hV : ∀ (xs : List α) b j,j≤ xs.length →
       volume ((xs.take j).foldl (fun b a => f (a,b)) b)≤ E*(volume (xs,b)+1)^r) :
     PolyBound R.fold := by
   obtain ⟨C,q,hC,hR⟩ := hR
   let F := C*(E+3)^q
   let u := (r+1)*q
   let e := u+r+2
   refine ⟨F+100*E+200,e,by dsimp [F]; positivity,?_⟩
   rintro ⟨xs,b⟩
   let z := volume (xs,b)+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hlen : xs.length≤ z := by have hh:=length_volume xs; dsimp [z]; simp only [volume_pair]; omega
   have hxs : volume xs≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hv (j : ℕ) (hj : j≤ xs.length) : volume ((xs.take j).foldl (fun b a => f (a,b)) b)≤ E*z^r := hV xs b j hj
   have hzr : z≤ z^(r+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ r+1)
   have hrr : z^r≤ z^(r+1) := Nat.pow_le_pow_right hz (by omega)
   have hone : 1≤ z^(r+1) := one_le_pow₀ hz
   have ht (j : ℕ) (hj : j< xs.length) : R.time (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)≤ F*z^u := by
     have ha := volume_mem_le (List.getElem_mem hj)
     have hb := hv j hj.le
     have hbase : volume (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)+1≤(E+3)*z^(r+1) := by
       simp only [volume_pair]
       nlinarith
     have hh := ((hR _).1).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
     simpa only [F,u,mul_pow,← pow_mul,Nat.mul_assoc] using hh
   have hh := fold_prefix_bound R xs b (F*z^u) (E*z^r) hv ht
   have hcopy : volume xs+2*(E*z^r)+1≤(2*E+2)*z^(r+1) := by nlinarith
   have hm := Nat.mul_le_mul hlen (Nat.add_le_add_left (Nat.mul_le_mul_left 20 hcopy) (F*z^u))
   have heq : z*(F*z^u+20*((2*E+2)*z^(r+1)))=
       F*z^(u+1)+(40*E+40)*z^(r+2) := by simp only [pow_succ]; ring
   rw [heq] at hm
   have hp1 : z^(u+1)≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hp2 : z^(r+2)≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hpr : z^r≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hp : z≤ z^e := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by dsimp [e]; omega : 1≤ e)
   have htime := Nat.mul_le_mul_left F hp1
   have hcopies := Nat.mul_le_mul_left (40*E+40) hp2
   constructor
   · rw [Realizer.time_fold]
     change 2*volume (xs,b)+6+Realizer.foldTime R b xs≤(F+100*E+200)*z^e
     have hinput : volume (xs,b)+1=z := rfl
     nlinarith only [hh,hm,htime,hcopies,hp,hinput,hz]
   · change volume (xs.foldl (fun b a => f (a,b)) b)≤ _
     have hv' := hv xs.length le_rfl
     rw [List.take_length] at hv'
     have hout := hv'.trans (Nat.mul_le_mul_left E hpr)
     exact hout.trans (Nat.mul_le_mul_right _ (show E≤ F+100*E+200 by omega))
end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.SignedVectorSumBounds
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 theorem vectorPairs_cons (a : SignedWords) (A B : SignedVector) :
     vectorPairs (a::A,B)=(a,B.headD signedZero)::vectorPairs (A,B.tail) := by
   simp only [vectorPairs,List.length_cons,List.range_succ_eq_map,List.map_cons,List.drop_zero,
     List.headD_cons,List.map_map]
   congr 1
   apply List.map_congr_left
   intro i hi
   simp only [Function.comp_apply,List.drop_succ_cons]
   rw [← List.tail_drop_eq_drop_tail]
   rw [List.drop_add_one_eq_tail_drop]

 theorem vectorSub_cons (a : SignedWords) (A B : SignedVector) :
     vectorSub (a::A,B)=canonicalSub (a,B.headD signedZero)::vectorSub (A,B.tail) := by
   simp only [vectorSub,vectorPairs_cons,List.map_cons]

 theorem vectorSub_width (A B : SignedVector) :
     vectorWidth (vectorSub (A,B))≤ vectorWidth A+vectorWidth B+2*A.length := by
   induction A generalizing B with
   | nil => simp [vectorWidth,vectorSub,vectorPairs]
   | cons a A ih =>
     cases B with
     | nil =>
       rw [vectorSub_cons]
       have hh := ih []
       have ha := canonicalSub_width a signedZero
       have hz : fractionWidth signedZero.2=2 := by decide
       simp only [vectorWidth,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,List.length_cons,List.headD_nil,List.tail_nil] at hh ⊢
       rw [hz] at ha
       omega
     | cons b B =>
       rw [vectorSub_cons]
       have hh := ih B
       have ha := canonicalSub_width a b
       simp only [vectorWidth,List.map_cons,List.sum_cons,List.length_cons,List.headD_cons,List.tail_cons] at hh ⊢
       omega

 theorem vectorWidth_volume (A : SignedVector) : vectorWidth A≤ volume A := signedWidths_sum A
 theorem vectorVolume_width (A : SignedVector) : volume A≤15*vectorWidth A+1 := by
   induction A with
   | nil => simp [vectorWidth]
   | cons a A ih =>
     have ha := signedVolume_width a
     have hw : 1≤ fractionWidth a.2 := by simp [fractionWidth]
     simp only [vectorWidth,List.map_cons,List.sum_cons,volume_cons] at ih ⊢
     nlinarith

 
 
 theorem subtractVector_polynomial : PolyBound subtractVectorRealizer :=
   polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) vectorSub_polynomial

 

 theorem vectorSub_fold_width (xs : List SignedVector) (b : SignedVector) :
     vectorWidth (xs.foldl (fun b a => subtractVector (a,b)) b)≤
       vectorWidth b+(xs.map vectorWidth).sum+2*b.length*xs.length := by
   induction xs generalizing b with
   | nil => simp
   | cons a xs ih =>
     rw [List.foldl_cons]
     have hh := ih (subtractVector (a,b))
     have ha : vectorWidth (subtractVector (a,b))≤ vectorWidth b+vectorWidth a+2*b.length := vectorSub_width b a
     have hl : (subtractVector (a,b)).length=b.length := vectorSub_length _
     rw [hl] at hh
     simp only [List.map_cons,List.sum_cons,List.length_cons]
     nlinarith

 theorem vectorWidths_sum (xs : List SignedVector) : (xs.map vectorWidth).sum≤ volume xs := by
   induction xs with
   | nil => simp
   | cons a xs ih =>
     have ha := vectorWidth_volume a
     simp only [List.map_cons,List.sum_cons,volume_cons]
     omega

 theorem subtractVector_fold_polynomial : PolyBound subtractVectorRealizer.fold := by
   apply polynomial_fold_power subtractVector_polynomial 80 2
   intro xs b j hj
   have hv := vectorVolume_width ((xs.take j).foldl (fun b a => subtractVector (a,b)) b)
   have hw := vectorSub_fold_width (xs.take j) b
   have hb := vectorWidth_volume b
   have hx := vectorWidths_sum (xs.take j)
   have ht := take_volume_le xs j
   have hn := length_volume b
   have hl := length_volume xs
   simp only [List.length_take] at hw
   have hmin : min j xs.length≤ volume xs := (Nat.min_le_right _ _).trans hl
   have hprod := Nat.mul_le_mul_left 2 (Nat.mul_le_mul hn hmin)
   simp only [volume_pair]
   nlinarith

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GramSchmidtRowCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 theorem gsProjectionWith_polynomial : PolyBound gsProjectionWith :=
   polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) gsProjection_polynomial
 
 
 theorem gsProjections_polynomial : PolyBound gsProjectionsRealizer :=
   polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst))
     (polynomial_mapEnvironment gsProjectionWith_polynomial)
 
 
 theorem gsRow_polynomial : PolyBound gsRowRealizer :=
   polynomial_comp (polynomial_pair gsProjections_polynomial (linear_polynomial linear_fst))
     subtractVector_fold_polynomial

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RationalVectorSemantics
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 

 theorem represents_length {n : ℕ} {A : SignedVector} {v : Vec n}
     (h : RepresentsVector A v) : A.length=n := by
   obtain ⟨a,rfl,ha,hv⟩ := h
   simp

 theorem represents_dot {n : ℕ} {A B : SignedVector} {v w : Vec n}
     (hA : RepresentsVector A v) (hB : RepresentsVector B w) :
     0< value (signedDot (A,B)).2.2 ∧
       (signedFractionValue (signedDot (A,B)):ℝ)=inner ℝ v w := by
   obtain ⟨a,rfl,ha,hv⟩ := hA
   obtain ⟨b,rfl,hb,hw⟩ := hB
   have hh := signedDot_ofFn a b ha hb
   refine ⟨hh.1,?_⟩
   rw [hh.2]
   simp only [Rat.cast_sum,Rat.cast_mul,hv,hw,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
   apply Finset.sum_congr rfl
   intro i hi
   ring

 theorem represents_sub {n : ℕ} {A B : SignedVector} {v w : Vec n}
     (hA : RepresentsVector A v) (hB : RepresentsVector B w) :
     RepresentsVector (vectorSub (A,B)) (v-w) := by
   obtain ⟨a,rfl,ha,hv⟩ := hA
   obtain ⟨b,rfl,hb,hw⟩ := hB
   refine ⟨fun i => canonicalSub (a i,b i),vectorSub_ofFn a b,?_,?_⟩
   · intro i
     exact canonicalSub_denpos _ _ (ha i) (hb i)
   · intro i
     rw [canonicalSub_value _ _ (ha i) (hb i),Rat.cast_sub,hv,hw]
     rfl

 theorem represents_scale {n : ℕ} {A : SignedVector} {v : Vec n}
     (hA : RepresentsVector A v) (s : SignedWords) (hs : 0< value s.2.2) :
     RepresentsVector (vectorScale (A,s)) ((signedFractionValue s:ℝ) • v) := by
   obtain ⟨a,rfl,ha,hv⟩ := hA
   refine ⟨fun i => canonicalMul (a i,s),vectorScale_ofFn a s,?_,?_⟩
   · intro i
     exact canonicalMul_denpos _ _ (ha i) hs
   · intro i
     rw [canonicalMul_value _ _ (ha i) hs,Rat.cast_mul,hv]
     simp only [PiLp.smul_apply,smul_eq_mul]
     ring

 theorem represents_projection {n : ℕ} {A B : SignedVector} {v w : Vec n}
     (hA : RepresentsVector A v) (hB : RepresentsVector B w) (hw0 : w≠0) :
     RepresentsVector (gsProjection (A,B)) ((inner ℝ v w/inner ℝ w w) • w) := by
   have hdot := represents_dot hA hB
   have hnorm := represents_dot hB hB
   have hnorm0 : inner ℝ w w≠0 := by rw [real_inner_self_eq_norm_sq]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hw0)
   have hn : 0< value (signedDot (B,B)).2.1 :=
     signed_num_positive_of_nonzero _ (by intro hz; rw [hz,Rat.cast_zero] at hnorm; exact hnorm0 hnorm.2.symm)
   have hden := canonicalDiv_denpos (signedDot (A,B)) (signedDot (B,B)) hdot.1 hn
   have hval : (signedFractionValue (gsCoefficient (A,B)):ℝ)=inner ℝ v w/inner ℝ w w := by
     change (signedFractionValue (canonicalDiv (signedDot (A,B),signedDot (B,B))):ℝ)=_
     rw [canonicalDiv_value _ _ hdot.1 hn,Rat.cast_div,hdot.2,hnorm.2]
   have h := represents_scale hB (gsCoefficient (A,B)) hden
   simpa only [gsProjection,hval] using h

 theorem represents_subtract_fold {n : ℕ} (xs : List SignedVector) (vs : List (Vec n))
     (hxs : List.Forall₂ RepresentsVector xs vs) (A : SignedVector) (v : Vec n)
     (hA : RepresentsVector A v) :
     RepresentsVector (xs.foldl (fun b a => subtractVector (a,b)) A) (v-vs.sum) := by
   induction hxs generalizing A v with
   | nil => simpa using hA
   | @cons a b xs vs hab htail ih =>
     rw [List.foldl_cons]
     have h := ih (vectorSub (A,a)) (v-b) (represents_sub hA hab)
     have he : v-b-vs.sum=v-(b::vs).sum := by simp only [List.sum_cons]; abel
     simpa only [subtractVector,he] using h

 theorem represents_gsRow {n : ℕ} {A : SignedVector} {v : Vec n}
     (hA : RepresentsVector A v) (xs : List SignedVector) (vs : List (Vec n))
     (hxs : List.Forall₂ RepresentsVector xs vs) (hn : ∀ w∈vs,w≠0) :
     RepresentsVector (gsRow (A,xs))
       (v-(vs.map (fun w => (inner ℝ v w/inner ℝ w w) • w)).sum) := by
   have hp : List.Forall₂ RepresentsVector (gsProjections (A,xs))
       (vs.map (fun w => (inner ℝ v w/inner ℝ w w) • w)) := by
     unfold gsProjections
     induction hxs with
     | nil => exact .nil
     | @cons a b xs vs hab htail ih =>
       simp only [List.map_cons]
       exact .cons (represents_projection hA hab (hn b (by simp)))
         (ih (fun w hw => hn w (by simp [hw])))
   exact represents_subtract_fold _ _ hp A v hA

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedFloorCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedFloorMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 

 

 

 

 

 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.IntegerRootStep
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.IntegerRoot
 
 
 
 
end EdgeSublinearMWIS.Main.IntegerRoot
end

-- Solutions.BinaryRootStep
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem difference_canonical (A B : List Bool) : trim (BinarySubtract.difference A B)=BinarySubtract.difference A B := by
   unfold BinarySubtract.difference
   split_ifs <;> simp only [trim,trim_idem]
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryPairs
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryRoot
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedDyadicRound
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RationalRoot
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryWordProduct
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryPowerTwoCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GLSRationalRounding
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RationalRounding.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-!
Computable rational rounding primitives with real error guarantees and grid
encoding bounds. These do not yet supply a RAM implementation.
-/

namespace EdgeSublinearMWIS.Main.GLS.RationalRounding























end EdgeSublinearMWIS.Main.GLS.RationalRounding
end

-- Solutions.SqrtUpperCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedFloorDyadic
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedMatrixCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ListReplacementCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
variable {α : Type} [Coding α]

 
 
 theorem replaceChoice_polynomial (default : α) : PolyBound (replaceChoiceRealizer default) := by
   unfold replaceChoiceRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair
     (polynomial_comp (linear_polynomial (linear_pair linear_fst (linear_comp (linear_comp linear_snd linear_snd) linear_fst))) eqNat_polynomial)
     (linear_polynomial linear_id))
     (polynomial_choose (linear_polynomial (linear_comp (linear_comp linear_snd linear_snd) linear_snd))
       (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) linear_fst)) (lookupList_polynomial default)))
 
 
 theorem replaceList_polynomial (default : α) : PolyBound (replaceListRealizer default) :=
   polynomial_comp (polynomial_pair
     (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) listLength_polynomial) range_polynomial)
     (linear_polynomial linear_id)) (polynomial_mapEnvironment (replaceChoice_polynomial default))
 
 theorem replaceList_ofFn {n : ℕ} (default : α) (f : Fin n → α) (i : Fin n) (a : α) :
     replaceList default (List.ofFn f,(i.val,a))=List.ofFn (Function.update f i a) := by
   apply List.ext_getElem
   · simp [replaceList]
   · intro j hj hk
     have hjn : j< n := by simpa using hk
     simp only [replaceList,List.getElem_map,List.getElem_range,replaceChoice]
     rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem (by simpa using hjn)]
     simp only [Option.getD_some,List.getElem_ofFn,Function.update_apply]
     simp only [Fin.ext_iff,Fin.val_mk]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.DiagonalMaximumCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RationalVectorAppend
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BorderedMatrix
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.InverseMath

 
 
 
 
 

 

 

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.LLLLovaszScalar
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedNearest
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 theorem nearestNumerator_polynomial : PolyBound nearestNumeratorRealizer :=
   polynomial_comp (polynomial_pair
     (linear_polynomial (linear_comp (linear_pair (linear_constant false) linear_fst) linear_cons))
     (linear_polynomial linear_snd)) sumWords_polynomial
 
 theorem nearestDenominator_linear : Linear nearestDenominatorRealizer :=
   linear_comp (linear_pair (linear_constant false) linear_snd) linear_cons
 
 
 theorem nearestMagnitude_polynomial : PolyBound nearestMagnitudeRealizer :=
   polynomial_comp (polynomial_comp (polynomial_pair nearestNumerator_polynomial
     (linear_polynomial nearestDenominator_linear)) divide_polynomial) (linear_polynomial linear_fst)
 
 
 theorem signedNearest_polynomial : PolyBound signedNearestRealizer :=
   polynomial_pair (linear_polynomial linear_fst)
     (polynomial_comp (linear_polynomial linear_snd) nearestMagnitude_polynomial)

 theorem nearest_nat_error (a d : ℕ) (hd : 0< d) :
     |(a:ℚ)/d-((2*a+d)/(2*d):ℕ)|≤(1/2:ℚ) := by
   let r := (2*a+d)/(2*d)
   have hd2 : 0<2*d := by omega
   have hlo := Nat.div_mul_le_self (2*a+d) (2*d)
   have hhi := Nat.lt_mul_div_succ (2*a+d) hd2
   have hloQ : (r:ℚ)*(2*d)≤2*a+d := by exact_mod_cast hlo
   have hhiQ : (2*a+d:ℚ)<(2*d)*(r+1) := by exact_mod_cast hhi
   have hdQ : (0:ℚ)< d := by exact_mod_cast hd
   apply abs_le.mpr
   constructor
   · rw [le_sub_iff_add_le]
     apply (le_div_iff₀ hdQ).mpr
     nlinarith
   · rw [sub_le_iff_le_add]
     apply (div_le_iff₀ hdQ).mpr
     nlinarith

 theorem nearestMagnitude_value (s : FractionWords) (hd : 0< value s.2) :
     value (nearestMagnitude s)=(2*value s.1+value s.2)/(2*value s.2) := by
   have hd' : 0< value (false::s.2) := by simp [value]; omega
   rw [nearestMagnitude,(divide_value _ _ hd').1,nearestNumerator,sumWords_value]
   simp [value,Nat.mul_comm]

 theorem signedNearest_error (s : SignedWords) (hd : 0< value s.2.2) :
     |signedFractionValue s-(signedValue (signedNearest s).1 (signedNearest s).2:ℚ)|≤(1/2:ℚ) := by
   rcases s with ⟨b,N,D⟩
   have h := nearest_nat_error (value N) (value D) hd
   cases b <;> simp only [signedFractionValue,signedNearest,signedValue,
     Bool.false_eq_true,if_false,if_true,Int.cast_natCast,Int.cast_neg,nearestMagnitude_value (N,D) hd]
   · exact h
   · have he : -(value N:ℚ)/value D+(((2*value N+value D)/(2*value D):ℕ):ℚ)=
         -((value N:ℚ)/value D-(((2*value N+value D)/(2*value D):ℕ):ℚ)) := by ring
     simpa only [sub_neg_eq_add,he,abs_neg] using h

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GramSchmidtFoldCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 theorem gsAppend_polynomial : PolyBound gsAppendRealizer :=
   polynomial_comp (polynomial_pair (linear_polynomial linear_snd)
     (polynomial_comp (polynomial_pair gsRow_polynomial (linear_polynomial (linear_constant ([] : List SignedVector))))
       (linear_polynomial linear_cons))) appendList_polynomial
 
 
 theorem gsAppend_length (s : SignedVector×List SignedVector) : (gsAppend s).length=s.2.length+1 := by
   simp [gsAppend]
 theorem gsMatrix_length (bs : List SignedVector) : (gsMatrix bs).length=bs.length := by
   have h (xs : List SignedVector) (acc : List SignedVector) :
       (xs.foldl (fun gs b => gsAppend (b,gs)) acc).length=acc.length+xs.length := by
     induction xs generalizing acc with
     | nil => simp
     | cons a xs ih => rw [List.foldl_cons,ih,gsAppend_length]; simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
   simpa only [gsMatrix,List.length_nil,Nat.zero_add] using h bs []

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLSizeReductionMath
noncomputable section

namespace EdgeSublinearMWIS.Main.LLLBounds.GS
open LLLFactor.RedBasis LLLFactor.Reduction
section GS
variable {n : ℕ}

lemma gs_orth (b : Fin n → Vec n) {i j : Fin n} (h : i ≠ j) :
    inner ℝ (gs b i) (gs b j) = 0 :=
  InnerProductSpace.gramSchmidt_orthogonal ℝ b h

lemma mu_eq (b : Fin n → Vec n) (i j : Fin n) :
    mu b i j = inner ℝ (gs b j) (b i) / inner ℝ (gs b j) (gs b j) := by
  unfold mu; rw [real_inner_comm]

lemma b_eq (b : Fin n → Vec n) (i : Fin n) :
    b i = gs b i + ∑ j ∈ Finset.Iio i, mu b i j • gs b j := by
  have h := InnerProductSpace.gramSchmidt_def'' ℝ b i
  conv_lhs => rw [h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mu_eq]
  simp only [gs, real_inner_self_eq_norm_sq]
  simp

lemma proj_id (b : Fin n → Vec n) (i : Fin n) (δ : Vec n)
    (hδ : δ ∈ Submodule.span ℝ (gs b '' Set.Iio i)) :
    ∑ j ∈ Finset.Iio i, (inner ℝ (gs b j) δ / inner ℝ (gs b j) (gs b j)) • gs b j = δ := by
  induction hδ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    have hl' : l ∈ Finset.Iio i := by simpa using hl
    rw [Finset.sum_eq_single_of_mem l hl']
    · by_cases h0 : gs b l = 0
      · simp [h0]
      · have : inner ℝ (gs b l) (gs b l) ≠ 0 := by simpa using h0
        rw [div_self this, one_smul]
    · intro j _ hj
      rw [gs_orth b hj, zero_div, zero_smul]
  | zero => simp
  | add x y _ _ ihx ihy =>
    simp only [inner_add_right, add_div, add_smul, Finset.sum_add_distrib, ihx, ihy]
  | smul a x _ ihx =>
    simp only [inner_smul_right, mul_div_assoc, mul_smul, ← Finset.smul_sum, ihx]

lemma gs_shift (b b' : Fin n → Vec n) (t : Fin n)
    (h : ∀ i ≤ t, b' i - b i ∈ Submodule.span ℝ (gs b '' Set.Iio i)) :
    ∀ i ≤ t, gs b' i = gs b i := by
  intro i
  induction i using WellFoundedLT.induction with
  | _ i ih =>
  intro hi
  have key : ∀ j ∈ Finset.Iio i, gs b' j = gs b j := fun j hj =>
    ih j (Finset.mem_Iio.1 hj) ((Finset.mem_Iio.1 hj).le.trans hi)
  have h1 := b_eq b i
  have h2 := b_eq b' i
  have hp := proj_id b i (b' i - b i) (h i hi)
  have hb' : b' i = b i + (b' i - b i) := by abel
  have e1 : b i - gs b i = ∑ j ∈ Finset.Iio i, mu b i j • gs b j := by
    rw [sub_eq_iff_eq_add']; exact h1
  have hsum : ∑ j ∈ Finset.Iio i, mu b' i j • gs b' j =
      (b i - gs b i) + (b' i - b i) := by
    rw [← hp, e1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [mu_eq, mu_eq, key j hj, ← add_smul, ← add_div, ← inner_add_right, add_sub_cancel]
  have : gs b' i = gs b i := by
    have := h2
    rw [hsum] at this
    have h3 : gs b' i = b' i - ((b i - gs b i) + (b' i - b i)) := by
      rw [eq_sub_iff_add_eq]; exact this.symm
    rw [h3]; abel
  exact this




lemma reduceBy_self (c : Fin n → Vec n) (κ l : Fin n) (r : ℤ) :
    reduceBy c κ l r κ = c κ - (r : ℝ) • c l := by
  simp [reduceBy]

lemma reduceBy_ne (c : Fin n → Vec n) (κ l : Fin n) (r : ℤ) (j : Fin n) (h : j ≠ κ) :
    reduceBy c κ l r j = c j := by
  simp [reduceBy, Function.update_of_ne h]

lemma gs_reduceBy (c : Fin n → Vec n) (κ l : Fin n) (hl : l < κ) (r : ℤ) (i : Fin n) :
    gs (reduceBy c κ l r) i = gs c i := by
  refine gs_shift c (reduceBy c κ l r) i ?_ i le_rfl
  intro i' _
  by_cases h : i' = κ
  · subst h
    rw [reduceBy_self]
    have h1 : c l ∈ Submodule.span ℝ (gs c '' Set.Iic l) :=
      InnerProductSpace.mem_span_gramSchmidt ℝ c (le_refl l)
    have h2 : c l ∈ Submodule.span ℝ (gs c '' Set.Iio i') :=
      Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iio.2 hl)) h1
    have : c i' - (r : ℝ) • c l - c i' = -((r : ℝ) • c l) := by abel
    rw [this]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ h2)
  · rw [reduceBy_ne c κ l r i' h, sub_self]; exact Submodule.zero_mem _

lemma mu_reduceBy (c : Fin n → Vec n) (κ l : Fin n) (hl : l < κ) (r : ℤ) (i j : Fin n) :
    mu (reduceBy c κ l r) i j = if i = κ then mu c κ j - r * mu c l j else mu c i j := by
  rw [mu_eq, gs_reduceBy c κ l hl]
  by_cases h : i = κ
  · subst h
    rw [if_pos rfl, reduceBy_self, mu_eq, mu_eq, inner_sub_right, real_inner_smul_right, sub_div,
      mul_div_assoc]
  · rw [if_neg h, reduceBy_ne c κ l r i h, mu_eq]

lemma mu_self (c : Fin n → Vec n) (l : Fin n) (h : gs c l ≠ 0) : mu c l l = 1 := by
  rw [mu_eq]
  have h1 := b_eq c l
  have h2 : inner ℝ (gs c l) (c l) = inner ℝ (gs c l) (gs c l) := by
    conv_lhs => rw [h1]
    rw [inner_add_right, inner_sum]
    have : ∑ x ∈ Finset.Iio l, inner ℝ (gs c l) (mu c l x • gs c x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [real_inner_smul_right, gs_orth c (Finset.mem_Iio.1 hx).ne', mul_zero]
    rw [this, add_zero]
  rw [h2]
  exact div_self (by simpa using h)

lemma mu_zero_of_lt (c : Fin n → Vec n) {i j : Fin n} (h : i < j) : mu c i j = 0 := by
  have := InnerProductSpace.gramSchmidt_inv_triangular ℝ c h
  rw [mu_eq]; change inner ℝ (InnerProductSpace.gramSchmidt ℝ c j) (c i) = 0 at this
  rw [show inner ℝ (gs c j) (c i) = 0 from this, zero_div]

end GS
end EdgeSublinearMWIS.Main.LLLBounds.GS
end

-- Solutions.GramSchmidtFoldSemantics
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 

 theorem finitePrefix_succ {α : Type} {n k : ℕ} (f : Fin n → α) (hk : k+1≤ n) :
     finitePrefix f (k+1) hk=finitePrefix f k (by omega)++[f ⟨k,by omega⟩] := by
   unfold finitePrefix
   rw [List.ofFn_succ']
   simp only [List.concat_eq_append,Fin.val_castSucc,Fin.val_last]

 theorem prefix_sum {α : Type} [AddCommMonoid α] {n : ℕ}
     (f : Fin n → α) (i : Fin n) :
     (finitePrefix f i.val (by omega)).sum=∑ j∈Finset.Iio i,f j := by
   rw [finitePrefix,List.sum_ofFn]
   apply Finset.sum_bij (fun j hj => (⟨j.val,lt_trans j.isLt i.isLt⟩:Fin n))
   · intro j hj
     simp only [Finset.mem_Iio,Fin.lt_def]
     exact j.isLt
   · intro a ha b hb he
     exact Fin.ext (congrArg (fun x : Fin n => x.val) he)
   · intro j hj
     refine ⟨⟨j.val,(show j < i from Finset.mem_Iio.mp hj)⟩,Finset.mem_univ _,?_⟩
     rfl
   · intro j hj
     rfl

 theorem represents_gsRow_exact {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
     (i : Fin n) (A : SignedVector) (xs : List SignedVector)
     (hA : RepresentsVector A (b i))
     (hxs : List.Forall₂ RepresentsVector xs (finitePrefix (gs b) i.val (by omega))) :
     RepresentsVector (gsRow (A,xs)) (gs b i) := by
   have hn : ∀ w∈finitePrefix (gs b) i.val (by omega),w≠0 := by
     intro w hw
     obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
     exact InnerProductSpace.gramSchmidt_ne_zero _ hb
   have h := represents_gsRow hA xs _ hxs hn
   have he : (finitePrefix (gs b) i.val (by omega)).map
       (fun w => (inner ℝ (b i) w/inner ℝ w w) • w)=
       finitePrefix (fun j => mu b i j • gs b j) i.val (by omega) := by
     simp only [finitePrefix,List.map_ofFn]
     rfl
   rw [he,prefix_sum] at h
   have hgs := LLLBounds.GS.b_eq b i
   have heq : b i-(∑ j∈Finset.Iio i,mu b i j • gs b j)=gs b i := by rw [hgs]; abel
   rwa [heq] at h

 theorem gsMatrix_append (xs : List SignedVector) (a : SignedVector) :
     gsMatrix (xs++[a])=gsAppend (a,gsMatrix xs) := by
   simp only [gsMatrix,List.foldl_append,List.foldl_cons,List.foldl_nil]

 theorem gsMatrix_prefix_rep {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
     (A : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (b i))
     (k : ℕ) (hk : k≤ n) :
     List.Forall₂ RepresentsVector (gsMatrix (finitePrefix A k hk))
       (finitePrefix (gs b) k hk) := by
   induction k with
   | zero => simp [finitePrefix,gsMatrix]
   | succ k ih =>
     rw [finitePrefix_succ,gsMatrix_append,gsAppend,finitePrefix_succ]
     apply List.rel_append (ih (by omega))
     apply List.Forall₂.cons _ List.Forall₂.nil
     exact represents_gsRow_exact b hb ⟨k,by omega⟩ _ _ (hA _) (ih (by omega))

 theorem gsMatrix_rep {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
     (A : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (b i)) :
     List.Forall₂ RepresentsVector (gsMatrix (List.ofFn A)) (List.ofFn (gs b)) :=
   gsMatrix_prefix_rep b hb A hA n le_rfl

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedCanonicalBounds
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 

 theorem signedReduced_idempotent (s : SignedWords) (hd : 0< value s.2.2) :
     SignedCanonical (signedReduced s) := by
   change signedReduced (signedReduced s)=signedReduced s
   rw [signedReduced_canonical _ (signedReduced_denpos s hd),signedReduced_value s hd,
     signedReduced_canonical s hd]

 theorem canonicalSub_canonical (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.2) :
     SignedCanonical (canonicalSub (a,b)) :=
   signedReduced_idempotent _ (signedFractionAdd_denpos a (signedFractionNeg b) ha hb)

 theorem signedCanonical_width (s : SignedWords) (hs : SignedCanonical s)
     (hd : 0< value s.2.2) (P : ℕ)
     (hn : (signedFractionValue s).num.natAbs≤2^P)
     (hD : (signedFractionValue s).den≤2^P) : fractionWidth s.2≤ P+2 := by
   have hbits (a : ℕ) (ha : a≤2^P) : (natBits a).length≤ P+1 := by
     simp only [natBits,List.length_map]
     apply (Nat.digits_length_le_iff (by decide : 1<2) _).mpr
     exact ha.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
   have h1 := hbits _ hn
   have h2 := hbits _ hD
   have he := signedReduced_canonical s hd
   rw [hs] at he
   rw [he]
   dsimp only [fractionWidth]
   omega

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GramSchmidtCanonical
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 theorem vectorSub_canonical {n : ℕ} {A B : SignedVector} {v w : Vec n}
     (hA : RepresentsVector A v) (hB : RepresentsVector B w) : VectorCanonical (vectorSub (A,B)) := by
   obtain ⟨a,rfl,ha,hv⟩ := hA
   obtain ⟨b,rfl,hb,hw⟩ := hB
   rw [vectorSub_ofFn]
   intro s hs
   obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hs
   exact canonicalSub_canonical _ _ (ha i) (hb i)

 theorem subtract_fold_canonical {n : ℕ} (xs : List SignedVector) (vs : List (Vec n))
     (hxs : List.Forall₂ RepresentsVector xs vs) (A : SignedVector) (v : Vec n)
     (hA : RepresentsVector A v) (hcan : VectorCanonical A) :
     VectorCanonical (xs.foldl (fun b a => subtractVector (a,b)) A) := by
   induction hxs generalizing A v with
   | nil => exact hcan
   | @cons a b xs vs hab htail ih =>
     rw [List.foldl_cons]
     exact ih _ _ (represents_sub hA hab) (vectorSub_canonical hA hab)

 theorem represents_projections {n : ℕ} {A : SignedVector} {v : Vec n}
     (hA : RepresentsVector A v) (xs : List SignedVector) (vs : List (Vec n))
     (hxs : List.Forall₂ RepresentsVector xs vs) (hn : ∀ w∈vs,w≠0) :
     List.Forall₂ RepresentsVector (gsProjections (A,xs))
       (vs.map (fun w => (inner ℝ v w/inner ℝ w w) • w)) := by
   unfold gsProjections
   induction hxs with
   | nil => exact .nil
   | @cons a b xs vs hab htail ih =>
     simp only [List.map_cons]
     exact .cons (represents_projection hA hab (hn b (by simp)))
       (ih (fun w hw => hn w (by simp [hw])))

 theorem gsRow_canonical {n : ℕ} {A : SignedVector} {v : Vec n}
     (hA : RepresentsVector A v) (hcan : VectorCanonical A)
     (xs : List SignedVector) (vs : List (Vec n))
     (hxs : List.Forall₂ RepresentsVector xs vs) (hn : ∀ w∈vs,w≠0) :
     VectorCanonical (gsRow (A,xs)) :=
   subtract_fold_canonical _ _ (represents_projections hA xs vs hxs hn) A v hA hcan

 theorem gsMatrix_prefix_canonical {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
     (A : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (b i))
     (hcan : ∀ i,VectorCanonical (A i)) (k : ℕ) (hk : k≤ n) :
     ∀ row∈gsMatrix (finitePrefix A k hk),VectorCanonical row := by
   induction k with
   | zero => simp [finitePrefix,gsMatrix]
   | succ k ih =>
     rw [finitePrefix_succ,gsMatrix_append,gsAppend]
     intro row hrow
     rcases List.mem_append.mp hrow with hrow|hrow
     · exact ih (by omega) row hrow
     · have hrow' : row=gsRow (A ⟨k,by omega⟩,gsMatrix (finitePrefix A k (by omega))) := by
         simpa only [List.mem_singleton] using hrow
       rw [hrow']
       apply gsRow_canonical (hA _) (hcan _) _ (finitePrefix (gs b) k (by omega))
         (gsMatrix_prefix_rep b hb A hA k (by omega))
       intro w hw
       obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
       exact InnerProductSpace.gramSchmidt_ne_zero _ hb

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GramSchmidtCramerProjection
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 theorem gs_orthogonal_span {n : ℕ} (b : Fin n → Vec n) (i : Fin n)
     (x : Vec n) (hx : x∈Submodule.span ℝ (b '' Set.Iio i)) : inner ℝ (gs b i) x=0 := by
   induction hx using Submodule.span_induction with
   | mem x hx =>
     obtain ⟨j,hj,rfl⟩ := hx
     exact InnerProductSpace.gramSchmidt_inv_triangular ℝ b hj
   | zero => simp
   | add x y hx hy ihx ihy => simp only [inner_add_right,ihx,ihy,add_zero]
   | smul a x hx ih => simp only [inner_smul_right,ih,mul_zero]

 theorem gs_residual_unique {n : ℕ} (b : Fin n → Vec n) (i : Fin n) (g : Vec n)
     (hspan : g-b i∈Submodule.span ℝ (b '' Set.Iio i))
     (horth : ∀ j< i,inner ℝ (b j) g=0) : g=gs b i := by
   let S := Submodule.span ℝ (b '' Set.Iio i)
   have hgs : gs b i-b i∈S := by
     have he := GS.b_eq b i
     have hsum : (∑ j∈Finset.Iio i,mu b i j • gs b j)∈S := by
       apply Submodule.sum_mem
       intro j hj
       apply Submodule.smul_mem
       have hmem := InnerProductSpace.gramSchmidt_mem_span ℝ b (le_rfl : j≤ j)
       apply (Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iio.mpr (Finset.mem_Iio.mp hj)))) hmem
     have heq : gs b i-b i= -(∑ j∈Finset.Iio i,mu b i j • gs b j) := by rw [he]; abel
     rw [heq]
     exact S.neg_mem hsum
   have hdelta : g-gs b i∈S := by
     have hh := S.sub_mem hspan hgs
     convert hh using 1 <;> abel
   have hg : ∀ x∈S,inner ℝ g x=0 := by
     intro x hx
     induction hx using Submodule.span_induction with
     | mem x hx =>
       obtain ⟨j,hj,rfl⟩ := hx
       rw [real_inner_comm]
       exact horth j hj
     | zero => simp
     | add x y hx hy ihx ihy => simp only [inner_add_right,ihx,ihy,add_zero]
     | smul a x hx ih => simp only [inner_smul_right,ih,mul_zero]
   have he : inner ℝ (g-gs b i) (g-gs b i)=0 := by
     rw [inner_sub_left,hg _ hdelta,gs_orthogonal_span b i _ hdelta,sub_zero]
   exact sub_eq_zero.mp (inner_self_eq_zero.mp he)

 theorem gs_from_projection_coefficients {n : ℕ} (b : Fin n → Vec n) (i : Fin n)
     (coef : Fin i.val → ℝ)
     (hsolve : ∀ j : Fin i.val,
       ∑ k : Fin i.val, inner ℝ (b ⟨j.val,by omega⟩) (b ⟨k.val,by omega⟩)*coef k=
         inner ℝ (b ⟨j.val,by omega⟩) (b i)) :
     gs b i=b i-∑ j : Fin i.val, coef j • b ⟨j.val,by omega⟩ := by
   symm
   apply gs_residual_unique b i
   · have hsum : (∑ j : Fin i.val, coef j • b ⟨j.val,by omega⟩)∈Submodule.span ℝ (b '' Set.Iio i) := by
       apply Submodule.sum_mem
       intro j hj
       apply Submodule.smul_mem
       exact Submodule.subset_span ⟨⟨j.val,by omega⟩,j.isLt,rfl⟩
     have he : (b i-∑ j : Fin i.val, coef j • b ⟨j.val,by omega⟩)-b i=
         -(∑ j : Fin i.val, coef j • b ⟨j.val,by omega⟩) := by abel
     rw [he]
     exact Submodule.neg_mem _ hsum
   · intro j hj
     rw [inner_sub_right,inner_sum]
     have hh := hsolve ⟨j.val,hj⟩
     simp only [inner_smul_right] at ⊢
     have he : (∑ k : Fin i.val, coef k*inner ℝ (b j) (b ⟨k.val,by omega⟩))=
         inner ℝ (b j) (b i) := by
       simpa only [mul_comm] using hh
     rw [he,sub_self]

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.IntegerVertexScale
noncomputable section

open scoped BigOperators Classical
open Matrix LinearOptimization
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools






end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.IntegralLLLPotential
noncomputable section

open scoped BigOperators Classical
open Matrix LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds



theorem inner_embed {n : ℕ} (b : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    inner ℝ (embed b i) (embed b j) = ((∑ k, b i k*b j k : ℤ) : ℝ) := by
  simp [embed,PiLp.inner_apply,real_inner_comm,mul_comm]

theorem integral_gram {n : ℕ} (b : Matrix (Fin n) (Fin n) ℤ) (i : ℕ) (hi : i≤ n) :
    ∃ z : ℤ, gram (embed b) i=(z:ℝ) := by
  let A : Matrix (Fin i) (Fin i) ℤ := fun j k =>
    ∑ l, b (Fin.castLE hi j) l*b (Fin.castLE hi k) l
  refine ⟨A.det,?_⟩
  rw [LLLFactor.Reduction.gram,dif_pos hi,Int.cast_det]
  congr 1
  ext j k
  exact inner_embed b _ _

theorem gram_ge_one {n : ℕ} (b : Matrix (Fin n) (Fin n) ℤ)
    (hb : LinearIndependent ℝ (embed b)) (i : ℕ) (hi : i≤ n) :
    1≤ gram (embed b) i := by
  have hpos := (gram_eq_prod_gs (embed b) hb).1 i hi |>.2
  obtain ⟨z,hz⟩ := integral_gram b i hi
  rw [hz] at hpos ⊢
  have hz0 : 0< z := by exact_mod_cast hpos
  have hz1 : 1≤ z := by omega
  exact_mod_cast hz1



theorem reduce_embed {n : ℕ} (b : Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin n) (r : ℤ) :
    reduceBy (embed b) i j r = embed (Function.update b i (fun k => b i k-r*b j k)) := by
  unfold Matrix at b
  funext a
  by_cases ha : a=i
  · subst a
    ext k
    simp [reduceBy,embed,Function.update_self]
  · ext k
    simp [reduceBy,embed,ha,Function.update_of_ne]

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.IntegralLLLClosure
noncomputable section

open scoped Classical
open Matrix LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds



theorem integral_reduce {n : ℕ} {b : Fin n → Vec n} (hb : IntegralRows b)
    (i j : Fin n) (r : ℤ) : IntegralRows (reduceBy b i j r) := by
  obtain ⟨B,rfl⟩ := hb
  exact ⟨_,reduce_embed B i j r⟩









end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.GeometricDescentBound
noncomputable section

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RuntimeMath





end EdgeSublinearMWIS.Main.RuntimeMath
end

-- Solutions.IntegralLLLStepBound
noncomputable section

open scoped BigOperators Classical
open Matrix LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 

 

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.IntegerHalfspaceEncoding
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryDual









end EdgeSublinearMWIS.Main.BinaryDual
end

-- Solutions.IntegralLLLInitialBound
noncomputable section

open scoped BigOperators Classical
open Matrix LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 theorem factorial_le_two_square (i : ℕ) : i.factorial≤2^(i*i) := by
   calc
     i.factorial≤ i^i := Nat.factorial_le_pow i
     _≤(2^i)^i := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) i
     _=2^(i*i) := (pow_mul 2 i i).symm

 theorem integer_inner_bound {n L : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hB : ∀ i j, |B i j|≤(2:ℤ)^L) (i j : Fin n) :
     |∑ k, B i k*B j k|≤(2:ℤ)^(n+2*L) := by
   calc
     _ ≤ ∑ k : Fin n, |B i k*B j k| := Finset.abs_sum_le_sum_abs _ _
     _ ≤ ∑ _k : Fin n, (2:ℤ)^(2*L) := by
       apply Finset.sum_le_sum
       intro k hk
       rw [abs_mul,show 2*L=L+L by omega,pow_add]
       exact mul_le_mul (hB i k) (hB j k) (abs_nonneg _) (by positivity)
     _ = (n:ℤ)*(2:ℤ)^(2*L) := by simp
     _ ≤ (2:ℤ)^n*(2:ℤ)^(2*L) := by
       apply mul_le_mul_of_nonneg_right _ (by positivity)
       exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self : n<2^n)
     _ = _ := (pow_add _ _ _).symm

 

 

end EdgeSublinearMWIS.Main.LLLBounds

namespace EdgeSublinearMWIS.Main.LLLBounds
 
end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.GramSchmidtIntegerCoordinates
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 
 

 theorem prefixGram_det_cast {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
     ((prefixGram B i).det:ℝ)=LLLFactor.Reduction.gram (embed B) i.val := by
   rw [LLLFactor.Reduction.gram,dif_pos (by omega),Int.cast_det]
   congr 1
   ext j k
   exact (inner_embed B _ _).symm

 theorem prefixGram_det_pos {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hb : LinearIndependent ℝ (embed B)) (i : Fin n) : 0<(prefixGram B i).det := by
   have h := ((gram_eq_prod_gs (embed B) hb).1 i.val (by omega)).2
   rw [← prefixGram_det_cast] at h
   exact_mod_cast h

 theorem int_cramer_cast {m : ℕ} (M : Matrix (Fin m) (Fin m) ℤ) (b : Fin m → ℤ) (j : Fin m) :
     (M.cramer b j:ℝ)=(M.map (Int.cast:ℤ→ℝ)).cramer (fun i => (b i:ℝ)) j := by
   simp only [Matrix.cramer_apply]
   rw [Int.cast_det]
   congr 1
   ext i k
   simp [Matrix.updateCol_apply]

 

 theorem gs_integer_coordinates {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hb : LinearIndependent ℝ (embed B)) (i k : Fin n) :
     gs (embed B) i k=(gsNumerator B i k:ℝ)/((prefixGram B i).det:ℝ) := by
   let M := prefixGram B i
   let C := prefixCross B i
   let R : Matrix (Fin i.val) (Fin i.val) ℝ := M.map (Int.cast:ℤ→ℝ)
   let Z := M.cramer C
   let D := M.det
   have hDpos : (0:ℝ)<(D:ℝ) := by exact_mod_cast prefixGram_det_pos B hb i
   have hD : (D:ℝ)≠0 := ne_of_gt hDpos
   have hdet : R.det=(D:ℝ) := (Int.cast_det M).symm
   let coef : Fin i.val → ℝ := fun j => (Z j:ℝ)/(D:ℝ)
   have hcoef : coef=(D:ℝ)⁻¹ • R.cramer (fun j => (C j:ℝ)) := by
     funext j
     change (Z j:ℝ)/(D:ℝ)=(D:ℝ)⁻¹*R.cramer (fun j => (C j:ℝ)) j
     rw [show R.cramer (fun j => (C j:ℝ)) j=(Z j:ℝ) from (int_cramer_cast M C j).symm]
     ring
   have hsolve : R *ᵥ coef=fun j => (C j:ℝ) := by
     rw [hcoef,Matrix.mulVec_smul,Matrix.mulVec_cramer,hdet,smul_smul,inv_mul_cancel₀ hD,one_smul]
   have hproj := gs_from_projection_coefficients (embed B) i coef (by
     intro j
     have h := congrFun hsolve j
     simpa only [Matrix.mulVec,dotProduct,R,M,prefixGram,C,prefixCross,
       Matrix.map_apply,inner_embed] using h)
   rw [hproj]
   simp only [WithLp.ofLp_sub,WithLp.ofLp_sum,WithLp.ofLp_smul,Pi.sub_apply,
     Finset.sum_apply,Pi.smul_apply,smul_eq_mul,embed,WithLp.ofLp_toLp]
   dsimp only [coef,Z,D,M,C,gsNumerator]
   simp only [Int.cast_sub,Int.cast_mul,Int.cast_sum]
   simp_rw [div_mul_eq_mul_div]
   rw [← Finset.sum_div]
   field_simp [show ((prefixGram B i).det:ℝ)≠0 from hD]

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.GramSchmidtCoordinateBounds
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 theorem bounded_int_det {n m H : ℕ} (hm : m≤ n) (M : Matrix (Fin m) (Fin m) ℤ)
     (hM : ∀ i j, |M i j|≤(2:ℤ)^H) : |M.det|≤(2:ℤ)^(n*n+H*n) := by
   have hd : |M.det|≤(m.factorial:ℤ)*((2:ℤ)^H)^m := by
     simpa using (Matrix.det_le (abv:=AbsoluteValue.abs) hM)
   have hf : (m.factorial:ℤ)≤(2:ℤ)^(m*m) := by exact_mod_cast factorial_le_two_square m
   calc
     _≤(m.factorial:ℤ)*((2:ℤ)^H)^m := hd
     _≤(2:ℤ)^(m*m)*((2:ℤ)^H)^m := mul_le_mul_of_nonneg_right hf (by positivity)
     _=(2:ℤ)^(m*m+H*m) := by rw [← pow_mul,← pow_add]
     _≤(2:ℤ)^(n*n+H*n) := by apply pow_le_pow_right₀ (by norm_num); nlinarith

 theorem gs_denominator_bound {n L : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hB : ∀ i j, |B i j|≤(2:ℤ)^L) (i : Fin n) :
     |(prefixGram B i).det|≤(2:ℤ)^(n*n+(n+2*L)*n) := by
   apply bounded_int_det (by omega)
   intro j k
   exact integer_inner_bound B hB _ _

 theorem gs_cramer_bound {n L : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hB : ∀ i j, |B i j|≤(2:ℤ)^L) (i : Fin n) (j : Fin i.val) :
     |(prefixGram B i).cramer (prefixCross B i) j|≤(2:ℤ)^(n*n+(n+2*L)*n) := by
   rw [Matrix.cramer_apply]
   apply bounded_int_det (by omega)
   intro a b
   by_cases hbj : b=j
   · subst b
     rw [Matrix.updateCol_self]
     exact integer_inner_bound B hB _ _
   · rw [Matrix.updateCol_ne hbj]
     exact integer_inner_bound B hB _ _

 theorem gs_numerator_bound {n L : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hB : ∀ i j, |B i j|≤(2:ℤ)^L) (i k : Fin n) :
     |gsNumerator B i k|≤(2:ℤ)^((n*n+(n+2*L)*n)+L+n+1) := by
   let J := n*n+(n+2*L)*n
   have hD : |(prefixGram B i).det|≤(2:ℤ)^J := gs_denominator_bound B hB i
   have hZ : ∀ j, |(prefixGram B i).cramer (prefixCross B i) j|≤(2:ℤ)^J := gs_cramer_bound B hB i
   have hprod (j : Fin i.val) : |(prefixGram B i).cramer (prefixCross B i) j*B ⟨j.val,by omega⟩ k|≤(2:ℤ)^(J+L) := by
     rw [abs_mul,pow_add]
     exact mul_le_mul (hZ j) (hB _ _) (abs_nonneg _) (by positivity)
   have hs : |∑ j : Fin i.val,(prefixGram B i).cramer (prefixCross B i) j*B ⟨j.val,by omega⟩ k|≤(i.val:ℤ)*(2:ℤ)^(J+L) := by
     calc
       _≤∑ j : Fin i.val,|(prefixGram B i).cramer (prefixCross B i) j*B ⟨j.val,by omega⟩ k| := Finset.abs_sum_le_sum_abs _ _
       _≤∑ _j : Fin i.val,(2:ℤ)^(J+L) := Finset.sum_le_sum (fun j hj => hprod j)
       _=_ := by simp
   have hfirst : |(prefixGram B i).det*B i k|≤(2:ℤ)^(J+L) := by
     rw [abs_mul,pow_add]
     exact mul_le_mul hD (hB i k) (abs_nonneg _) (by positivity)
   have hn : (i.val:ℤ)+1≤(2:ℤ)^(n+1) := by
     have h1 : i.val+1≤ n+1 := by omega
     have h2 : n+1≤2^(n+1) := Nat.le_of_lt Nat.lt_two_pow_self
     exact_mod_cast h1.trans h2
   calc
     _≤|(prefixGram B i).det*B i k|+
         |∑ j : Fin i.val,(prefixGram B i).cramer (prefixCross B i) j*B ⟨j.val,by omega⟩ k| := abs_sub _ _
     _≤((i.val:ℤ)+1)*(2:ℤ)^(J+L) := by nlinarith
     _≤(2:ℤ)^(n+1)*(2:ℤ)^(J+L) := mul_le_mul_of_nonneg_right hn (by positivity)
     _=_ := by rw [← pow_add]; congr 1 <;> omega

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.GramSchmidtRationalBounds
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds
open RawStack

 theorem rational_integer_bounds (a : ℤ) (d P : ℕ) (hd : 0< d)
     (ha : a.natAbs≤2^P) (hb : d≤2^P) :
     ((a:ℚ)/d).num.natAbs≤2^P ∧ ((a:ℚ)/d).den≤2^P := by
   have h := normalized_rat_num_den a d hd
   rw [h.1,h.2]
   exact ⟨(Nat.div_le_self _ _).trans ha,(Nat.div_le_self _ _).trans hb⟩

 theorem gs_rational_coordinate_bound {n L : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hb : LinearIndependent ℝ (embed B))
     (hB : ∀ i j, |B i j|≤(2:ℤ)^L) (i k : Fin n) :
     ∃ q : ℚ, (q:ℝ)=gs (embed B) i k ∧
       q.num.natAbs≤2^((n*n+(n+2*L)*n)+L+n+1) ∧
       q.den≤2^((n*n+(n+2*L)*n)+L+n+1) := by
   let a := gsNumerator B i k
   let d := (prefixGram B i).det
   let P := (n*n+(n+2*L)*n)+L+n+1
   have hd : 0< d := prefixGram_det_pos B hb i
   have hdN : 0< d.natAbs := Int.natAbs_pos.mpr (ne_of_gt hd)
   have hdcast : (d.natAbs:ℤ)=d := by rw [Int.natCast_natAbs,abs_of_pos hd]
   have ha : a.natAbs≤2^P := by
     have h : |a|≤(2:ℤ)^P := gs_numerator_bound B hB i k
     rw [← Int.natCast_natAbs] at h
     exact_mod_cast h
   have hb' : d.natAbs≤2^P := by
     have h : |d|≤(2:ℤ)^P := (gs_denominator_bound B hB i).trans
       (pow_le_pow_right₀ (by norm_num) (by dsimp [P]; omega))
     rw [← Int.natCast_natAbs] at h
     exact_mod_cast h
   have hbound := rational_integer_bounds a d.natAbs P hdN ha hb'
   refine ⟨(a:ℚ)/d.natAbs,?_,hbound⟩
   rw [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,gs_integer_coordinates B hb i k]
   have he : (d.natAbs:ℝ)=(d:ℝ) := by
     simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℝ)) hdcast
   exact congrArg (fun x : ℝ => (a:ℝ)/x) he

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.GramSchmidtWordBounds
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 theorem represents_gs_word_bound {n L : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hb : LinearIndependent ℝ (embed B)) (hB : ∀ i j, |B i j|≤(2:ℤ)^L)
     (i : Fin n) (A : SignedVector) (hA : RepresentsVector A (gs (embed B) i))
     (hcan : VectorCanonical A) :
     ∀ s∈A,volume s≤14*(((n*n+(n+2*L)*n)+L+n+1)+2) := by
   obtain ⟨a,rfl,ha,hv⟩ := hA
   intro s hs
   obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hs
   obtain ⟨q,hq,hn,hd⟩ := gs_rational_coordinate_bound B hb hB i k
   have he : signedFractionValue (a k)=q := Rat.cast_injective ((hv k).trans hq.symm)
   have hc := hcan (a k) (List.mem_ofFn.mpr ⟨k,rfl⟩)
   have hw := signedCanonical_width (a k) hc (ha k) _ (by rwa [he]) (by rwa [he])
   exact (signedVolume_width (a k)).trans (Nat.mul_le_mul_left 14 hw)

 theorem forall2_left_exists {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
     (h : List.Forall₂ R xs ys) : ∀ x∈xs,∃ y∈ys,R x y := by
   induction h with
   | nil => simp
   | @cons a b xs ys hab htail ih =>
     intro x hx
     rcases List.mem_cons.mp hx with rfl|hx
     · exact ⟨b,List.mem_cons_self,hab⟩
     · obtain ⟨y,hy,hxy⟩ := ih x hx
       exact ⟨y,List.mem_cons_of_mem b hy,hxy⟩

 theorem gsMatrix_prefix_volume {n L : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hb : LinearIndependent ℝ (embed B)) (hB : ∀ i j, |B i j|≤(2:ℤ)^L)
     (A : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (embed B i))
     (hcan : ∀ i,VectorCanonical (A i)) (k : ℕ) (hk : k≤ n) :
     volume (gsMatrix (finitePrefix A k hk))≤
       n*(n*(14*(((n*n+(n+2*L)*n)+L+n+1)+2)+1)+2)+1 := by
   let P := (n*n+(n+2*L)*n)+L+n+1
   let rows := gsMatrix (finitePrefix A k hk)
   have hr := gsMatrix_prefix_rep (embed B) hb A hA k hk
   have hc := gsMatrix_prefix_canonical (embed B) hb A hA hcan k hk
   have hvrow : ∀ row∈rows,volume row≤ n*(14*(P+2)+1)+1 := by
     intro row hrow
     obtain ⟨v,hv,hrep⟩ := forall2_left_exists hr row hrow
     obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
     have hw := represents_gs_word_bound B hb hB _ row hrep (hc row hrow)
     have hvol := volume_list_le row (14*(P+2)) hw
     rw [represents_length hrep] at hvol
     exact hvol
   have hvol := volume_list_le rows (n*(14*(P+2)+1)+1) hvrow
   have hlen : rows.length=k := by simp [rows,gsMatrix_length,finitePrefix]
   rw [hlen] at hvol
   exact hvol.trans (by dsimp [P]; gcongr)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialFoldClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

 theorem polynomial_fold_clock {f : α×β → β} {R : Realizer f}
     (hR : PolyBound R) (E r : ℕ) :
     ∃ D e : ℕ, 0< D ∧ ∀ (xs : List α) (b : β) (z : ℕ),
       volume (xs,b)+1≤ z →
       (∀ j,j≤ xs.length → volume ((xs.take j).foldl (fun b a => f (a,b)) b)≤ E*z^r) →
       R.fold.time (xs,b)≤ D*z^e ∧ volume (xs.foldl (fun b a => f (a,b)) b)≤ D*z^e := by
   obtain ⟨C,q,hC,hR⟩ := hR
   let F := C*(E+3)^q
   let u := (r+1)*q
   let e := u+r+2
   refine ⟨F+100*E+200,e,by dsimp [F]; positivity,?_⟩
   intro xs b z hinput hv
   have hz : 1≤ z := by omega
   have hlen : xs.length≤ z := by have hh:=length_volume xs; simp only [volume_pair] at hinput; omega
   have hxs : volume xs≤ z := by simp only [volume_pair] at hinput; omega
   have hzr : z≤ z^(r+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ r+1)
   have hrr : z^r≤ z^(r+1) := Nat.pow_le_pow_right hz (by omega)
   have hone : 1≤ z^(r+1) := one_le_pow₀ hz
   have ht (j : ℕ) (hj : j< xs.length) : R.time (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)≤ F*z^u := by
     have ha := volume_mem_le (List.getElem_mem hj)
     have hb := hv j hj.le
     have hbase : volume (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)+1≤(E+3)*z^(r+1) := by
       simp only [volume_pair]
       nlinarith
     have hh := ((hR _).1).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
     simpa only [F,u,mul_pow,← pow_mul,Nat.mul_assoc] using hh
   have hh := fold_prefix_bound R xs b (F*z^u) (E*z^r) hv ht
   have hcopy : volume xs+2*(E*z^r)+1≤(2*E+2)*z^(r+1) := by nlinarith
   have hm := Nat.mul_le_mul hlen (Nat.add_le_add_left (Nat.mul_le_mul_left 20 hcopy) (F*z^u))
   have heq : z*(F*z^u+20*((2*E+2)*z^(r+1)))=
       F*z^(u+1)+(40*E+40)*z^(r+2) := by simp only [pow_succ]; ring
   rw [heq] at hm
   have hp1 : z^(u+1)≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hp2 : z^(r+2)≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hpr : z^r≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hp : z≤ z^e := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by dsimp [e]; omega : 1≤ e)
   have htime := Nat.mul_le_mul_left F hp1
   have hcopies := Nat.mul_le_mul_left (40*E+40) hp2
   constructor
   · rw [Realizer.time_fold]
     change 2*volume (xs,b)+6+Realizer.foldTime R b xs≤(F+100*E+200)*z^e
     nlinarith only [hh,hm,htime,hcopies,hp,hinput,hz]
   · change volume (xs.foldl (fun b a => f (a,b)) b)≤ _
     have hv' := hv xs.length le_rfl
     rw [List.take_length] at hv'
     have hout := hv'.trans (Nat.mul_le_mul_left E hpr)
     exact hout.trans (Nat.mul_le_mul_right _ (show E≤ F+100*E+200 by omega))
end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.GramSchmidtClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 theorem finitePrefix_take {α : Type} {n : ℕ} (A : Fin n → α) (j : ℕ) (hj : j≤ n) :
     (List.ofFn A).take j=finitePrefix A j hj := by
   apply List.ext_getElem
   · simp [finitePrefix,List.length_take,Nat.min_eq_left hj]
   · intro k hk hk'
     simp only [List.getElem_take,List.getElem_ofFn,finitePrefix]

 theorem gs_state_numeric (n L z : ℕ) (hz : 1≤ z) (hn : n≤ z) (hL : L≤ z) :
     n*(n*(14*(((n*n+(n+2*L)*n)+L+n+1)+2)+1)+2)+1≤200*z^4 := by
   have hn2 := Nat.mul_le_mul hn hn
   have hLn := Nat.mul_le_mul hL hn
   have hzz : z≤ z^2 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤2)
   have hP : (n*n+(n+2*L)*n)+L+n+1≤8*z^2 := by nlinarith
   have hcoef : 14*(((n*n+(n+2*L)*n)+L+n+1)+2)+1≤141*z^2 := by nlinarith
   calc
     _≤ z*(z*(141*z^2)+2)+1 := by gcongr
     _=141*z^4+2*z+1 := by ring
     _≤200*z^4 := by
       have hp : z≤ z^4 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤4)
       have h1 : 1≤ z^4 := one_le_pow₀ hz
       omega

 theorem gsMatrix_prefix_budget {n L : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hb : LinearIndependent ℝ (embed B)) (hB : ∀ i j, |B i j|≤(2:ℤ)^L)
     (A : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (embed B i))
     (hcan : ∀ i,VectorCanonical (A i)) (z : ℕ) (hz : 1≤ z) (hn : n≤ z) (hL : L≤ z) :
     ∀ j,j≤(List.ofFn A).length →
       volume (((List.ofFn A).take j).foldl (fun gs b => gsAppend (b,gs)) [])≤200*z^4 := by
   intro j hj
   have hjn : j≤ n := by simpa using hj
   rw [finitePrefix_take A j hjn]
   exact (gsMatrix_prefix_volume B hb hB A hA hcan j hjn).trans (gs_state_numeric n L z hz hn hL)

 theorem gsMatrix_polynomial_time :
     ∃ C q : ℕ,0< C ∧ ∀ (n L : ℕ) (B : Matrix (Fin n) (Fin n) ℤ),
       LinearIndependent ℝ (embed B) → (∀ i j, |B i j|≤(2:ℤ)^L) →
       ∀ (A : Fin n → SignedVector), (∀ i,RepresentsVector (A i) (embed B i)) →
       (∀ i,VectorCanonical (A i)) →
       gsMatrixRealizer.time (List.ofFn A)≤ C*(volume (List.ofFn A)+n+L+4)^q ∧
       volume (gsMatrix (List.ofFn A))≤ C*(volume (List.ofFn A)+n+L+4)^q := by
   obtain ⟨D,e,hD,hfold⟩ := polynomial_fold_clock gsAppend_polynomial 200 4
   let pre : Realizer (fun bs : List SignedVector => (bs,([] : List SignedVector))) :=
     Realizer.id.pair (Realizer.constant [])
   have hpreLinear : Linear pre := by
     apply linear_pair
     · exact linear_id
     · exact linear_constant ([] : List SignedVector)
   obtain ⟨F,hF,hpreBounds⟩ := hpreLinear
   refine ⟨D+20*F+100,e+1,by omega,?_⟩
   intro n L B hb hB A hA hcan
   let z := volume (List.ofFn A)+n+L+4
   have hz : 1≤ z := by dsimp [z]; omega
   have hn : n≤ z := by dsimp [z]; omega
   have hL : L≤ z := by dsimp [z]; omega
   have hin : volume (List.ofFn A,([] : List SignedVector))+1≤ z := by
     simp only [volume_pair,volume_nil]
     dsimp [z]
     omega
   have hh := hfold (List.ofFn A) [] z hin (gsMatrix_prefix_budget B hb hB A hA hcan z hz hn hL)
   have hpre : pre.time (List.ofFn A)≤ F*z := by
     have h:=(hpreBounds (List.ofFn A)).1
     exact h.trans (Nat.mul_le_mul_left F (by dsimp [z]; omega))
   have hp : z^e≤ z^(e+1) := Nat.pow_le_pow_right hz (by omega)
   have hpz : z≤ z^(e+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ e+1)
   change gsMatrixRealizer.time (List.ofFn A)≤(D+20*F+100)*z^(e+1) ∧
     volume (gsMatrix (List.ofFn A))≤(D+20*F+100)*z^(e+1)
   constructor
   · change (pre.comp gsAppendRealizer.fold).time (List.ofFn A)≤ _
     rw [Realizer.time_comp]
     have htime := Nat.mul_le_mul_left D hp
     have hcopy := Nat.mul_le_mul_left (20*F+100) hpz
     nlinarith [hh.1]
   · exact hh.2.trans ((Nat.mul_le_mul_left D hp).trans
       (Nat.mul_le_mul_right _ (show D≤ D+20*F+100 by omega)))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLSizeStepCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 theorem nearestIntegerCode_polynomial : PolyBound nearestIntegerCodeRealizer :=
   polynomial_comp signedNearest_polynomial
     (linear_polynomial (linear_pair linear_fst (linear_pair linear_snd (linear_constant [true]))))
 theorem nearestIntegerCode_denpos (s : SignedWords) : 0< value (nearestIntegerCode s).2.2 := by change 0< value [true]; decide
 theorem nearestIntegerCode_value (s : SignedWords) :
     signedFractionValue (nearestIntegerCode s)=(signedValue (signedNearest s).1 (signedNearest s).2:ℚ) := by
   simp [signedFractionValue,nearestIntegerCode,value]

 
 
 
 
 theorem sizeRowI_polynomial : PolyBound sizeRowI := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) (linear_comp linear_fst linear_fst))) (lookupList_polynomial [])
 theorem sizeRowJ_polynomial : PolyBound sizeRowJ := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) (linear_comp linear_fst linear_snd))) (lookupList_polynomial [])
 theorem sizeGsJ_polynomial : PolyBound sizeGsJ := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp linear_snd linear_snd) (linear_comp linear_fst linear_snd))) (lookupList_polynomial [])
 
 
 theorem sizeCoefficient_polynomial : PolyBound sizeCoefficientRealizer :=
   polynomial_comp (polynomial_pair sizeRowI_polynomial sizeGsJ_polynomial) gsCoefficient_polynomial
 
 
 theorem sizeInteger_polynomial : PolyBound sizeIntegerRealizer :=
   polynomial_comp sizeCoefficient_polynomial nearestIntegerCode_polynomial
 
 
 theorem sizeNewRow_polynomial : PolyBound sizeNewRowRealizer :=
   polynomial_comp (polynomial_pair sizeRowI_polynomial
     (polynomial_comp (polynomial_pair sizeRowJ_polynomial sizeInteger_polynomial) vectorScale_polynomial)) vectorSub_polynomial
 
 
 theorem sizeStep_polynomial : PolyBound sizeStepRealizer := polynomial_pair
   (polynomial_comp (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_fst))
     (polynomial_pair (linear_polynomial (linear_comp linear_fst linear_fst)) sizeNewRow_polynomial)) (replaceList_polynomial []))
   (linear_polynomial (linear_comp linear_snd linear_snd))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLSizeStepSemantics
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 theorem lookup_ofFn_default {α : Type} {n : ℕ} (A : Fin n → α) (i : Fin n) (a : α) :
     ((List.ofFn A).drop i.val).headD a=A i := by
   rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem (by simpa using i.isLt)]
   simp

 theorem coefficient_represents {n : ℕ} {A B : SignedVector} {v w : Vec n}
     (hA : RepresentsVector A v) (hB : RepresentsVector B w) (hw : w≠0) :
     0< value (gsCoefficient (A,B)).2.2 ∧
       (signedFractionValue (gsCoefficient (A,B)):ℝ)=inner ℝ v w/inner ℝ w w := by
   have hdot := represents_dot hA hB
   have hnorm := represents_dot hB hB
   have hnorm0 : inner ℝ w w≠0 := by
     rw [real_inner_self_eq_norm_sq]
     exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
   have hn : 0< value (signedDot (B,B)).2.1 :=
     signed_num_positive_of_nonzero _ (by intro hz; rw [hz,Rat.cast_zero] at hnorm; exact hnorm0 hnorm.2.symm)
   refine ⟨canonicalDiv_denpos _ _ hdot.1 hn,?_⟩
   change (signedFractionValue (canonicalDiv (signedDot (A,B),signedDot (B,B))):ℝ)=_
   rw [canonicalDiv_value _ _ hdot.1 hn,Rat.cast_div,hdot.2,hnorm.2]

 theorem sizeStep_correct {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
     (A C : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (b i))
     (hC : ∀ i,RepresentsVector (C i) (gs b i)) (hcan : ∀ i,VectorCanonical (A i))
     (i j : Fin n) :
     ∃ (r : ℤ) (A' : Fin n → SignedVector), IsNearestInt r (mu b i j) ∧
       sizeStep ((i.val,j.val),(List.ofFn A,List.ofFn C))=(List.ofFn A',List.ofFn C) ∧
       (∀ k,RepresentsVector (A' k) (reduceBy b i j r k)) ∧
       (∀ k,VectorCanonical (A' k)) := by
   let s : SizeStepInput := ((i.val,j.val),(List.ofFn A,List.ofFn C))
   have hcoef : sizeCoefficient s=gsCoefficient (A i,C j) := by
     dsimp only [sizeCoefficient,s]
     rw [lookup_ofFn_default,lookup_ofFn_default]
   have hc := coefficient_represents (hA i) (hC j) (InnerProductSpace.gramSchmidt_ne_zero j hb)
   have hcvalue : (signedFractionValue (sizeCoefficient s):ℝ)=mu b i j := by
     rw [hcoef,hc.2]
     rfl
   have hcden : 0< value (sizeCoefficient s).2.2 := by rw [hcoef]; exact hc.1
   let r := signedValue (signedNearest (sizeCoefficient s)).1 (signedNearest (sizeCoefficient s)).2
   have hnear : IsNearestInt r (mu b i j) := by
     have hq := signedNearest_error (sizeCoefficient s) hcden
     have hq' : |signedFractionValue (sizeCoefficient s)-(r:ℚ)|≤(1/2:ℚ) := hq
     have hr : |(signedFractionValue (sizeCoefficient s):ℝ)-(r:ℝ)|≤(1/2:ℝ) := by
       have hh : ((|signedFractionValue (sizeCoefficient s)-(r:ℚ)|:ℚ):ℝ)≤((1/2:ℚ):ℝ) := by exact_mod_cast hq'
       simpa only [Rat.cast_abs,Rat.cast_sub,Rat.cast_intCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh
     rwa [hcvalue] at hr
   have hrvalue : (signedFractionValue (sizeInteger s):ℝ)=(r:ℝ) := by
     change (signedFractionValue (nearestIntegerCode (sizeCoefficient s)):ℝ)=_
     rw [nearestIntegerCode_value,Rat.cast_intCast]
   have hrden : 0< value (sizeInteger s).2.2 := nearestIntegerCode_denpos _
   have hscl := represents_scale (hA j) (sizeInteger s) hrden
   rw [hrvalue] at hscl
   have hrow : sizeNewRow s=vectorSub (A i,vectorScale (A j,sizeInteger s)) := by
     dsimp only [sizeNewRow,s]
     rw [lookup_ofFn_default,lookup_ofFn_default]
   have hnew : RepresentsVector (sizeNewRow s) (b i-(r:ℝ) • b j) := by
     rw [hrow]
     exact represents_sub (hA i) hscl
   have hnewcan : VectorCanonical (sizeNewRow s) := by
     rw [hrow]
     exact vectorSub_canonical (hA i) hscl
   let A' := Function.update A i (sizeNewRow s)
   refine ⟨r,A',hnear,?_,?_,?_⟩
   · change (replaceList [] (List.ofFn A,(i.val,sizeNewRow s)),List.ofFn C)=_
     rw [replaceList_ofFn]
   · intro k
     by_cases hk : k=i
     · subst k
       simpa only [A',reduceBy,Function.update_self] using hnew
     · simpa only [A',reduceBy,Function.update_of_ne hk] using hA k
   · intro k
     by_cases hk : k=i
     · subst k
       simpa only [A',Function.update_self] using hnewcan
     · simpa only [A',Function.update_of_ne hk] using hcan k

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLReductionBasis
noncomputable section

set_option backward.isDefEq.respectTransparency false
open LLLFactor.Reduction LLLFactor.RedBasis
namespace EdgeSublinearMWIS.Main.LLLBounds
theorem reduce_li {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
    (κ l : Fin n) (hne : κ ≠ l) (r : ℤ) : LinearIndependent ℝ (reduceBy b κ l r) := by
  apply hb.update κ (b κ - (r : ℝ) • b l)
  refine ⟨1, by simp, Finsupp.single κ 1 - Finsupp.single l (r : ℝ), ?_, ?_⟩
  · simp [hne]
  · simp

theorem reduce_le {n : ℕ} (b : Fin n → Vec n) (κ l : Fin n) (r : ℤ) :
    latticeOf (reduceBy b κ l r) ≤ latticeOf b := by
  apply Submodule.span_le.mpr
  rintro v ⟨i, rfl⟩
  by_cases hi : i = κ
  · subst i
    simp only [reduceBy, Function.update_self]
    apply Submodule.sub_mem
    · exact Submodule.subset_span ⟨κ, rfl⟩
    · have h := (latticeOf b).smul_mem r (Submodule.subset_span (Set.mem_range_self l))
      simpa only [Int.cast_smul_eq_zsmul] using h
  · simpa [reduceBy, latticeOf, Function.update_of_ne hi] using
      (Submodule.subset_span (Set.mem_range_self i) : b i ∈ latticeOf b)

theorem reduce_lat {n : ℕ} (b : Fin n → Vec n) (κ l : Fin n) (hne : κ ≠ l) (r : ℤ) :
    latticeOf (reduceBy b κ l r) = latticeOf b := by
  apply le_antisymm (reduce_le b κ l r)
  have hinv : reduceBy (reduceBy b κ l r) κ l (-r) = b := by
    funext i
    by_cases hi : i = κ
    · subst i
      simp [reduceBy, Function.update_of_ne hne.symm]
    · simp [reduceBy, Function.update_of_ne hi]
  have h := reduce_le (reduceBy b κ l r) κ l (-r)
  rwa [hinv] at h


end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLRowReduction
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds



 theorem row_basis {n : ℕ} {i : Fin n} {m : ℕ} {b c : Fin n → Vec n}
     (h : RowReduction i m b c) (hb : LinearIndependent ℝ b) :
     LinearIndependent ℝ c ∧ latticeOf c=latticeOf b := by
   induction h with
   | zero b => exact ⟨hb,rfl⟩
   | succ m hm b c r near next ih =>
     have hne : i≠(⟨m,by omega⟩:Fin n) := by intro h; have:=congrArg Fin.val h; simp at this; omega
     have hc := ih (reduce_li b hb _ _ hne r)
     exact ⟨hc.1,hc.2.trans (reduce_lat b _ _ hne r)⟩

 theorem row_gs {n : ℕ} {i : Fin n} {m : ℕ} {b c : Fin n → Vec n}
     (h : RowReduction i m b c) : ∀ j, gs c j=gs b j := by
   induction h with
   | zero b => intro j; rfl
   | succ m hm b c r near next ih =>
     intro j
     exact (ih j).trans (GS.gs_reduceBy b i _ hm r j)

 theorem row_other {n : ℕ} {i : Fin n} {m : ℕ} {b c : Fin n → Vec n}
     (h : RowReduction i m b c) : ∀ j, j≠i → c j=b j := by
   induction h with
   | zero b => intro j hj; rfl
   | succ m hm b c r near next ih =>
     intro j hj
     exact (ih j hj).trans (GS.reduceBy_ne b i _ r j hj)

 theorem row_mu_other {n : ℕ} {i : Fin n} {m : ℕ} {b c : Fin n → Vec n}
     (h : RowReduction i m b c) (j k : Fin n) (hj : j≠i) : mu c j k=mu b j k := by
   simp only [mu,row_other h j hj,row_gs h k]

 theorem row_integral {n : ℕ} {i : Fin n} {m : ℕ} {b c : Fin n → Vec n}
     (h : RowReduction i m b c) (hb : IntegralRows b) : IntegralRows c := by
   induction h with
   | zero b => exact hb
   | succ m hm b c r near next ih => exact ih (integral_reduce hb _ _ r)

 theorem row_mu {n : ℕ} {i : Fin n} {m : ℕ} {b c : Fin n → Vec n}
     (h : RowReduction i m b c) (hb : LinearIndependent ℝ b) :
     (∀ j : Fin n, j.val< m → |mu c i j|≤(1/2:ℝ)) ∧
     (∀ j : Fin n, m≤ j.val → mu c i j=mu b i j) := by
   induction h with
   | zero b => exact ⟨fun j hj => by omega,fun j hj => rfl⟩
   | succ m hm b c r near next ih =>
     let l : Fin n := ⟨m,by omega⟩
     have hli : l< i := hm
     have hne : i≠l := hli.ne'
     have hbr : LinearIndependent ℝ (reduceBy b i l r) := reduce_li b hb i l hne r
     have hc := ih hbr
     have hself : mu b l l=1 := GS.mu_self b l (InnerProductSpace.gramSchmidt_ne_zero l hb)
     constructor
     · intro j hj
       by_cases hjm : j.val< m
       · exact hc.1 j hjm
       · have hjl : j=l := Fin.ext (by dsimp [l]; omega)
         subst j
         rw [hc.2 l (by dsimp [l]; omega),GS.mu_reduceBy b i l hli r i l,if_pos rfl,hself,mul_one]
         exact near
     · intro j hj
       rw [hc.2 j (by omega),GS.mu_reduceBy b i l hli r i j,if_pos rfl,
         GS.mu_zero_of_lt b (show l< j by change m< j.val; omega),mul_zero,sub_zero]

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLRowCode
noncomputable section

open scoped Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 
 
 
 theorem rowPairs_polynomial : PolyBound rowPairsRealizer :=
   polynomial_comp (polynomial_pair
     (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) range_polynomial) reverse_polynomial_generic)
     (linear_polynomial linear_snd))
     (polynomial_mapEnvironment (linear_polynomial (linear_pair linear_snd linear_fst)))
 
 
 
 theorem rowCode_succ (m i : ℕ) (st : WordBasisState) :
     rowCode (m+1,(i,st))=rowCode (m,(i,sizeStep ((i,m),st))) := by
   simp [rowCode,rowPairs,List.range_succ,List.reverse_append]

 theorem rowCode_correct {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
     (A C : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (b i))
     (hC : ∀ i,RepresentsVector (C i) (gs b i)) (hcan : ∀ i,VectorCanonical (A i))
     (i : Fin n) (m : ℕ) (hm : m≤ i.val) :
     ∃ (c : Fin n → Vec n) (A' : Fin n → SignedVector), RowReduction i m b c ∧
       rowCode (m,(i.val,(List.ofFn A,List.ofFn C)))=(List.ofFn A',List.ofFn C) ∧
       (∀ k,RepresentsVector (A' k) (c k)) ∧ (∀ k,VectorCanonical (A' k)) := by
   induction m generalizing b A with
   | zero => exact ⟨b,A,.zero b,rfl,hA,hcan⟩
   | succ m ih =>
     let j : Fin n := ⟨m,by omega⟩
     have hji : j< i := by change m< i.val; omega
     obtain ⟨r,A1,hnear,hstep,hA1,hcan1⟩ := sizeStep_correct b hb A C hA hC hcan i j
     have hb1 := reduce_li b hb i j hji.ne' r
     have hC1 : ∀ k,RepresentsVector (C k) (gs (reduceBy b i j r) k) := by
       intro k
       rw [GS.gs_reduceBy b i j hji r k]
       exact hC k
     obtain ⟨c,A',hrow,hexec,hA',hcan'⟩ := ih (reduceBy b i j r) hb1 A1 hA1 hC1 hcan1 (by omega)
     refine ⟨c,A',.succ m (by omega) b c r hnear hrow,?_,hA',hcan'⟩
     rw [rowCode_succ,hstep]
     exact hexec

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLSizePass
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 



 theorem pass_basis {n : ℕ} {m : ℕ} {b c : Fin n → Vec n}
     (h : SizePass m b c) (hb : LinearIndependent ℝ b) :
     LinearIndependent ℝ c ∧ latticeOf c=latticeOf b := by
   induction h with
   | zero b => exact ⟨hb,rfl⟩
   | succ m hm b c d prior row ih =>
     have hc := ih hb
     have hd := row_basis row hc.1
     exact ⟨hd.1,hd.2.trans hc.2⟩

 theorem pass_gs {n : ℕ} {m : ℕ} {b c : Fin n → Vec n}
     (h : SizePass m b c) : ∀ j, gs c j=gs b j := by
   induction h with
   | zero b => intro j; rfl
   | succ m hm b c d prior row ih => intro j; exact (row_gs row j).trans (ih j)

 theorem pass_integral {n : ℕ} {m : ℕ} {b c : Fin n → Vec n}
     (h : SizePass m b c) (hb : IntegralRows b) : IntegralRows c := by
   induction h with
   | zero b => exact hb
   | succ m hm b c d prior row ih => exact row_integral row (ih hb)

 theorem pass_mu {n : ℕ} {m : ℕ} {b c : Fin n → Vec n}
     (h : SizePass m b c) (hb : LinearIndependent ℝ b) :
     ∀ i j : Fin n, i.val< m → j< i → |mu c i j|≤(1/2:ℝ) := by
   induction h with
   | zero b => intro i j hi hj; omega
   | succ m hm b c d prior row ih =>
     intro i j hi hj
     by_cases him : i.val< m
     · have hne : i≠(⟨m,hm⟩:Fin n) := by intro he; have:=congrArg Fin.val he; simp at this; omega
       rw [row_mu_other row i j hne]
       exact ih hb i j him hj
     · have he : i=(⟨m,hm⟩:Fin n) := Fin.ext (by change i.val=m; omega)
       subst i
       exact (row_mu row (pass_basis prior hb).1).1 j hj

 

 theorem pass_gram {n : ℕ} {m : ℕ} {b c : Fin n → Vec n}
     (h : SizePass m b c) (hb : LinearIndependent ℝ b) (j : ℕ) (hj : j≤ n) :
     LLLFactor.Reduction.gram c j=LLLFactor.Reduction.gram b j := by
   rw [((gram_eq_prod_gs c (pass_basis h hb).1).1 j hj).1,
       ((gram_eq_prod_gs b hb).1 j hj).1]
   apply Finset.prod_congr rfl
   intro k hk
   rw [pass_gs h]

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLFullPassCode
noncomputable section

open scoped Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 
 
 
 
 
 theorem fullSizeCode_succ (m : ℕ) (st : WordBasisState) :
     fullSizeCode (m+1,st)=rowCode (m,(m,fullSizeCode (m,st))) := by
   simp [fullSizeCode,List.range_succ,List.foldl_append,rowIteration]

 theorem fullSizeCode_correct {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
     (A C : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (b i))
     (hC : ∀ i,RepresentsVector (C i) (gs b i)) (hcan : ∀ i,VectorCanonical (A i))
     (m : ℕ) (hm : m≤ n) :
     ∃ (c : Fin n → Vec n) (A' : Fin n → SignedVector), SizePass m b c ∧
       fullSizeCode (m,(List.ofFn A,List.ofFn C))=(List.ofFn A',List.ofFn C) ∧
       (∀ k,RepresentsVector (A' k) (c k)) ∧ (∀ k,VectorCanonical (A' k)) := by
   induction m with
   | zero => exact ⟨b,A,.zero b,rfl,hA,hcan⟩
   | succ m ih =>
     obtain ⟨c,A1,hpass,hprefix,hA1,hcan1⟩ := ih (by omega)
     have hc := (pass_basis hpass hb).1
     have hC1 : ∀ k,RepresentsVector (C k) (gs c k) := by
       intro k
       rw [pass_gs hpass k]
       exact hC k
     obtain ⟨d,A',hrow,hrowexec,hA',hcan'⟩ := rowCode_correct c hc A1 C hA1 hC1 hcan1 ⟨m,by omega⟩ m le_rfl
     refine ⟨d,A',.succ m (by omega) b c d hpass hrow,?_,hA',hcan'⟩
     rw [fullSizeCode_succ,hprefix]
     exact hrowexec

 
 
 
 

 theorem forall2_ofFn_left {α β : Type} {R : α → β → Prop} {n : ℕ}
     (xs : List α) (f : Fin n → β) (h : List.Forall₂ R xs (List.ofFn f)) :
     ∃ A : Fin n → α, xs=List.ofFn A ∧ ∀ i,R (A i) (f i) := by
   have hlen : xs.length=n := by simpa using h.length_eq
   let A : Fin n → α := fun i => xs.get ⟨i.val,by rw [hlen]; exact i.isLt⟩
   refine ⟨A,?_,?_⟩
   · apply List.ext_getElem
     · simp [hlen]
     · intro i hi hj
       simp only [List.getElem_ofFn,A,List.get_eq_getElem]
   · intro i
     have hh := h.get (i:=i.val) (by rw [hlen]; exact i.isLt) (by simpa using i.isLt)
     simpa only [A,List.get_ofFn,Fin.cast_mk] using hh

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLovaszQueryCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 

 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLFindBadCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 

 
 
 

 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GenericListTake
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

 
 
 

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.MatrixBorderCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GLSCast
noncomputable section

namespace EdgeSublinearMWIS.Main.GLS.Cast

end EdgeSublinearMWIS.Main.GLS.Cast
end

-- Solutions.SignedMatrixSemantics
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open EdgeSublinearMWIS.Main.RealizerBounds

 
 

 

 

 

 

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.CanonicalVectorCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLFactor.RedBasis

 
 
 
 
 
 
 
 
 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.NaturalProductCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 

 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationBasisCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidScalarCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixInverseStepCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixInverseLoopCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RationalVectorTake
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixBorderSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open EdgeSublinearMWIS.Main.RealizerBounds

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BorderedInverse
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.InverseMath

 

 

 
 

 

 

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.BorderedPositive
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.InverseMath

 

 

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.RationalMatrixCast
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.InverseMath

 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.PrincipalMatrix
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.InverseMath

 
 
 
 
 
 

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.VectorPrefix
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLSwapCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
variable {α : Type} [Coding α]

 
 
 
 
 
 
 
 
 
 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLRoundCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLoopCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler

 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLovaszQueryMath
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 

end EdgeSublinearMWIS.Main.LLLBounds
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLFindBadMath
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 

 

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLReducedNormBound
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 theorem gram_succ_formula {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
     (m : ℕ) (hm : m+1≤ n) :
     LLLFactor.Reduction.gram b (m+1)=LLLFactor.Reduction.gram b m*‖gs b ⟨m,by omega⟩‖^2 := by
   rw [((gram_eq_prod_gs b hb).1 (m+1) hm).1,
     ((gram_eq_prod_gs b hb).1 m (by omega)).1,Fin.prod_univ_castSucc]
   congr 1

 theorem gs_sq_upper {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hb : LinearIndependent ℝ (embed B)) (R : ℝ)
     (hR : ∀ i≤ n, LLLFactor.Reduction.gram (embed B) i≤ R) (j : Fin n) :
     ‖gs (embed B) j‖^2≤ R := by
   have hg1 := gram_ge_one B hb j.val (by omega)
   have hg2 := hR (j.val+1) (by omega)
   rw [gram_succ_formula (embed B) hb j.val (by omega)] at hg2
   have hn : 0≤‖gs (embed B) j‖^2 := sq_nonneg _
   nlinarith

 theorem orthogonal_sum_norm {ι : Type} {n : ℕ} (s : Finset ι) (v : ι → Vec n)
     (h : ∀ i∈s, ∀ j∈s, i≠j → inner ℝ (v i) (v j)=0) :
     ‖∑ i∈s,v i‖^2=∑ i∈s,‖v i‖^2 := by
   rw [← real_inner_self_eq_norm_sq,sum_inner]
   apply Finset.sum_congr rfl
   intro i hi
   rw [inner_sum,Finset.sum_eq_single_of_mem i hi,real_inner_self_eq_norm_sq]
   intro j hj hji
   exact h i hi j hj hji.symm

 theorem norm_sq_decompose {n : ℕ} (b : Fin n → Vec n) (i : Fin n) :
     ‖b i‖^2=‖gs b i‖^2+∑ j∈Finset.Iio i, (mu b i j)^2*‖gs b j‖^2 := by
   rw [GS.b_eq b i,norm_add_sq_real]
   have horth : inner ℝ (gs b i) (∑ j∈Finset.Iio i, mu b i j • gs b j)=0 := by
     rw [inner_sum]
     apply Finset.sum_eq_zero
     intro j hj
     rw [real_inner_smul_right,GS.gs_orth b (Finset.mem_Iio.mp hj).ne',mul_zero]
   rw [horth,mul_zero,add_zero]
   congr 1
   rw [orthogonal_sum_norm]
   · apply Finset.sum_congr rfl
     intro j hj
     rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
   · intro j hj k hk hne
     rw [inner_smul_left,inner_smul_right,GS.gs_orth b hne]
     simp

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLFullSwap
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 

 

 

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLRoundMath
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 
 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLBoundedFullReduction
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds



 

 

 

 

 

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLSizeNormGrowth
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 theorem mu_from_gram_bounds {n : ℕ} (b : Fin n → Vec n)
     (hb : LinearIndependent ℝ b) (R : ℝ) (hR : 1≤ R)
     (hG : ∀ i≤ n,1≤ LLLFactor.Reduction.gram b i ∧ LLLFactor.Reduction.gram b i≤ R)
     (i j : Fin n) : |mu b i j|≤‖b i‖*(R+1)^2 := by
   have hg := gram_succ_formula b hb j.val (by omega)
   have hlo := (hG (j.val+1) (by omega)).1
   have hhi := (hG j.val (by omega)).2
   have hmul := mul_le_mul_of_nonneg_right hhi (sq_nonneg ‖gs b j‖)
   have hratio : 1≤ R*‖gs b j‖^2 := by rw [hg] at hlo; nlinarith
   have hs2 : ‖gs b j‖^2≤ R := by
     have hge := (hG j.val (by omega)).1
     have hcap := (hG (j.val+1) (by omega)).2
     rw [hg] at hcap
     nlinarith [sq_nonneg ‖gs b j‖]
   have hnorm : ‖gs b j‖≤ R+1 := by nlinarith [norm_nonneg (gs b j)]
   have hp : 0< inner ℝ (gs b j) (gs b j) := by
     rw [real_inner_self_eq_norm_sq]
     exact sq_pos_of_pos (norm_pos_iff.mpr (InnerProductSpace.gramSchmidt_ne_zero j hb))
   rw [mu,abs_div,abs_of_pos hp]
   apply (div_le_iff₀ hp).mpr
   rw [real_inner_self_eq_norm_sq]
   calc
     |inner ℝ (b i) (gs b j)|≤‖b i‖*‖gs b j‖ := abs_real_inner_le_norm _ _
     _≤‖b i‖*(R+1) := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
     _≤(‖b i‖*(R+1))*(R*‖gs b j‖^2) :=
       le_mul_of_one_le_right (by positivity) hratio
     _≤(‖b i‖*(R+1))*((R+1)*‖gs b j‖^2) := by gcongr <;> linarith
     _=‖b i‖*(R+1)^2*‖gs b j‖^2 := by ring

 theorem nearest_reduce_norm_bound {n : ℕ} (b : Fin n → Vec n) (i j : Fin n)
     (r : ℤ) (U S : ℝ) (hU : 0≤ U) (hS : 0≤ S)
     (hmu : |mu b i j|≤ U*‖b i‖) (hj : ‖b j‖≤ S)
     (hr : IsNearestInt r (mu b i j)) :
     ‖reduceBy b i j r i‖+1≤(‖b i‖+1)*(1+S*(U+1)) := by
   have hr' : |(r:ℝ)|≤ U*‖b i‖+1 := by
     have he : (r:ℝ)=mu b i j-(mu b i j-r) := by ring
     calc
       |(r:ℝ)|=|mu b i j-(mu b i j-r)| := congrArg abs he
       _≤|mu b i j|+|mu b i j-r| := abs_sub _ _
       _≤ U*‖b i‖+1 := by dsimp only [IsNearestInt] at hr; linarith
   rw [GS.reduceBy_self]
   have hnorm := norm_sub_le (b i) ((r:ℝ) • b j)
   rw [norm_smul,Real.norm_eq_abs] at hnorm
   have hmul : |(r:ℝ)| *‖b j‖≤(U*‖b i‖+1)*S :=
     mul_le_mul hr' hj (norm_nonneg _) (by positivity)
   have hdiff : 0≤ S*(U+‖b i‖) := by positivity
   nlinarith

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLPassNorm
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 theorem pass_other {n : ℕ} {m : ℕ} {b c : Fin n → Vec n}
     (h : SizePass m b c) : ∀ j,m≤ j.val → c j=b j := by
   induction h with
   | zero b => intro j hj; rfl
   | succ m hm b c d prior row ih =>
     intro j hj
     have hne : j≠(⟨m,hm⟩:Fin n) := by intro he; have:=congrArg Fin.val he; simp at this; omega
     rw [row_other row j hne,ih j (by omega)]

 theorem one_row_size_norm {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hb : LinearIndependent ℝ (embed B)) (R : ℝ) (hR : 0≤ R)
     (hG : ∀ k≤ n, LLLFactor.Reduction.gram (embed B) k≤ R) (i : Fin n)
     (hsmall : ∀ j< i,|mu (embed B) i j|≤(1/2:ℝ)) :
     ‖embed B i‖^2≤(n+1)*R := by
   rw [norm_sq_decompose]
   have hgs := gs_sq_upper B hb R hG i
   have hs : (∑ j∈Finset.Iio i, (mu (embed B) i j)^2*‖gs (embed B) j‖^2)≤ n*R := by
     calc
       _≤∑ _j∈Finset.Iio i,R := by
         apply Finset.sum_le_sum
         intro j hj
         have hm := hsmall j (Finset.mem_Iio.mp hj)
         have hma : (mu (embed B) i j)^2≤1 := by
           have hh := abs_le.mp hm
           nlinarith [sq_nonneg (mu (embed B) i j)]
         have hgj := gs_sq_upper B hb R hG j
         exact (mul_le_mul_of_nonneg_right hma (sq_nonneg _)).trans (by simpa using hgj)
       _=(Finset.Iio i).card*R := by simp
       _≤ n*R := mul_le_mul_of_nonneg_right (by
         exact_mod_cast (show (Finset.Iio i).card≤ n from by simpa using (Finset.card_le_card (Finset.subset_univ (Finset.Iio i))))) hR
   nlinarith

 theorem one_row_norm {n : ℕ} (b : Fin n → Vec n)
     (hb : LinearIndependent ℝ b) (hint : IntegralRows b) (R : ℝ) (hR : 1≤ R)
     (hG : ∀ k≤ n, LLLFactor.Reduction.gram b k≤ R) (i : Fin n)
     (hsmall : ∀ j< i,|mu b i j|≤(1/2:ℝ)) :
     ‖b i‖≤(n+1)*(R+1) := by
   obtain ⟨B,rfl⟩ := hint
   have hh := one_row_size_norm B hb R (by linarith) hG i hsmall
   let S : ℝ := (n+1)*(R+1)
   have hn : (1:ℝ)≤ n+1 := by have h0 : (0:ℝ)≤ n := Nat.cast_nonneg _; linarith
   have hS : 1≤ S := by dsimp [S]; nlinarith
   have hSR : (n+1:ℝ)*R≤ S := by dsimp [S]; nlinarith
   change ‖embed B i‖≤ S
   nlinarith [norm_nonneg (embed B i)]

 theorem pass_prefix_norm {n : ℕ} {m : ℕ} {b c : Fin n → Vec n}
     (h : SizePass m b c) (hb : LinearIndependent ℝ b) (hint : IntegralRows b)
     (R : ℝ) (hR : 1≤ R) (hG : ∀ k≤ n, LLLFactor.Reduction.gram b k≤ R)
     (hstart : ∀ i,‖b i‖≤(n+1)*(R+1)) :
     ∀ i,‖c i‖≤(n+1)*(R+1) := by
   intro i
   by_cases hi : i.val< m
   · have hGc : ∀ k≤ n, LLLFactor.Reduction.gram c k≤ R := by
       intro k hk
       rw [pass_gram h hb k hk]
       exact hG k hk
     exact one_row_norm c (pass_basis h hb).1 (pass_integral h hint) R hR hGc i
       (fun j hj => pass_mu h hb i j hi hj)
   · rw [pass_other h i (by omega)]
     exact hstart i

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLUniformTrace
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 

 

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLLoopInvariant
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 

 

 

end EdgeSublinearMWIS.Main.LLLBounds
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLoopCorrect
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

end EdgeSublinearMWIS.Main.LLLBounds
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLowerTrace
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 

 theorem lowerTrace_basis {n : ℕ} {i : Fin n} {b c : Fin n → Vec n} {t : ℕ}
     (h : LowerTrace i b t c) (hb : LinearIndependent ℝ b) :
     LinearIndependent ℝ c ∧ latticeOf c=latticeOf b := by
   induction h with
   | zero => exact ⟨hb,rfl⟩
   | succ prior j hj r near ih =>
     exact ⟨reduce_li _ ih.1 i j hj.ne' r,(reduce_lat _ i j hj.ne' r).trans ih.2⟩

 theorem lowerTrace_gs {n : ℕ} {i : Fin n} {b c : Fin n → Vec n} {t : ℕ}
     (h : LowerTrace i b t c) : ∀ k,gs c k=gs b k := by
   induction h with
   | zero => intro k; rfl
   | succ prior j hj r near ih => intro k; rw [GS.gs_reduceBy _ i j hj r,ih]

 theorem lowerTrace_gram {n : ℕ} {i : Fin n} {b c : Fin n → Vec n} {t : ℕ}
     (h : LowerTrace i b t c) (hb : LinearIndependent ℝ b) (k : ℕ) (hk : k≤ n) :
     LLLFactor.Reduction.gram c k=LLLFactor.Reduction.gram b k := by
   rw [((gram_eq_prod_gs c (lowerTrace_basis h hb).1).1 k hk).1,
     ((gram_eq_prod_gs b hb).1 k hk).1]
   apply Finset.prod_congr rfl
   intro a ha
   rw [lowerTrace_gs h]

 theorem lowerTrace_other {n : ℕ} {i : Fin n} {b c : Fin n → Vec n} {t : ℕ}
     (h : LowerTrace i b t c) : ∀ k,k≠i → c k=b k := by
   induction h with
   | zero => intro k hk; rfl
   | succ prior j hj r near ih => intro k hk; rw [GS.reduceBy_ne _ i j r k hk,ih k hk]

 theorem lowerTrace_integral {n : ℕ} {i : Fin n} {b c : Fin n → Vec n} {t : ℕ}
     (h : LowerTrace i b t c) (hb : IntegralRows b) : IntegralRows c := by
   induction h with
   | zero => exact hb
   | succ prior j hj r near ih => exact integral_reduce ih i j r

 theorem lowerTrace_norm {n : ℕ} {i : Fin n} {b c : Fin n → Vec n} {t : ℕ}
     (h : LowerTrace i b t c) (hb : LinearIndependent ℝ b) (R S : ℝ)
     (hR : 1≤ R) (hS : 0≤ S)
     (hG : ∀ k≤ n,1≤ LLLFactor.Reduction.gram b k ∧ LLLFactor.Reduction.gram b k≤ R)
     (hsmall : ∀ j< i,‖b j‖≤ S) :
     ‖c i‖+1≤(‖b i‖+1)*(1+S*((R+1)^2+1))^t := by
   induction h with
   | zero => simp
   | @succ t c prior j hj r near ih =>
     have hc := (lowerTrace_basis prior hb).1
     have hG' : ∀ k≤ n,1≤ LLLFactor.Reduction.gram c k ∧ LLLFactor.Reduction.gram c k≤ R := by
       intro k hk
       rw [lowerTrace_gram prior hb k hk]
       exact hG k hk
     have hmu := mu_from_gram_bounds c hc R hR hG' i j
     have hnormj : ‖c j‖≤ S := by rw [lowerTrace_other prior j hj.ne]; exact hsmall j hj
     have hone := nearest_reduce_norm_bound c i j r ((R+1)^2) S (sq_nonneg _) hS
       (by simpa only [mul_comm] using hmu) hnormj near
     have hF : 0≤1+S*((R+1)^2+1) := by positivity
     calc
       _≤(‖c i‖+1)*(1+S*((R+1)^2+1)) := hone
       _≤((‖b i‖+1)*(1+S*((R+1)^2+1))^t)*(1+S*((R+1)^2+1)) :=
         mul_le_mul_of_nonneg_right ih hF
       _=_ := by rw [pow_succ]; ring

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLBitGrowthPower
noncomputable section

open scoped Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 theorem two_pow_add_one (H : ℕ) : (2:ℝ)^H+1≤(2:ℝ)^(H+1) := by
   have h : (1:ℝ)≤2^H := one_le_pow₀ (by norm_num)
   rw [pow_succ]
   linarith

 theorem size_constant_bound (n H : ℕ) :
     (n+1:ℝ)*((2:ℝ)^H+1)≤(2:ℝ)^(H+n+2) := by
   have hn : (n+1:ℝ)≤(2:ℝ)^(n+1) := by exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self : n+1<2^(n+1))
   have hR := two_pow_add_one H
   calc
     _≤(2:ℝ)^(n+1)*(2:ℝ)^(H+1) := mul_le_mul hn hR (by positivity) (by positivity)
     _=(2:ℝ)^(H+n+2) := by rw [← pow_add]; congr 1 <;> omega

 theorem size_constant_plus_bound (n H : ℕ) :
     (n+1:ℝ)*((2:ℝ)^H+1)+1≤(2:ℝ)^(H+n+3) := by
   have hs := size_constant_bound n H
   have h2 := two_pow_add_one (H+n+2)
   have he : (H+n+2)+1=H+n+3 := by omega
   rw [he] at h2
   linarith

 theorem reduction_factor_bound (n H : ℕ) :
     1+((n+1:ℝ)*((2:ℝ)^H+1))*(((2:ℝ)^H+1)^2+1)≤(2:ℝ)^(3*H+n+6) := by
   have hs := size_constant_bound n H
   have hR := two_pow_add_one H
   have hU : ((2:ℝ)^H+1)^2+1≤(2:ℝ)^(2*H+3) := by
     have hh := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2^H+1) hR 2
     have he : ((2:ℝ)^(H+1))^2=(2:ℝ)^(2*H+2) := by rw [← pow_mul]; congr 1 <;> omega
     rw [he] at hh
     have hd := two_pow_add_one (2*H+2)
     have he2 : (2*H+2)+1=2*H+3 := by omega
     rw [he2] at hd
     linarith
   have hprod : ((n+1:ℝ)*((2:ℝ)^H+1))*(((2:ℝ)^H+1)^2+1)≤(2:ℝ)^(3*H+n+5) := by
     calc
       _≤(2:ℝ)^(H+n+2)*(2:ℝ)^(2*H+3) := mul_le_mul hs hU (by positivity) (by positivity)
       _=_ := by rw [← pow_add]; congr 1 <;> omega
   have hdup := two_pow_add_one (3*H+n+5)
   linarith

 theorem row_growth_power_bound (n H t : ℕ) (ht : t≤ n) :
     (((n+1:ℝ)*((2:ℝ)^H+1))+1)*
       (1+((n+1:ℝ)*((2:ℝ)^H+1))*(((2:ℝ)^H+1)^2+1))^t≤
         (2:ℝ)^(intermediateExponent n H) := by
   have hF : (1:ℝ)≤1+((n+1:ℝ)*((2:ℝ)^H+1))*(((2:ℝ)^H+1)^2+1) := by
     have h0 : (0:ℝ)≤((n+1:ℝ)*((2:ℝ)^H+1))*(((2:ℝ)^H+1)^2+1) := by positivity
     linarith
   have hp := pow_le_pow_right₀ hF ht
   have hbound := reduction_factor_bound n H
   calc
     _≤(((n+1:ℝ)*((2:ℝ)^H+1))+1)*
       (1+((n+1:ℝ)*((2:ℝ)^H+1))*(((2:ℝ)^H+1)^2+1))^n := mul_le_mul_of_nonneg_left hp (by positivity)
     _≤(2:ℝ)^(H+n+3)*((2:ℝ)^(3*H+n+6))^n :=
       mul_le_mul (size_constant_plus_bound n H) (pow_le_pow_left₀ (by positivity) hbound n) (by positivity) (by positivity)
     _=_ := by rw [← pow_mul,← pow_add]; congr 1; dsimp [intermediateExponent]; ring

 theorem lowerTrace_norm_power {n H t : ℕ} {i : Fin n} {b c : Fin n → Vec n}
     (h : LowerTrace i b t c) (hb : LinearIndependent ℝ b) (ht : t≤ n)
     (hG : ∀ k≤ n,1≤ LLLFactor.Reduction.gram b k ∧ LLLFactor.Reduction.gram b k≤(2:ℝ)^H)
     (hstart : ∀ j,‖b j‖≤(n+1)*((2:ℝ)^H+1)) :
     ∀ j,‖c j‖≤(2:ℝ)^(intermediateExponent n H) := by
   let R : ℝ := 2^H
   let S : ℝ := (n+1)*(R+1)
   have hR : 1≤ R := one_le_pow₀ (by norm_num)
   have hn := lowerTrace_norm h hb R S hR (by dsimp [S]; positivity) hG (fun j hj => hstart j)
   have hF : 0≤1+S*((R+1)^2+1) := by positivity
   have hstarti := hstart i
   intro j
   by_cases hj : j=i
   · subst j
     have hm : (‖b i‖+1)*(1+S*((R+1)^2+1))^t≤(S+1)*(1+S*((R+1)^2+1))^t :=
       mul_le_mul_of_nonneg_right (by linarith : ‖b i‖+1≤ S+1) (pow_nonneg hF t)
     exact (show ‖c i‖≤‖c i‖+1 by linarith).trans (hn.trans (hm.trans (row_growth_power_bound n H t ht)))
   · rw [lowerTrace_other h j hj]
     exact (hstart j).trans ((show S≤ S+1 by linarith).trans
       ((size_constant_plus_bound n H).trans (pow_le_pow_right₀ (by norm_num) (by dsimp [intermediateExponent]; omega))))

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLPassInitializeClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 theorem sizePassInitialize_polynomial_time :
     ∃ C q : ℕ,0< C ∧ ∀ (n H : ℕ) (b : Fin n → Vec n),
       LinearIndependent ℝ b → IntegralRows b →
       (∀ j,‖b j‖≤(n+1)*((2:ℝ)^H+1)) → ∀ (A : Fin n → SignedVector),
       (∀ k,RepresentsVector (A k) (b k)) → (∀ k,VectorCanonical (A k)) →
       sizePassInitializeRealizer.time (List.ofFn A)≤ C*(volume (List.ofFn A)+n+H+4)^q ∧
       volume (sizePassInitialize (List.ofFn A))≤ C*(volume (List.ofFn A)+n+H+4)^q := by
   obtain ⟨C,q,hC,hgs⟩ := gsMatrix_polynomial_time
   obtain ⟨D,p,hD,hlen⟩ := (listLength_polynomial (α:=SignedVector))
   let F := C*2^q
   let e := p+q+2
   refine ⟨D+50*F+1000,e,by positivity,?_⟩
   intro n H b hb hint hstart A hA hcan
   obtain ⟨B,rfl⟩ := hint
   let z := volume (List.ofFn A)+n+H+4
   have hz : 1≤ z := by dsimp [z]; omega
   have hn : n≤ z := by dsimp [z]; omega
   have hvol : volume (List.ofFn A)≤ z := by dsimp [z]; omega
   have hinput : volume (List.ofFn A)+1≤ z := by dsimp [z]; omega
   have hB : ∀ i j,|B i j|≤(2:ℤ)^(H+n+2) := by
     intro i j
     have hcoord := PiLp.norm_apply_le (embed B i) j
     have he : ‖embed B i j‖=|(B i j:ℝ)| := by simp [embed,Real.norm_eq_abs]
     rw [he] at hcoord
     have hh := hcoord.trans ((hstart i).trans (size_constant_bound n H))
     exact_mod_cast hh
   have hgsclock := hgs n (H+n+2) B hb hB A hA hcan
   have hbase : volume (List.ofFn A)+n+(H+n+2)+4≤2*z := by dsimp [z]; omega
   have hgtime : gsMatrixRealizer.time (List.ofFn A)≤ F*z^q := by
     exact (hgsclock.1.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))).trans_eq (by dsimp [F]; rw [mul_pow]; ring)
   have hgvol : volume (gsMatrix (List.ofFn A))≤ F*z^q := by
     exact (hgsclock.2.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))).trans_eq (by dsimp [F]; rw [mul_pow]; ring)
   have hltime := (hlen (List.ofFn A)).1.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hinput p))
   have hp : z^p≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hq : z^q≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hze : z≤ z^e := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by dsimp [e]; omega : 1≤ e)
   have h1 : 1≤ z^e := one_le_pow₀ hz
   have hdp := Nat.mul_le_mul_left D hp
   have hfq := Nat.mul_le_mul_left F hq
   have hbig := Nat.mul_le_mul_left 1000 hze
   change sizePassInitializeRealizer.time (List.ofFn A)≤(D+50*F+1000)*z^e ∧
     volume (sizePassInitialize (List.ofFn A))≤(D+50*F+1000)*z^e
   constructor
   · unfold sizePassInitializeRealizer
     rw [Realizer.time_pair,Realizer.time_pair]
     simp only [Realizer.time_id,id_eq,List.length_ofFn,volume_pair,volume_nat]
     nlinarith
   · simp only [sizePassInitialize,List.length_ofFn,volume_pair,volume_nat]
     nlinarith

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLowerWordTrace
noncomputable section

open scoped Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 theorem lowerTrace_trans {n : ℕ} {i : Fin n} {a b c : Fin n → Vec n} {t u : ℕ}
     (h1 : LowerTrace i a t b) (h2 : LowerTrace i b u c) : LowerTrace i a (t+u) c := by
   induction h2 with
   | zero => simpa using h1
   | succ prior j hj r near ih => simpa only [Nat.add_assoc] using LowerTrace.succ ih j hj r near

end EdgeSublinearMWIS.Main.LLLBounds
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 theorem lowerWordsFold_correct {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
     (A C : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (b i))
     (hC : ∀ i,RepresentsVector (C i) (gs b i)) (hcan : ∀ i,VectorCanonical (A i))
     (i : Fin n) (js : List ℕ) (hjs : ∀ j∈js,j< i.val) :
     ∃ (c : Fin n → Vec n) (A' : Fin n → SignedVector), LowerTrace i b js.length c ∧
       ((js.map (fun j => (i.val,j))).foldl (fun st ij => sizeStep (ij,st))
         (List.ofFn A,List.ofFn C))=(List.ofFn A',List.ofFn C) ∧
       (∀ k,RepresentsVector (A' k) (c k)) ∧ (∀ k,VectorCanonical (A' k)) := by
   induction js generalizing b A with
   | nil => exact ⟨b,A,.zero,rfl,hA,hcan⟩
   | cons j js ih =>
     have hji : j< i.val := hjs j (by simp)
     let jf : Fin n := ⟨j,by omega⟩
     have hjf : jf< i := hji
     obtain ⟨r,A1,hnear,hstep,hA1,hcan1⟩ := sizeStep_correct b hb A C hA hC hcan i jf
     have hb1 := reduce_li b hb i jf hjf.ne' r
     have hC1 : ∀ k,RepresentsVector (C k) (gs (reduceBy b i jf r) k) := by
       intro k
       rw [GS.gs_reduceBy b i jf hjf r k]
       exact hC k
     obtain ⟨c,A',htrace,hexec,hA',hcan'⟩ := ih (reduceBy b i jf r) hb1 A1 hA1 hC1 hcan1
       (fun k hk => hjs k (by simp [hk]))
     have hfirst : LowerTrace i b 1 (reduceBy b i jf r) := .succ .zero jf hjf r hnear
     have htr := lowerTrace_trans hfirst htrace
     refine ⟨c,A',?_,?_,hA',hcan'⟩
     · simpa only [List.length_cons,Nat.add_comm] using htr
     · rw [List.map_cons,List.foldl_cons,hstep]
       exact hexec

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.IntegerBasisWordBounds
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 theorem integer_row_word_bound {n J : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n)
     (hnorm : ‖embed B i‖≤(2:ℝ)^J) (A : SignedVector)
     (hA : RepresentsVector A (embed B i)) (hcan : VectorCanonical A) :
     ∀ s∈A,volume s≤14*(J+2) := by
   obtain ⟨a,rfl,ha,hv⟩ := hA
   intro s hs
   obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hs
   have hq : signedFractionValue (a k)=(B i k:ℚ) := by
     apply Rat.cast_injective (α:=ℝ)
     simpa only [Rat.cast_intCast,embed,WithLp.ofLp_toLp] using hv k
   have hcoord : |(B i k:ℝ)|≤(2:ℝ)^J := by
     have hh := PiLp.norm_apply_le (embed B i) k
     have he : ‖embed B i k‖=|(B i k:ℝ)| := by simp [embed,Real.norm_eq_abs]
     rw [he] at hh
     exact hh.trans hnorm
   have hnum : (B i k).natAbs≤2^J := by
     have he : ((B i k).natAbs:ℝ)=|(B i k:ℝ)| := by
       rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
     rw [← he] at hcoord
     exact_mod_cast hcoord
   have hden : 1≤2^J := Nat.one_le_pow _ _ (by omega)
   have hw := signedCanonical_width (a k) (hcan _ (List.mem_ofFn.mpr ⟨k,rfl⟩)) (ha k) J
     (by simpa only [hq,Rat.num_intCast] using hnum)
     (by simpa only [hq,Rat.den_intCast] using hden)
   exact (signedVolume_width (a k)).trans (Nat.mul_le_mul_left 14 hw)

 theorem integer_matrix_word_volume {n J : ℕ} (b : Fin n → Vec n)
     (hint : IntegralRows b) (hnorm : ∀ i,‖b i‖≤(2:ℝ)^J)
     (A : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (b i))
     (hcan : ∀ i,VectorCanonical (A i)) :
     volume (List.ofFn A)≤ n*(n*(14*(J+2)+1)+2)+1 := by
   obtain ⟨B,rfl⟩ := hint
   have hrow : ∀ i,volume (A i)≤ n*(14*(J+2)+1)+1 := by
     intro i
     have h := volume_list_le (A i) (14*(J+2)) (integer_row_word_bound B i (hnorm i) (A i) (hA i) (hcan i))
     rw [represents_length (hA i)] at h
     exact h
   have h := volume_list_le (List.ofFn A) (n*(14*(J+2)+1)+1) (by
     intro a ha
     obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
     exact hrow i)
   simpa using h

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLRowWordBudget
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 theorem rowCode_prefix_volume {n H : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
     (hint : IntegralRows b)
     (hG : ∀ k≤ n,1≤ LLLFactor.Reduction.gram b k ∧ LLLFactor.Reduction.gram b k≤(2:ℝ)^H)
     (hstart : ∀ j,‖b j‖≤(n+1)*((2:ℝ)^H+1))
     (A C : Fin n → SignedVector) (hA : ∀ k,RepresentsVector (A k) (b k))
     (hC : ∀ k,RepresentsVector (C k) (gs b k)) (hcan : ∀ k,VectorCanonical (A k))
     (i : Fin n) (m : ℕ) (hm : m≤ i.val) :
     ∀ j,j≤(rowPairs (m,i.val)).length →
       volume (((rowPairs (m,i.val)).take j).foldl (fun st ij => sizeStep (ij,st))
         (List.ofFn A,List.ofFn C))≤
       (n*(n*(14*(intermediateExponent n H+2)+1)+2)+1)+volume (List.ofFn C)+1 := by
   intro j hj
   let js := ((List.range m).reverse).take j
   have hjs : ∀ k∈js,k< i.val := by
     intro k hk
     have hk' : k∈(List.range m).reverse := List.mem_of_mem_take hk
     have hk'' : k< m := List.mem_range.mp (List.mem_reverse.mp hk')
     omega
   obtain ⟨c,A',htrace,hexec,hA',hcan'⟩ := lowerWordsFold_correct b hb A C hA hC hcan i js hjs
   have hlen : js.length≤ n := by
     have hh : js.length≤ m := by simp [js]
     omega
   have hnorm := lowerTrace_norm_power htrace hb hlen hG hstart
   have hvol := integer_matrix_word_volume c (lowerTrace_integral htrace hint) hnorm A' hA' hcan'
   have hpair : (rowPairs (m,i.val)).take j=js.map (fun k => (i.val,k)) := by
     simp only [rowPairs,List.map_take,js]
   rw [hpair,hexec,volume_pair]
   omega

 theorem intermediate_matrix_numeric (n H z : ℕ) (hz : 1≤ z) (hn : n≤ z) (hH : H≤ z) :
     n*(n*(14*(intermediateExponent n H+2)+1)+2)+1≤300*z^4 := by
   have hn2 := Nat.mul_le_mul hn hn
   have hHn := Nat.mul_le_mul hH hn
   have hzz : z≤ z^2 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤2)
   have hJ : intermediateExponent n H+2≤17*z^2 := by dsimp [intermediateExponent]; nlinarith
   have hcoef : 14*(intermediateExponent n H+2)+1≤239*z^2 := by nlinarith
   calc
     _≤ z*(z*(239*z^2)+2)+1 := by gcongr
     _=239*z^4+2*z+1 := by ring
     _≤300*z^4 := by
       have hp : z≤ z^4 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤4)
       have h1 : 1≤ z^4 := one_le_pow₀ hz
       omega

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLFullPassBudget
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 theorem fullSize_prefix_correct {n m : ℕ} (hm : m≤ n) (b : Fin n → Vec n)
     (hb : LinearIndependent ℝ b) (A C : Fin n → SignedVector)
     (hA : ∀ k,RepresentsVector (A k) (b k)) (hC : ∀ k,RepresentsVector (C k) (gs b k))
     (hcan : ∀ k,VectorCanonical (A k)) (j : ℕ) (hj : j≤ m) :
     ∃ c A', SizePass j b c ∧
       (((List.range m).take j).foldl (fun st i => rowIteration (i,st))
         (List.ofFn A,List.ofFn C))=(List.ofFn A',List.ofFn C) ∧
       (∀ k,RepresentsVector (A' k) (c k)) ∧ (∀ k,VectorCanonical (A' k)) := by
   obtain ⟨c,A',hpass,hexec,hA',hcan'⟩ := fullSizeCode_correct b hb A C hA hC hcan j (by omega)
   refine ⟨c,A',hpass,?_,hA',hcan'⟩
   rw [List.take_range,Nat.min_eq_left hj]
   exact hexec

 theorem fullSize_prefix_volume {n m H : ℕ} (hm : m≤ n) (b : Fin n → Vec n)
     (hb : LinearIndependent ℝ b) (hint : IntegralRows b)
     (hG : ∀ k≤ n,LLLFactor.Reduction.gram b k≤(2:ℝ)^H)
     (hstart : ∀ j,‖b j‖≤(n+1)*((2:ℝ)^H+1))
     (A C : Fin n → SignedVector) (hA : ∀ k,RepresentsVector (A k) (b k))
     (hC : ∀ k,RepresentsVector (C k) (gs b k)) (hcan : ∀ k,VectorCanonical (A k)) :
     ∀ j,j≤ m →
       volume (((List.range m).take j).foldl (fun st i => rowIteration (i,st))
         (List.ofFn A,List.ofFn C))≤
       (n*(n*(14*(intermediateExponent n H+2)+1)+2)+1)+volume (List.ofFn C)+1 := by
   intro j hj
   obtain ⟨c,A',hpass,hexec,hA',hcan'⟩ := fullSize_prefix_correct hm b hb A C hA hC hcan j hj
   have hn := pass_prefix_norm hpass hb hint (2^H) (one_le_pow₀ (by norm_num)) hG hstart
   have hnorm : ∀ k,‖c k‖≤(2:ℝ)^(intermediateExponent n H) := by
     intro k
     exact (hn k).trans ((size_constant_bound n H).trans
       (pow_le_pow_right₀ (by norm_num) (by dsimp [intermediateExponent]; omega)))
   have hvol := integer_matrix_word_volume c (pass_integral hpass hint) hnorm A' hA' hcan'
   rw [hexec,volume_pair]
   omega

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialComposedFoldClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 theorem polynomial_composed_fold_clock {pre : α → List β×γ} {step : β×γ → γ}
     {R : Realizer pre} {S : Realizer step} (hR : PolyBound R) (hS : PolyBound S) (E r : ℕ) :
     ∃ D e : ℕ,0< D ∧ ∀ (a : α) (z : ℕ),volume a+1≤ z →
       (∀ j,j≤(pre a).1.length → volume (((pre a).1.take j).foldl (fun b x => step (x,b)) (pre a).2)≤ E*z^r) →
       (R.comp S.fold).time a≤ D*z^e ∧
       volume ((pre a).1.foldl (fun b x => step (x,b)) (pre a).2)≤ D*z^e := by
   obtain ⟨C,p,hC,hR⟩ := hR
   obtain ⟨F,q,hF,hfold⟩ := polynomial_fold_clock hS E r
   let K := F*(C+1)^q
   let e := (p+1)*(q+1)+1
   refine ⟨K+20*C+20,e,by dsimp [K]; positivity,?_⟩
   intro a z hin hv
   have hz : 1≤ z := by omega
   have hp := (hR a).1.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hin p))
   have hvol := (hR a).2.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hin p))
   let W := (C+1)*z^(p+1)
   have hpow : z^p≤ z^(p+1) := Nat.pow_le_pow_right hz (by omega)
   have hone : 1≤ z^(p+1) := one_le_pow₀ hz
   have hzw : z≤ W := by
     have hh : z≤ z^(p+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ p+1)
     dsimp [W]
     nlinarith
   have hinput : volume (pre a)+1≤ W := by dsimp [W]; nlinarith
   have hv' : ∀ j,j≤(pre a).1.length → volume (((pre a).1.take j).foldl (fun b x => step (x,b)) (pre a).2)≤ E*W^r := by
     intro j hj
     exact (hv j hj).trans (Nat.mul_le_mul_left E (Nat.pow_le_pow_left hzw r))
   have hf := hfold (pre a).1 (pre a).2 W hinput hv'
   have heq : F*W^q=K*z^((p+1)*q) := by dsimp [W,K]; rw [mul_pow,← pow_mul]; ring
   rw [heq] at hf
   have hlow : z^((p+1)*q)≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; nlinarith)
   have hpp : z^p≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; nlinarith)
   have h1 : 1≤ z^e := one_le_pow₀ hz
   have hkt := Nat.mul_le_mul_left K hlow
   have hct := Nat.mul_le_mul_left (20*C+20) hpp
   constructor
   · rw [Realizer.time_comp]
     have hfoldtime : S.fold.time (pre a)≤ K*z^((p+1)*q) := hf.1
     nlinarith
   · exact hf.2.trans ((Nat.mul_le_mul_left K hlow).trans
       (Nat.mul_le_mul_right _ (show K≤ K+20*C+20 by omega)))
end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.LLLRowClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 theorem rowCode_polynomial_time :
     ∃ C q : ℕ,0< C ∧ ∀ (n H : ℕ) (b : Fin n → Vec n),
       LinearIndependent ℝ b → IntegralRows b →
       (∀ k≤ n,1≤ LLLFactor.Reduction.gram b k ∧ LLLFactor.Reduction.gram b k≤(2:ℝ)^H) →
       (∀ j,‖b j‖≤(n+1)*((2:ℝ)^H+1)) →
       ∀ (A G : Fin n → SignedVector),
       (∀ k,RepresentsVector (A k) (b k)) → (∀ k,RepresentsVector (G k) (gs b k)) →
       (∀ k,VectorCanonical (A k)) → ∀ (i : Fin n) (m : ℕ),m≤ i.val →
       rowCodeRealizer.time (m,(i.val,(List.ofFn A,List.ofFn G)))≤
         C*(volume (m,(i.val,(List.ofFn A,List.ofFn G)))+n+H+1)^q ∧
       volume (rowCode (m,(i.val,(List.ofFn A,List.ofFn G))))≤
         C*(volume (m,(i.val,(List.ofFn A,List.ofFn G)))+n+H+1)^q := by
   let pre : Realizer (fun s : ℕ×(ℕ×WordBasisState) => (rowPairs (s.1,s.2.1),s.2.2)) :=
     (((Realizer.fst.pair (Realizer.snd.comp Realizer.fst)).comp rowPairsRealizer).pair
       (Realizer.snd.comp Realizer.snd))
   have hpre : PolyBound pre := polynomial_pair
     (polynomial_comp (linear_polynomial (linear_pair linear_fst (linear_comp linear_snd linear_fst))) rowPairs_polynomial)
     (linear_polynomial (linear_comp linear_snd linear_snd))
   obtain ⟨C,q,hC,hclock⟩ := polynomial_composed_fold_clock hpre sizeStep_polynomial 302 4
   refine ⟨C,q,hC,?_⟩
   intro n H b hb hint hG hstart A G hA hgs hcan i m hm
   let input := (m,(i.val,(List.ofFn A,List.ofFn G)))
   let z := volume input+n+H+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hn : n≤ z := by dsimp [z]; omega
   have hH : H≤ z := by dsimp [z]; omega
   have hgsV : volume (List.ofFn G)≤ z := by
     dsimp only [input,z]
     simp only [volume_pair,volume_nat]
     omega
   have hprefix := rowCode_prefix_volume b hb hint hG hstart A G hA hgs hcan i m hm
   have hnumeric := intermediate_matrix_numeric n H z hz hn hH
   have hz4 : z≤ z^4 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤4)
   have hone : 1≤ z^4 := one_le_pow₀ hz
   have hv : ∀ j,j≤(rowPairs (m,i.val)).length →
       volume (((rowPairs (m,i.val)).take j).foldl (fun st ij => sizeStep (ij,st))
         (List.ofFn A,List.ofFn G))≤302*z^4 := by
     intro j hj
     exact (hprefix j hj).trans (by nlinarith)
   exact hclock input z (by dsimp [z]; omega) hv

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLRowIterationClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 theorem rowIteration_polynomial_time :
     ∃ C q : ℕ,0< C ∧ ∀ (n H : ℕ) (b : Fin n → Vec n),
       LinearIndependent ℝ b → IntegralRows b →
       (∀ k≤ n,1≤ LLLFactor.Reduction.gram b k ∧ LLLFactor.Reduction.gram b k≤(2:ℝ)^H) →
       (∀ j,‖b j‖≤(n+1)*((2:ℝ)^H+1)) →
       ∀ (A G : Fin n → SignedVector),
       (∀ k,RepresentsVector (A k) (b k)) → (∀ k,RepresentsVector (G k) (gs b k)) →
       (∀ k,VectorCanonical (A k)) → ∀ i : Fin n,
       rowIterationRealizer.time (i.val,(List.ofFn A,List.ofFn G))≤
         C*(volume (i.val,(List.ofFn A,List.ofFn G))+n+H+4)^q ∧
       volume (rowIteration (i.val,(List.ofFn A,List.ofFn G)))≤
         C*(volume (i.val,(List.ofFn A,List.ofFn G))+n+H+4)^q := by
   obtain ⟨C,q,hC,hrow⟩ := rowCode_polynomial_time
   let pre : Realizer (fun s : ℕ×WordBasisState => (s.1,(s.1,s.2))) :=
     Realizer.fst.pair (Realizer.fst.pair Realizer.snd)
   have hpreL : Linear pre := by
     apply linear_pair
     · exact linear_fst
     · exact linear_pair linear_fst linear_snd
   obtain ⟨F,hF,hpre⟩ := hpreL
   let D := C*3^q
   refine ⟨D+F+100,q+1,by dsimp [D]; positivity,?_⟩
   intro n H b hb hint hG hstart A G hA hgs hcan i
   let input := (i.val,(List.ofFn A,List.ofFn G))
   let output := (i.val,(i.val,(List.ofFn A,List.ofFn G)))
   let z := volume input+n+H+4
   have hz : 1≤ z := by dsimp [z]; omega
   have hin : volume input+1≤ z := by dsimp [z]; omega
   have hbase : volume output+n+H+1≤3*z := by
     dsimp [input,output,z]
     simp only [volume_pair,volume_nat]
     omega
   have hvo : volume output+1≤3*z := by omega
   have hh := hrow n H b hb hint hG hstart A G hA hgs hcan i i.val le_rfl
   have htime : rowCodeRealizer.time output≤ D*z^q := by
     exact (hh.1.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))).trans_eq (by dsimp [D]; rw [mul_pow]; ring)
   have hout : volume (rowCode output)≤ D*z^q := by
     exact (hh.2.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))).trans_eq (by dsimp [D]; rw [mul_pow]; ring)
   have hpt : pre.time input≤ F*z := ((hpre input).1).trans (Nat.mul_le_mul_left F hin)
   have hp : z^q≤ z^(q+1) := Nat.pow_le_pow_right hz (by omega)
   have hpz : z≤ z^(q+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+1)
   change rowIterationRealizer.time input≤(D+F+100)*z^(q+1) ∧
     volume (rowIteration input)≤(D+F+100)*z^(q+1)
   constructor
   · change (pre.comp rowCodeRealizer).time input≤ _
     rw [Realizer.time_comp]
     have hpow := Nat.mul_le_mul_left D hp
     have hlinear := Nat.mul_le_mul_left (F+100) hpz
     change pre.time input+rowCodeRealizer.time output+10*(volume output+1)≤ _
     nlinarith
   · exact hout.trans ((Nat.mul_le_mul_left D hp).trans
       (Nat.mul_le_mul_right _ (show D≤ D+F+100 by omega)))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FoldLocalClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

 theorem fold_local_clock {f : α×β → β} (R : Realizer f)
     (xs : List α) (b : β) (z E r F s G t : ℕ) (hz : 1≤ z)
     (hin : volume (xs,b)+1≤ E*z^r)
     (hv : ∀ j,j≤ xs.length → volume ((xs.take j).foldl (fun b a => f (a,b)) b)≤ F*z^s)
     (ht : ∀ j (hj : j< xs.length), R.time (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)≤ G*z^t) :
     R.fold.time (xs,b)≤(E*(G+20*E+40*F+20)+2*E+F+10)*z^(2*r+s+t+2) ∧
     volume (xs.foldl (fun b a => f (a,b)) b)≤(E*(G+20*E+40*F+20)+2*E+F+10)*z^(2*r+s+t+2) := by
   let u := r+s+t+1
   let e := 2*r+s+t+2
   let K := G+20*E+40*F+20
   have hr : z^r≤ z^u := Nat.pow_le_pow_right hz (by dsimp [u]; omega)
   have hs : z^s≤ z^u := Nat.pow_le_pow_right hz (by dsimp [u]; omega)
   have htp : z^t≤ z^u := Nat.pow_le_pow_right hz (by dsimp [u]; omega)
   have h1 : 1≤ z^u := one_le_pow₀ hz
   have hx : volume xs≤ E*z^r := by simp only [volume_pair] at hin; omega
   have hlen : xs.length≤ E*z^r := (length_volume xs).trans hx
   have hinside : G*z^t+20*(volume xs+2*(F*z^s)+1)≤ K*z^u := by
     have hrr := Nat.mul_le_mul_left E hr
     have hss := Nat.mul_le_mul_left F hs
     have htt := Nat.mul_le_mul_left G htp
     dsimp [K]
     nlinarith
   have hh := fold_prefix_bound R xs b (G*z^t) (F*z^s) hv ht
   have hm := Nat.mul_le_mul hlen hinside
   have heq : (E*z^r)*(K*z^u)=E*K*z^(r+u) := by rw [pow_add]; ring
   rw [heq] at hm
   have hpe : z^(r+u)≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e,u]; omega)
   have hbase : z^r≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hstate : z^s≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hconst : 1≤ z^e := one_le_pow₀ hz
   have hmain := Nat.mul_le_mul_left (E*K) hpe
   have hbt := Nat.mul_le_mul_left (2*E+10) hbase
   constructor
   · rw [Realizer.time_fold]
     change 2*volume (xs,b)+6+Realizer.foldTime R b xs≤ _
     dsimp [e,K] at *
     nlinarith
   · have hh := hv xs.length le_rfl
     rw [List.take_length] at hh
     exact hh.trans ((Nat.mul_le_mul_left F hstate).trans
       (Nat.mul_le_mul_right _ (by omega)))
end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.LLLFullSizeClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 theorem fullSizeCode_polynomial_time :
     ∃ C q : ℕ,0< C ∧ ∀ (n H : ℕ) (b : Fin n → Vec n),
       LinearIndependent ℝ b → IntegralRows b →
       (∀ k≤ n,1≤ LLLFactor.Reduction.gram b k ∧ LLLFactor.Reduction.gram b k≤(2:ℝ)^H) →
       (∀ j,‖b j‖≤(n+1)*((2:ℝ)^H+1)) →
       ∀ (A G : Fin n → SignedVector),
       (∀ k,RepresentsVector (A k) (b k)) → (∀ k,RepresentsVector (G k) (gs b k)) →
       (∀ k,VectorCanonical (A k)) → ∀ m : ℕ,m≤ n →
       fullSizeCodeRealizer.time (m,(List.ofFn A,List.ofFn G))≤
         C*(volume (m,(List.ofFn A,List.ofFn G))+n+H+4)^q ∧
       volume (fullSizeCode (m,(List.ofFn A,List.ofFn G)))≤
         C*(volume (m,(List.ofFn A,List.ofFn G))+n+H+4)^q := by
   obtain ⟨C,q,hC,hrow⟩ := rowIteration_polynomial_time
   let K := C*312^q
   let D := 8*(K+20*8+40*302+20)+2*8+302+10
   let e := 4*q+10
   let pre : Realizer (fun s : ℕ×WordBasisState => (List.range s.1,s.2)) :=
     (Realizer.fst.comp Realizer.range).pair Realizer.snd
   have hpre : PolyBound pre := by
     apply polynomial_pair
     · exact polynomial_comp (linear_polynomial linear_fst) range_polynomial
     · exact linear_polynomial linear_snd
   obtain ⟨F,p,hF,hpre⟩ := hpre
   refine ⟨D+F+1000,e+p+3,by dsimp [D]; positivity,?_⟩
   intro n H b hb hint hG hstart A G hA hgs hcan m hm
   let state : WordBasisState := (List.ofFn A,List.ofFn G)
   let input := (m,state)
   let z := volume input+n+H+4
   have hz : 1≤ z := by dsimp [z]; omega
   have hn : n≤ z := by dsimp [z]; omega
   have hH : H≤ z := by dsimp [z]; omega
   have hmz : m≤ z := hm.trans hn
   have hstate : volume state≤ z := by dsimp [state,input,z]; simp only [volume_pair,volume_nat]; omega
   have hgsV : volume (List.ofFn G)≤ z := by
     dsimp [state] at hstate
     simp only [volume_pair] at hstate
     omega
   have hz4 : z≤ z^4 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤4)
   have h1 : 1≤ z^4 := one_le_pow₀ hz
   have hV : ∀ j,j≤(List.range m).length →
       volume (((List.range m).take j).foldl (fun st i => rowIteration (i,st)) state)≤302*z^4 := by
     intro j hj
     have hjm : j≤ m := by simpa using hj
     have hp := fullSize_prefix_volume hm b hb hint (fun k hk => (hG k hk).2) hstart A G hA hgs hcan j hjm
     have hmatrix := intermediate_matrix_numeric n H z hz hn hH
     exact hp.trans (by nlinarith)
   have hT : ∀ j (hj : j<(List.range m).length),
       rowIterationRealizer.time ((List.range m)[j],
         ((List.range m).take j).foldl (fun st i => rowIteration (i,st)) state)≤ K*z^(4*q) := by
     intro j hj
     have hjm : j< m := by simpa using hj
     have hjn : j< n := lt_of_lt_of_le hjm hm
     obtain ⟨c,A1,hpass,hexec,hA1,hcan1⟩ := fullSize_prefix_correct hm b hb A G hA hgs hcan j hjm.le
     have hc := (pass_basis hpass hb).1
     have hcint := pass_integral hpass hint
     have hGc : ∀ k≤ n,1≤ LLLFactor.Reduction.gram c k ∧ LLLFactor.Reduction.gram c k≤(2:ℝ)^H := by
       intro k hk
       rw [pass_gram hpass hb k hk]
       exact hG k hk
     have hnorm := pass_prefix_norm hpass hb hint (2^H) (one_le_pow₀ (by norm_num)) (fun k hk => (hG k hk).2) hstart
     have hGSc : ∀ k,RepresentsVector (G k) (gs c k) := by intro k; rw [pass_gs hpass k]; exact hgs k
     have hclock := hrow n H c hc hcint hGc hnorm A1 G hA1 hGSc hcan1 ⟨j,hjn⟩
     have hv := hV j (by simpa using hjm.le)
     rw [hexec] at hv
     have hbase : volume (j,(List.ofFn A1,List.ofFn G))+n+H+4≤312*z^4 := by
       simp only [volume_pair,volume_nat] at hv ⊢
       nlinarith
     simp only [List.getElem_range]
     rw [hexec]
     have hh := hclock.1.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
     simpa only [K,mul_pow,← pow_mul,Nat.mul_assoc] using hh
   have hlist : volume (List.range m)≤5*z^2 := by
     have hh := volume_list_le (List.range m) (2*m+1) (by
       intro a ha
       have ha' : a< m := List.mem_range.mp ha
       simp only [volume_nat]
       omega)
     simp only [List.length_range] at hh
     have hm2 := Nat.pow_le_pow_left hmz 2
     have hzsq : z≤ z^2 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤2)
     have hzsq1 : 1≤ z^2 := one_le_pow₀ hz
     nlinarith
   have hin : volume (List.range m,state)+1≤8*z^2 := by
     have hz2 : z≤ z^2 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤2)
     simp only [volume_pair]
     nlinarith
   have hf := fold_local_clock rowIterationRealizer (List.range m) state z 8 2 302 4 K (4*q) hz hin hV hT
   have hf' : rowIterationRealizer.fold.time (List.range m,state)≤ D*z^e ∧
       volume (fullSizeCode input)≤ D*z^e := by simpa only [D,e,fullSizeCode,input,show 2*2+4+4*q+2=4*q+10 by omega] using hf
   have hinput : volume input+1≤ z := by dsimp [z]; omega
   have hp := (hpre input).1.trans (Nat.mul_le_mul_left F (Nat.pow_le_pow_left hinput p))
   have hpow1 : z^e≤ z^(e+p+3) := Nat.pow_le_pow_right hz (by omega)
   have hpow2 : z^p≤ z^(e+p+3) := Nat.pow_le_pow_right hz (by omega)
   have hpow3 : z^2≤ z^(e+p+3) := Nat.pow_le_pow_right hz (by omega)
   have hone : 1≤ z^(e+p+3) := one_le_pow₀ hz
   change fullSizeCodeRealizer.time input≤(D+F+1000)*z^(e+p+3) ∧
     volume (fullSizeCode input)≤(D+F+1000)*z^(e+p+3)
   constructor
   · change (pre.comp rowIterationRealizer.fold).time input≤ _
     rw [Realizer.time_comp]
     have hmain := Nat.mul_le_mul_left D hpow1
     have hpret := Nat.mul_le_mul_left F hpow2
     have hcopy := Nat.mul_le_mul_left 1000 hpow3
     change pre.time input+rowIterationRealizer.fold.time (List.range m,state)+10*(volume (List.range m,state)+1)≤ _
     nlinarith [hf'.1]
   · exact hf'.2.trans ((Nat.mul_le_mul_left D hpow1).trans
       (Nat.mul_le_mul_right _ (show D≤ D+F+1000 by omega)))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialPipelineClock
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RuntimeMath

 theorem polynomial_pipeline_clock (z A p B q u v t : ℕ) (hz : 1≤ z)
     (hu : u≤ A*z^p) (hv : v≤ A*z^p) (ht : t≤ B*(v+z)^q) :
     u+t+10*(v+1)≤(B*(A+1)^q+20*A+20)*z^(p+(p+1)*q+2) := by
   let e := p+(p+1)*q+2
   have hp : z^p≤ z^(p+1) := Nat.pow_le_pow_right hz (by omega)
   have hze : z≤ z^(p+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ p+1)
   have hbase : v+z≤(A+1)*z^(p+1) := by nlinarith
   have hpost := ht.trans (Nat.mul_le_mul_left B (Nat.pow_le_pow_left hbase q))
   have heq : B*((A+1)*z^(p+1))^q=B*(A+1)^q*z^((p+1)*q) := by rw [mul_pow,← pow_mul]; ring
   rw [heq] at hpost
   have hp1 : z^p≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hp2 : z^((p+1)*q)≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have h1 : 1≤ z^e := one_le_pow₀ hz
   have hpre := Nat.mul_le_mul_left (20*A+20) hp1
   have hpost2 := Nat.mul_le_mul_left (B*(A+1)^q) hp2
   change u+t+10*(v+1)≤(B*(A+1)^q+20*A+20)*z^e
   nlinarith

end EdgeSublinearMWIS.Main.RuntimeMath
end

-- Solutions.LLLSizePassClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 theorem sizePassCode_polynomial_time :
     ∃ C q : ℕ,0< C ∧ ∀ (n H : ℕ) (b : Fin n → Vec n),
       LinearIndependent ℝ b → IntegralRows b →
       (∀ k≤ n,1≤ LLLFactor.Reduction.gram b k ∧ LLLFactor.Reduction.gram b k≤(2:ℝ)^H) →
       (∀ j,‖b j‖≤(n+1)*((2:ℝ)^H+1)) → ∀ (A : Fin n → SignedVector),
       (∀ k,RepresentsVector (A k) (b k)) → (∀ k,VectorCanonical (A k)) →
       sizePassCodeRealizer.time (List.ofFn A)≤ C*(volume (List.ofFn A)+n+H+4)^q ∧
       volume (sizePassCode (List.ofFn A))≤ C*(volume (List.ofFn A)+n+H+4)^q := by
   obtain ⟨C,p,hC,hinit⟩ := sizePassInitialize_polynomial_time
   obtain ⟨D,q,hD,hfull⟩ := fullSizeCode_polynomial_time
   let F := D*(C+1)^q+20*C+20
   let e := p+(p+1)*q+2
   refine ⟨F,e,by dsimp [F]; positivity,?_⟩
   intro n H b hb hint hG hstart A hA hcan
   let xs := List.ofFn A
   let z := volume xs+n+H+4
   let v := volume (sizePassInitialize xs)
   have hz : 1≤ z := by dsimp [z]; omega
   have hparam : n+H+4≤ z := by dsimp [z]; omega
   obtain ⟨G,hGeq,hgs⟩ := forall2_ofFn_left (gsMatrix xs) (gs b) (gsMatrix_rep b hb A hA)
   have hinput : sizePassInitialize xs=(n,(xs,List.ofFn G)) := by
     simp only [sizePassInitialize,xs,List.length_ofFn,hGeq]
   have hh := hfull n H b hb hint hG hstart A G hA hgs hcan n le_rfl
   rw [← hinput] at hh
   have hi := hinit n H b hb hint hstart A hA hcan
   have hbase : volume (sizePassInitialize xs)+n+H+4≤ v+z := by dsimp [v]; omega
   have htime : fullSizeCodeRealizer.time (sizePassInitialize xs)≤ D*(v+z)^q :=
     hh.1.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hbase q))
   have hout : volume (fullSizeCode (sizePassInitialize xs))≤ D*(v+z)^q :=
     hh.2.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hbase q))
   have hpipeline := RuntimeMath.polynomial_pipeline_clock z C p D q
     (sizePassInitializeRealizer.time xs) v (fullSizeCodeRealizer.time (sizePassInitialize xs)) hz hi.1 hi.2 htime
   have hopipeline := RuntimeMath.polynomial_pipeline_clock z C p D q
     (sizePassInitializeRealizer.time xs) v (volume (fullSizeCode (sizePassInitialize xs))) hz hi.1 hi.2 hout
   change sizePassCodeRealizer.time xs≤ F*z^e ∧ volume (sizePassCode xs)≤ F*z^e
   constructor
   · unfold sizePassCodeRealizer
     rw [Realizer.time_comp]
     exact hpipeline
   · change volume (fullSizeCode (sizePassInitialize xs))≤ _
     dsimp [F,e] at *
     omega

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLRoundClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLBodyClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLoopClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLInitialInvariant
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 

 

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.StreamParserIteration
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]
 
 
 
 
 
 
end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.ProjectionSemantics
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open WeightedHelpers

 
 
 
 
 
 
 

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

 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SparsePathParser
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixRowsParser
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 

 
 
 
 
 
 

 

 

 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLBitProgramCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 
 
 
 
 
 
 
 
 
 
 

 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.IntegerMatrixEncoding
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 

 
 

 
 

 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixRowsParserMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLBitProgramMath
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 

 

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLDeterminantTrace
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RepresentedBasisUnique
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLReducedGramBound
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLFirstVectorBound
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLBitGram
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.IntegerBasisDeterminant
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.LLLBounds

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.DiophantineLattice
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 
 
 
 

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.ApproximationBasisSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 
 
 
 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidScalarSemantics
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedMatrixRoundingSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open EdgeSublinearMWIS.Main.RealizerBounds

 

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixInverseStepSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open InverseMath

 
 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixInverseLoopSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open InverseMath

 

 
 
 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GLSDeterminantBounds
noncomputable section
-- Adapted from EdouardBonnet/lax-109476, commit0a042604c7ae1ef4cd9a4c7d82eb902f313d4864.
-- Apache-2.0; original license retained in external-lp/LICENSE.

open scoped BigOperators Matrix

namespace EdgeSublinearMWIS.Main.GLS.DeterminantBounds





end EdgeSublinearMWIS.Main.GLS.DeterminantBounds
end

-- Solutions.IntegerMatrixInverseFormula
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.InverseMath

 

 

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.MatrixDenominatorBounds
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.InverseMath

 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.MatrixInverseHeight
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.InverseMath

 
 

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.MatrixInverseClockBounds
noncomputable section

open scoped Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds InverseMath

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixInverseClock
noncomputable section

open scoped Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds InverseMath

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ThinDirectionCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationModuliCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationModuliMath
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 
 
 
 
 
 
 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLBitProgramClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationPipelineCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialRestrictedComposition
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 

 

 

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.ApproximationPipelineMath
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 
 
 
 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationExtractCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.DiophantineWordAlgorithm
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.DiophantineWordClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationExtractSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationExtractInteger
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.DiophantineCoordinates
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.LLLBounds

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.DiophantineExtract
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.DiophantineNormBound
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.LLLBounds

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.DiophantineWordCorrect
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.CanonicalApproximation
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 

 
 
 
 
 

 

 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.HyperplaneApproximationCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidRecoveryCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.HyperplanePrecision
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.ConvexTools

 
 
 

end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.EllipsoidDyadicScalar
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidCutShapeCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GLSEllipsoidStep
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidStep.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-!
Internal lemmas for the ellipsoid algorithm. These establish the normalized
central-cut matrix update, containment, and determinant shrink factor. They do not yet
establish a rounded rational algorithm or a RAM runtime bound.
-/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidStep















open Matrix



















end EdgeSublinearMWIS.Main.GLS.EllipsoidStep
end

-- Solutions.GLSEllipsoidRounding
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidRounding.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-!
Internal shape-rounding lemmas. Entrywise rounding needs a diagonal enlargement:
entrywise inequalities alone do not imply containment of ellipsoids.
-/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidRounding

open Matrix





































end EdgeSublinearMWIS.Main.GLS.EllipsoidRounding
end

-- Solutions.GLSEllipsoidBounds
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidBounds.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-! Internal conditioning and precision bounds for general central-cut shapes. -/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidBounds

open Matrix EllipsoidRounding

































end EdgeSublinearMWIS.Main.GLS.EllipsoidBounds
end

-- Solutions.EllipsoidCutShapeSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixDiagonalCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidRoundedShapeCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 

 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GLSEllipsoidCenter
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidCenter.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-! Computable center updates and their error in the new ellipsoid's metric. -/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidCenter

open Matrix EllipsoidRounding EllipsoidBounds
open EdgeSublinearMWIS.Main.GLS.Cast





























end EdgeSublinearMWIS.Main.GLS.EllipsoidCenter
end

-- Solutions.EllipsoidRoundedShapeSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SqrtUpperMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 

 
 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedSqrtUpper
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidCenterCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidCenterSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidUpdateCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 

 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GLSEllipsoidPrecision
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidPrecision.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-! A uniform dyadic grid for both parts of the rational center update. -/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidPrecision

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter
open EdgeSublinearMWIS.Main.GLS.Cast

















end EdgeSublinearMWIS.Main.GLS.EllipsoidPrecision
end

-- Solutions.GLSEllipsoidDeterminant
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidDeterminant.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-! Determinant bounds from quadratic-form comparison, used for rounded updates. -/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidDeterminant

open Matrix EllipsoidRounding







end EdgeSublinearMWIS.Main.GLS.EllipsoidDeterminant
end

-- Solutions.GLSEllipsoidIteration
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidIteration.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-! Conditioning and determinant shrinkage of the same rational stored update. -/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidIteration

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision
open EllipsoidDeterminant EdgeSublinearMWIS.Main.GLS.Cast















end EdgeSublinearMWIS.Main.GLS.EllipsoidIteration
end

-- Solutions.GLSEllipsoidSequence
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidSequence.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-!
A concrete sequence of rational stored ellipsoids. The cut normals are supplied
externally; no LP separation, stopping rule, certificate recovery, or RAM execution
is asserted here.
-/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidSequence

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision EllipsoidIteration
open EdgeSublinearMWIS.Main.GLS.Cast



















end EdgeSublinearMWIS.Main.GLS.EllipsoidSequence
end

-- Solutions.EllipsoidUpdateSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidCanonicalUpdate
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidPhaseCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidBudgetCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
open ConvexTools GLS.EllipsoidSequence

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

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

 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.NonzeroCoordinateCode
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ListEraseCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

 
 
 
 
 

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.AffineEliminationCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RectangularMatrixSemantics
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open RealizerBounds

 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.AffineEliminationSemantics
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open RealizerBounds

 
 
 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.CanonicalAffineElimination
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleRecoveryParameters
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.AffineEvaluationCode
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 

 
 
 
 
 
 
 

 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RationalVectorClearing
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SelectiveChoose
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.ThreeMachine.StackCompiler
namespace Routine
open Tree
variable {f g : Data → Data} {c d : Data → ℕ}


end Routine
end OAI.ThreeMachine.StackCompiler

namespace OAI.ThreeMachine.StackCompiler.Realizer
variable {α β : Type} [Coding α] [Coding β]
 
 
end OAI.ThreeMachine.StackCompiler.Realizer
end

-- Solutions.OracleControlCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RectangularRowsParser
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PostprocessSemantics
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack

 

 

 

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
 
end EdgeSublinearMWIS.Main.RealizerBounds

namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
 
end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.ReadUnboundedNatural
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleTranscriptParserCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleOutputCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleTranscriptParserMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 

 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidPhaseMath
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open InverseMath GLS.EllipsoidSequence GLS.EllipsoidRounding GLS.Cast

 

 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidPrefixCongruence
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence

 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleCounterMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 
 
 
 
 
 
 
 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryHullHyperplane
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools

 

 

end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.OraclePhaseInvariant
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence GLS.Cast

 
 

 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleQuerySemantics
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.AffineCoordinateElimination
noncomputable section

open scoped Classical BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools

 
 
 

 
 

 
 

end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.AffineEliminationMath
noncomputable section

open scoped Classical BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools
open RawStack

 

 

 

end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.AffineIntegerHeight
noncomputable section

open scoped Classical BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.ConvexTools
open RawStack GLS.DeterminantBounds

 
 
 
 

end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.HyperplaneApproximationMath
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.HyperplaneCoefficientHeight
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools

 

 

end EdgeSublinearMWIS.Main.ConvexTools

namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.DiagonalMaximumMath
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 

 

 

 

 

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PositiveMatrixCauchy
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.EllipsoidMath

 

 

end EdgeSublinearMWIS.Main.EllipsoidMath
end

-- Solutions.PositiveMatrixEntryBound
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.EllipsoidMath

 

 

 

end EdgeSublinearMWIS.Main.EllipsoidMath
end

-- Solutions.EllipsoidThinDirection
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.EllipsoidMath

 
 

 
 

 

end EdgeSublinearMWIS.Main.EllipsoidMath
end

-- Solutions.GLSEllipsoidBall
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidBall.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

open scoped BigOperators Matrix

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidBall

open Matrix EllipsoidRounding EllipsoidDeterminant

variable {ι : Type} [Fintype ι] [DecidableEq ι]







end EdgeSublinearMWIS.Main.GLS.EllipsoidBall
end

-- Solutions.EllipsoidLargeInverseDiagonal
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.EllipsoidMath

 

end EdgeSublinearMWIS.Main.EllipsoidMath
end

-- Solutions.ThinDirectionMath
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open InverseMath EllipsoidMath

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GLSEllipsoidStateBounds
noncomputable section
-- Adapted from EdouardBonnet/lax-109476, commit 0a042604c7ae1ef4cd9a4c7d82eb902f313d4864.
-- Apache-2.0; original license retained in external-lp/LICENSE.

open scoped BigOperators

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize

open Matrix EllipsoidBounds EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence RationalRounding
open EdgeSublinearMWIS.Main.GLS.Cast

























end EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize
end

-- Solutions.EllipsoidSequenceHeight
noncomputable section

open scoped Classical BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize
open EllipsoidSequence EllipsoidRounding EllipsoidPrecision Cast

 
 

 

end EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize
end

-- Solutions.OracleCounterTermination
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleQueryBudget
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools

 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RecoveryUniformHeight
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open InverseMath EllipsoidMath ConvexTools

 
 
 
 
 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleCoreModel
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 
 
 

 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RecoveryParametersSemantics
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleModelElimination
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidRecoveryMath
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open InverseMath EllipsoidMath ConvexTools

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryScaledUnit
noncomputable section

open scoped Classical BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools

 

end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.EllipsoidPhaseRecovery
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open InverseMath EllipsoidMath ConvexTools GLS.EllipsoidSequence GLS.Cast GLS.EllipsoidRounding

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OraclePhaseHeight
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence GLS.EllipsoidStateSize

 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleBoundaryGeometry
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence ConvexTools

 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidHistoryAppend
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence GLS.Cast

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleModelPhaseAdvance
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence GLS.Cast

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleBigCutGeometry
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence GLS.Cast

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleCutGeometry
noncomputable section

open scoped Classical BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools

 
 
 

end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.OracleValidCut
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools GLS.Cast

 
 
 
 
 
 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleClearedCutGeometry
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools GLS.Cast

 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleSmallCutGeometry
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.Cast

 
 
 
 
 

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OraclePhaseCenter
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence

 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OraclePreparedCutSoundness
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.Cast

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleActiveCutSoundness
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 
 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleSerializationMath
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ProgramOutputUnique
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main

 
 
 
 
 

end EdgeSublinearMWIS.Main
end

-- Solutions.OracleTranscriptState
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleDialogueSoundness
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 
 

 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.WordRationalHeight
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixInverseValidClock
noncomputable section

open scoped Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds InverseMath

 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.HyperplaneApproximationClock
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RestrictedClockComposition
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 
 
 
 
 

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.EllipsoidRecoveryClock
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds InverseMath

 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleReductionClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RestrictedSelectiveChoose
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

 

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.SelectiveChoosePolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.ThreeMachine.StackCompiler.Realizer
variable {α β : Type} [Coding α] [Coding β]
 
end OAI.ThreeMachine.StackCompiler.Realizer
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]
 

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.OracleBranchClocks
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleClockValidity
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence GLS.Cast

 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleHeightBounds
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools GLS.EllipsoidStateSize

 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OraclePhaseSize
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence GLS.EllipsoidStateSize

 
 
 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleCoreSize
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ConvexTools

 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleDialogueClockValidity
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RestrictedFoldClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

 
end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.RestrictedComposedFoldClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 
end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.OracleExecutionClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleTranscriptParserClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleOutputBounds
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RestrictedExpandedClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 
 

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.OracleByteClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleWorkPolynomials
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleFiniteProgram
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main
open RawStack

 

end EdgeSublinearMWIS.Main
end

-- Solutions.OracleQualitativeCorrectness
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ExactBinaryOracleLocal
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main
open RawStack OAI.ThreeMachine.StackCompiler RealizerBounds

 

end EdgeSublinearMWIS.Main
end

-- Solutions.Sol_exact_binary_oracle
noncomputable section


end

open scoped BigOperators
open LLLFactor.RedBasis LLLFactor.Reduction
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds EdgeSublinearMWIS.Main.LLLBounds

theorem solution :
     ∃ C q : ℕ,0< C ∧ ∀ (n H : ℕ) (b : Fin n → Vec n),
       LinearIndependent ℝ b → IntegralRows b →
       (∀ k≤ n,1≤ LLLFactor.Reduction.gram b k ∧ LLLFactor.Reduction.gram b k≤(2:ℝ)^H) →
       (∀ j,‖b j‖≤(n+1)*((2:ℝ)^H+1)) → ∀ (A : Fin n → SignedVector),
       (∀ k,RepresentsVector (A k) (b k)) → (∀ k,VectorCanonical (A k)) →
       sizePassCodeRealizer.time (List.ofFn A)≤ C*(volume (List.ofFn A)+n+H+4)^q ∧
       volume (sizePassCode (List.ofFn A))≤ C*(volume (List.ofFn A)+n+H+4)^q := by
  exact sizePassCode_polynomial_time
