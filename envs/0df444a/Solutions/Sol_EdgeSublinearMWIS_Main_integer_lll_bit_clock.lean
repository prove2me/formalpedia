-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.integer_lll_bit_clock
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:16:39.623356+00:00
-- url     : https://prove2.me/submissions/f3c5295b-23c8-43e3-b300-f5b68c8d0f38

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
import Theorems.Thm_EdgeSublinearMWIS_Main_lll_size_reduction_bit_clock
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

namespace EdgeSublinearMWIS.Main.RawStack
open LLLFactor.RedBasis LLLFactor.Reduction OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds EdgeSublinearMWIS.Main.LLLBounds
theorem sizePassCode_polynomial_time :
     ∃ C q : ℕ,0< C ∧ ∀ (n H : ℕ) (b : Fin n → Vec n),
       LinearIndependent ℝ b → IntegralRows b →
       (∀ k≤ n,1≤ LLLFactor.Reduction.gram b k ∧ LLLFactor.Reduction.gram b k≤(2:ℝ)^H) →
       (∀ j,‖b j‖≤(n+1)*((2:ℝ)^H+1)) → ∀ (A : Fin n → SignedVector),
       (∀ k,RepresentsVector (A k) (b k)) → (∀ k,VectorCanonical (A k)) →
       sizePassCodeRealizer.time (List.ofFn A)≤ C*(volume (List.ofFn A)+n+H+4)^q ∧
       volume (sizePassCode (List.ofFn A))≤ C*(volume (List.ofFn A)+n+H+4)^q :=
  EdgeSublinearMWIS.Main.lll_size_reduction_bit_clock
end EdgeSublinearMWIS.Main.RawStack
end


-- Solutions.RawBinary
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 
 

 theorem increment_value (L : List Bool) : value (increment L)=value L+1 := by
  induction L with
  | nil => rfl
  | cons b L ih => cases b <;> simp [increment,value,ih] <;> omega

 

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

 
 theorem prependTrue_linear : Linear prependTrue := by
   have ht : Linear (Realizer.constant true : Realizer (fun _ : List Bool => true)) := linear_bool _ 2000 (fun L => by change (2*3+1)*(20*volume L+50*3+50)≤ _; omega)
   exact linear_comp (linear_pair ht linear_id) linear_cons
 
 theorem replicateTrue_polynomial : PolyBound replicateTrue := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : ℕ => ([] : List Bool))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   unfold replicateTrue
   apply polynomial_congr
   apply polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial hn))
   exact polynomial_iterate (linear_polynomial prependTrue_linear) 4 (fun L => by simp only [volume_cons,volume_bool_true]; omega)

 
 
 theorem falseCons_linear : Linear falseCons := by
   have ht : Linear (Realizer.false : Realizer (fun _ : List Bool => false)) := linear_bool _ 3 (fun _ => by change 2≤ _; omega)
   exact linear_comp (linear_pair ht linear_id) linear_cons
 
 theorem prefix_polynomial : PolyBound prefixRealizer :=
   polynomial_comp (polynomial_pair (polynomial_comp BinaryGcd.wordLength_polynomial replicateTrue_polynomial)
     (linear_polynomial falseCons_linear)) appendBits_polynomial

 

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

 
 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.CappedBinary
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 

 
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
 
 theorem min_polynomial : PolyBound minRealizer := by
   unfold minRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair nat_le_polynomial (linear_polynomial linear_id))
     (polynomial_choose (linear_polynomial linear_fst) (linear_polynomial linear_snd))

 
 
 
 
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

 
 
 theorem nextWord_polynomial : PolyBound nextWordRealizer :=
   polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_id)
     (linear_polynomial (linear_constant [true]))) word_polynomial) trim_polynomial
 
 
 theorem nextWord_eq (A : List Bool) : nextWord A=trim (increment A) := by
   apply canonical_value_injective _ _ (nextWord_canonical A) (trim_idem _)
   rw [nextWord_value,trim_value,increment_value]
 theorem nextWord_volume (A : List Bool) : volume (nextWord A)≤ volume A+4 := by
   rw [nextWord_eq]
   exact (trim_volume _).trans (increment_volume A)
 
 
 
 theorem naturalWord_polynomial : PolyBound naturalWordRealizer := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : ℕ => ([] : List Bool))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   unfold naturalWordRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial hn))
     (polynomial_iterate nextWord_polynomial 4 nextWord_volume)
 
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

 
 
 theorem flattenStep_polynomial : PolyBound (flattenStepRealizer (α:=α)) :=
   polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) appendList_polynomial
 
 theorem flatten_fold_polynomial : PolyBound (flattenStepRealizer (α:=α)).fold := by
   apply polynomial_fold_bounded flattenStep_polynomial 1
   intro xs acc j _
   rw [flattenFold]
   have hflat := volume_flatten (xs.take j)
   have ht := take_volume_le xs j
   have ha := volume_append acc (xs.take j).flatten
   simp only [volume_pair,one_mul]
   omega
 
 theorem flattenList_polynomial : PolyBound (flattenList (α:=α)) := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : List (List α) => ([] : List α))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   unfold flattenList
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial hn)) flatten_fold_polynomial

 
 
 theorem repeatStep_linear : Linear (repeatStepRealizer (α:=α)) := linear_pair linear_fst linear_cons
 
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

 
 theorem selectSingleton_polynomial {p : α×γ → Bool} {P : Realizer p} (hP : PolyBound P) : PolyBound (selectSingleton P) := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : α×γ => ([] : List α))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   exact polynomial_comp (polynomial_pair hP (linear_polynomial linear_id))
     (polynomial_choose (linear_polynomial (linear_comp (linear_pair linear_fst hn) linear_cons)) (linear_polynomial hn))
 
 
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

 
 theorem headNat_linear : Linear headNat := by
   refine linear_of _ 3 (by omega) (fun L => by change volume L+2≤ _; omega) ?_
   intro L
   cases L with
   | nil => simp
   | cons a L => simp only [List.headD_cons,volume_cons]; omega
 
 
 
 

 
 
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

 
 
 
 
 
 
 
 
 
 
 
 theorem nonemptyNatList_linear : Linear nonemptyNatList := by
   apply linear_bool _ 10000
   intro L
   exact Realizer.time_test_le (fun L : List ℕ => !L.isEmpty) (by intro L; cases L <;> rfl) L
 
 
 
 
 
 
 
 

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
 
 theorem signedFractionValue_code (q : RationalCode) : signedFractionValue (codeWords q)=q.value := by
   simp only [signedFractionValue,codeWords,signedValue_encode,value_natBits,RationalCode.value]
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

 
 
 
 theorem canonicalSub_denpos (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.2) :
     0< value (canonicalSub (a,b)).2.2 := canonicalAdd_denpos a _ ha hb
 theorem canonicalSub_value (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.2) :
     signedFractionValue (canonicalSub (a,b))=signedFractionValue a-signedFractionValue b := by
   change signedFractionValue (canonicalAdd (a,signedFractionNeg b))=_
   rw [canonicalAdd_value a (signedFractionNeg b) ha hb,signedFractionNeg_value,sub_eq_add_neg]
 

 
 
 
 
 
 
 
 
 

 
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

 
end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.SignedVectorSumBounds
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 

 

 

 
 

 
 
 

 

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GramSchmidtRowCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 

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

 
 theorem threeQuarter_den : 0< value threeQuarter.2.2 := by decide
 theorem threeQuarter_value : signedFractionValue threeQuarter=(3/4:ℚ) := by
   norm_num [threeQuarter,signedFractionValue,signedValue,value]
 
 
 theorem lovaszSquare_polynomial : PolyBound lovaszSquare :=
   polynomial_comp (linear_polynomial (linear_pair linear_fst linear_fst)) canonicalMul_polynomial
 
 theorem lovaszTerm_polynomial : PolyBound lovaszTerm :=
   polynomial_comp (polynomial_pair lovaszSquare_polynomial (linear_polynomial (linear_comp linear_snd linear_fst))) canonicalMul_polynomial
 
 
 theorem lovaszLeft_polynomial : PolyBound lovaszLeftRealizer :=
   polynomial_comp (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_snd)) lovaszTerm_polynomial) canonicalAdd_polynomial
 
 
 theorem lovaszRight_polynomial : PolyBound lovaszRightRealizer :=
   polynomial_comp (linear_polynomial (linear_pair (linear_constant threeQuarter) (linear_comp linear_snd linear_fst))) canonicalMul_polynomial
 
 
 
 
 
 
 theorem lovaszBad_polynomial : PolyBound lovaszBadRealizer :=
   polynomial_comp (polynomial_comp (polynomial_pair
     (polynomial_comp lovaszRight_polynomial (linear_polynomial linear_snd))
     (polynomial_comp lovaszLeft_polynomial (linear_polynomial linear_snd))) fractionLE_polynomial) (linear_polynomial linear_not)

 theorem fractionMagnitude (s : SignedWords) : fractionValue s.2=|signedFractionValue s| := by
   rcases s with ⟨b,N,D⟩
   cases b <;> simp [fractionValue,signedFractionValue,signedValue,abs_div,
     abs_of_nonneg (show (0:ℚ)≤ value N by positivity),abs_of_nonneg (show (0:ℚ)≤ value D by positivity)]

 theorem lovaszBad_correct (s : LovaszScalarInput)
     (hm : 0< value s.1.2.2) (hp : 0< value s.2.1.2.2) (hn : 0< value s.2.2.2.2)
     (hp0 : 0≤ signedFractionValue s.2.1) (hn0 : 0≤ signedFractionValue s.2.2) :
     lovaszBad s=true ↔ signedFractionValue s.2.2+(signedFractionValue s.1)^2*signedFractionValue s.2.1<
       (3/4:ℚ)*signedFractionValue s.2.1 := by
   have hD1 := canonicalMul_denpos s.1 s.1 hm hm
   have hD2 := canonicalMul_denpos (canonicalMul (s.1,s.1)) s.2.1 hD1 hp
   have hDL := canonicalAdd_denpos s.2.2 (canonicalMul (canonicalMul (s.1,s.1),s.2.1)) hn hD2
   have hDR := canonicalMul_denpos threeQuarter s.2.1 threeQuarter_den hp
   have hL : signedFractionValue (lovaszLeft s)=signedFractionValue s.2.2+
       (signedFractionValue s.1)^2*signedFractionValue s.2.1 := by
     rw [lovaszLeft,canonicalAdd_value _ _ hn hD2,canonicalMul_value _ _ hD1 hp,canonicalMul_value _ _ hm hm,pow_two]
   have hR : signedFractionValue (lovaszRight s)=(3/4:ℚ)*signedFractionValue s.2.1 := by
     rw [lovaszRight,canonicalMul_value _ _ threeQuarter_den hp,threeQuarter_value]
   have hL0 : 0≤ signedFractionValue (lovaszLeft s) := by rw [hL]; positivity
   have hR0 : 0≤ signedFractionValue (lovaszRight s) := by rw [hR]; positivity
   have htest := fractionLE_correct (lovaszRight s).2 (lovaszLeft s).2 hDR hDL
   rw [fractionMagnitude,fractionMagnitude,abs_of_nonneg hR0,abs_of_nonneg hL0] at htest
   have hb : lovaszBad s=true ↔ ¬fractionLE ((lovaszRight s).2,(lovaszLeft s).2)=true := by
     cases hh : fractionLE ((lovaszRight s).2,(lovaszLeft s).2) <;> simp [lovaszBad,lovaszTest,lovaszMagnitudes,Function.comp_apply,hh]
   rw [hb,htest,not_le,hL,hR]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedNearest
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 

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

 

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GramSchmidtCramerProjection
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 

 

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

 theorem gram_initial_upper {n L : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hB : ∀ i j, |B i j|≤(2:ℤ)^L) (i : ℕ) (hi : i≤ n) :
     LLLFactor.Reduction.gram (embed B) i≤(2:ℝ)^(n*n+(n+2*L)*n) := by
   let A : Matrix (Fin i) (Fin i) ℤ := fun j k =>
     ∑ l, B (Fin.castLE hi j) l*B (Fin.castLE hi k) l
   have hg : LLLFactor.Reduction.gram (embed B) i=(A.det:ℝ) := by
     rw [LLLFactor.Reduction.gram,dif_pos hi,Int.cast_det]
     congr 1
     ext j k
     exact inner_embed B _ _
   have hA : ∀ j k, |A j k|≤(2:ℤ)^(n+2*L) := fun j k => integer_inner_bound B hB _ _
   have hd : |A.det|≤(i.factorial:ℤ)*((2:ℤ)^(n+2*L))^i := by
     simpa using (Matrix.det_le (abv:=AbsoluteValue.abs) hA)
   have hf : (i.factorial:ℤ)≤(2:ℤ)^(i*i) := by exact_mod_cast factorial_le_two_square i
   have hbound : A.det≤(2:ℤ)^(n*n+(n+2*L)*n) := by
     calc
       _≤|A.det| := le_abs_self _
       _≤(i.factorial:ℤ)*((2:ℤ)^(n+2*L))^i := hd
       _≤(2:ℤ)^(i*i)*((2:ℤ)^(n+2*L))^i :=
         mul_le_mul_of_nonneg_right hf (by positivity)
       _=(2:ℤ)^(i*i+(n+2*L)*i) := by rw [← pow_mul,← pow_add]
       _≤(2:ℤ)^(n*n+(n+2*L)*n) := by
         apply pow_le_pow_right₀ (by norm_num)
         nlinarith
   rw [hg]
   exact_mod_cast hbound

 theorem potential_initial_upper {n L : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hb : LinearIndependent ℝ (embed B)) (hB : ∀ i j, |B i j|≤(2:ℤ)^L) :
     potD (embed B)≤(2:ℝ)^(n*(n*n+(n+2*L)*n)) := by
   let H := n*n+(n+2*L)*n
   have hcard : (Finset.Ioo 0 n).card≤ n := by simp [Nat.card_Ioo]
   calc
     _≤∏ _i∈Finset.Ioo 0 n, (2:ℝ)^H := by
       apply Finset.prod_le_prod
       · intro i hi
         exact ((gram_eq_prod_gs (embed B) hb).1 i (by have h:=Finset.mem_Ioo.mp hi; omega)).2.le
       · intro i hi
         exact gram_initial_upper B hB i (by have h:=Finset.mem_Ioo.mp hi; omega)
     _=((2:ℝ)^H)^((Finset.Ioo 0 n).card) := by simp
     _=(2:ℝ)^(H*((Finset.Ioo 0 n).card)) := (pow_mul _ _ _).symm
     _≤(2:ℝ)^(n*H) := by
       apply pow_le_pow_right₀ (by norm_num)
       nlinarith

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

 
 

 

 

 

 

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.GramSchmidtCoordinateBounds
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 

 

 

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

 

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLSizeStepCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 theorem nearestIntegerCode_denpos (s : SignedWords) : 0< value (nearestIntegerCode s).2.2 := by change 0< value [true]; decide
 theorem nearestIntegerCode_value (s : SignedWords) :
     signedFractionValue (nearestIntegerCode s)=(signedValue (signedNearest s).1 (signedNearest s).2:ℚ) := by
   simp [signedFractionValue,nearestIntegerCode,value]

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

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

 theorem sizePassCode_correct {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
     (A : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (b i))
     (hcan : ∀ i,VectorCanonical (A i)) :
     ∃ (c : Fin n → Vec n) (A' C : Fin n → SignedVector), SizePass n b c ∧
       sizePassCode (List.ofFn A)=(List.ofFn A',List.ofFn C) ∧
       (∀ k,RepresentsVector (A' k) (c k)) ∧ (∀ k,VectorCanonical (A' k)) ∧
       (∀ k,RepresentsVector (C k) (gs c k)) := by
   obtain ⟨C,hCeq,hC⟩ := forall2_ofFn_left (gsMatrix (List.ofFn A)) (gs b) (gsMatrix_rep b hb A hA)
   obtain ⟨c,A',hpass,hexec,hA',hcan'⟩ := fullSizeCode_correct b hb A C hA hC hcan n le_rfl
   refine ⟨c,A',C,hpass,?_,hA',hcan',?_⟩
   · simpa only [sizePassCode,sizePassInitialize,List.length_ofFn,hCeq] using hexec
   · intro k
     rw [pass_gs hpass k]
     exact hC k

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLovaszQueryCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem natSucc_linear : Linear Realizer.succ := by
   refine linear_of _ 201 (by omega) ?_ ?_
   · intro n
     have h:=Realizer.time_succ_le n
     simp only [volume_nat]
     omega
   · intro n
     simp only [volume_nat]
     omega

 
 
 
 
 theorem lovaszPrevGs_polynomial : PolyBound lovaszPrevGs := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp linear_snd linear_snd) linear_fst)) (lookupList_polynomial [])
 theorem lovaszNextGs_polynomial : PolyBound lovaszNextGs := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp linear_snd linear_snd) (linear_comp linear_fst natSucc_linear))) (lookupList_polynomial [])
 theorem lovaszNextRow_polynomial : PolyBound lovaszNextRow := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) (linear_comp linear_fst natSucc_linear))) (lookupList_polynomial [])
 
 
 theorem lovaszQueryData_polynomial : PolyBound lovaszQueryDataRealizer := polynomial_pair
   (polynomial_comp (polynomial_pair lovaszNextRow_polynomial lovaszPrevGs_polynomial) gsCoefficient_polynomial)
   (polynomial_pair
     (polynomial_comp (polynomial_pair lovaszPrevGs_polynomial lovaszPrevGs_polynomial) signedDot_polynomial)
     (polynomial_comp (polynomial_pair lovaszNextGs_polynomial lovaszNextGs_polynomial) signedDot_polynomial))
 
 
 theorem lovaszQuery_polynomial : PolyBound lovaszQueryRealizer :=
   polynomial_comp lovaszQueryData_polynomial lovaszBad_polynomial

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLFindBadCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem natPred_linear : Linear Realizer.pred := by
   refine linear_of _ 3 (by omega) ?_ ?_
   · intro n
     change volume n+2≤ _
     omega
   · intro n
     have h:=Nat.pred_le n
     simp only [volume_nat]
     omega

 
 
 theorem badList_polynomial : PolyBound badListRealizer :=
   polynomial_comp (polynomial_pair
     (polynomial_comp (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) listLength_polynomial)
       (linear_polynomial natPred_linear)) range_polynomial) (linear_polynomial linear_id))
     (filterEnvironment_polynomial lovaszQuery_polynomial)

 
 
 theorem findBadCode_polynomial : PolyBound findBadCodeRealizer :=
   polynomial_comp badList_polynomial (linear_polynomial (linear_pair nonemptyNatList_linear headNat_linear))

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

 
 
 theorem naturalProduct_polynomial : PolyBound naturalProductRealizer := by
   unfold naturalProductRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp (polynomial_comp
     (polynomial_pair (linear_polynomial linear_fst) (polynomial_comp (linear_polynomial linear_snd) replicateTrue_polynomial))
     replicateList_polynomial) flattenList_polynomial) listLength_polynomial

 
 theorem naturalSquare_polynomial : PolyBound naturalSquare :=
   polynomial_comp (linear_polynomial (linear_pair linear_id linear_id)) naturalProduct_polynomial
 
 theorem naturalFourth_polynomial : PolyBound naturalFourth := polynomial_comp naturalSquare_polynomial naturalSquare_polynomial
 
 theorem naturalFifth_polynomial : PolyBound naturalFifth := by
   unfold naturalFifth
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair naturalFourth_polynomial (linear_polynomial linear_id)) naturalProduct_polynomial

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

 
 
 theorem swapOld_polynomial (a : α) : PolyBound (swapOld a) :=
   polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) (lookupList_polynomial a)
 theorem swapNew_polynomial (a : α) : PolyBound (swapNew a) :=
   polynomial_comp (linear_polynomial (linear_pair linear_snd (linear_comp linear_fst natSucc_linear))) (lookupList_polynomial a)
 
 
 theorem swapFirst_polynomial (a : α) : PolyBound (swapFirstRealizer a) :=
   polynomial_comp (polynomial_pair (linear_polynomial linear_snd)
     (polynomial_pair (linear_polynomial linear_fst) (swapNew_polynomial a))) (replaceList_polynomial a)
 
 
 theorem swapAdjacent_polynomial (a : α) : PolyBound (swapAdjacentRealizer a) :=
   polynomial_comp (polynomial_pair (swapFirst_polynomial a)
     (polynomial_pair (linear_polynomial (linear_comp linear_fst natSucc_linear)) (swapOld_polynomial a))) (replaceList_polynomial a)

 theorem swapAdjacent_ofFn {n : ℕ} (a : α) (A : Fin n → α) (i : Fin n) (hi : i.val+1< n) :
     swapAdjacent a (i.val,List.ofFn A)=
       List.ofFn (A ∘ Equiv.swap i (⟨i.val+1,hi⟩:Fin n)) := by
   let j : Fin n := ⟨i.val+1,hi⟩
   have hij : i≠j := by intro he; have hh:=congrArg Fin.val he; dsimp [j] at hh; omega
   have hfirst : swapFirst a (i.val,List.ofFn A)=List.ofFn (Function.update A i (A j)) := by
     change replaceList a (List.ofFn A,(i.val,((List.ofFn A).drop (i.val+1)).headD a))=_
     rw [lookup_ofFn_default A j a,replaceList_ofFn]
   have hsecond : swapAdjacent a (i.val,List.ofFn A)=
       List.ofFn (Function.update (Function.update A i (A j)) j (A i)) := by
     change replaceList a (swapFirst a (i.val,List.ofFn A),(i.val+1,((List.ofFn A).drop i.val).headD a))=_
     rw [hfirst,lookup_ofFn_default,replaceList_ofFn a _ j]
   rw [hsecond]
   congr 1
   change Function.update (Function.update A i (A j)) j (A i)=A ∘ Equiv.swap i j
   funext k
   by_cases hki : k=i
   · subst k
     simp [Function.update_self,Function.update_of_ne hij,Function.comp_apply]
   · by_cases hkj : k=j
     · subst k
       simp [Function.update_self,Function.comp_apply]
     · simp [Function.update_of_ne hki,Function.update_of_ne hkj,Function.comp_apply,
         Equiv.swap_apply_of_ne_of_ne hki hkj]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLRoundCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 theorem finishContinue_polynomial : PolyBound finishContinue := polynomial_pair
   (linear_polynomial (linear_constant false))
   (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst linear_snd) (linear_comp linear_snd linear_fst))) (swapAdjacent_polynomial []))
 
 theorem finishDone_linear : Linear finishDone :=
   linear_pair (linear_constant true) (linear_comp linear_snd linear_fst)
 
 
 theorem finishWithBad_polynomial : PolyBound finishWithBadRealizer := by
   unfold finishWithBadRealizer
   apply polynomial_congr
   exact polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst linear_fst) linear_id))
     (polynomial_choose finishContinue_polynomial (linear_polynomial finishDone_linear))
 
 
 theorem finishPass_polynomial : PolyBound finishPassRealizer :=
   polynomial_comp (polynomial_pair findBadCode_polynomial (linear_polynomial linear_id)) finishWithBad_polynomial
 
 

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

 theorem gs_lovasz_square {n : ℕ} (b : Fin n → Vec n) (i j : Fin n) (hij : i≠j) :
     ‖gs b j+mu b j i • gs b i‖^2=‖gs b j‖^2+(mu b j i)^2*‖gs b i‖^2 := by
   rw [norm_add_sq_real]
   simp only [inner_smul_right,GS.gs_orth b hij.symm,mul_zero,add_zero,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]

 theorem cond119_scalar {n : ℕ} (b : Fin n → Vec n) (i : Fin n) (hi : i.val+1< n) :
     Cond119 b (i.val+2) ↔
       ‖gs b ⟨i.val+1,hi⟩‖^2+(mu b ⟨i.val+1,hi⟩ i)^2*‖gs b i‖^2<
         (3/4:ℝ)*‖gs b i‖^2 := by
   let j : Fin n := ⟨i.val+1,hi⟩
   have hij : i≠j := by intro he; have:=congrArg Fin.val he; dsimp [j] at this; omega
   have he := gs_lovasz_square b i j hij
   have h1 : i.val+2-1=i.val+1 := by omega
   have h2 : i.val+2-2=i.val := by omega
   constructor
   · rintro ⟨hk,hbad⟩
     have hh : ‖gs b j+mu b j i • gs b i‖^2<(3/4:ℝ)*‖gs b i‖^2 := by simpa only [h1,h2] using hbad
     rwa [he] at hh
   · intro hbad
     refine ⟨⟨by omega,by omega⟩,?_⟩
     have hh : ‖gs b j+mu b j i • gs b i‖^2<(3/4:ℝ)*‖gs b i‖^2 := by rwa [he]
     simpa only [h1,h2] using hh

end EdgeSublinearMWIS.Main.LLLBounds
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 theorem lovaszQuery_correct {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
     (A G : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (b i))
     (hG : ∀ i,RepresentsVector (G i) (gs b i))
     (i : Fin n) (hi : i.val+1< n) :
     lovaszQuery (i.val,(List.ofFn A,List.ofFn G))=true ↔ Cond119 b (i.val+2) := by
   let j : Fin n := ⟨i.val+1,hi⟩
   let m := gsCoefficient (A j,G i)
   let P := signedDot (G i,G i)
   let N := signedDot (G j,G j)
   have hdata : lovaszQueryData (i.val,(List.ofFn A,List.ofFn G))=(m,(P,N)) := by
     dsimp only [lovaszQueryData,m,P,N]
     rw [lookup_ofFn_default A j [],lookup_ofFn_default G i [],lookup_ofFn_default G j []]
   have hm := coefficient_represents (hA j) (hG i) (InnerProductSpace.gramSchmidt_ne_zero i hb)
   have hp := represents_dot (hG i) (hG i)
   have hn := represents_dot (hG j) (hG j)
   have hp0 : (0:ℚ)≤ signedFractionValue P := by
     have h : (0:ℝ)≤(signedFractionValue P:ℝ) := by rw [hp.2]; exact real_inner_self_nonneg
     exact_mod_cast h
   have hn0 : (0:ℚ)≤ signedFractionValue N := by
     have h : (0:ℝ)≤(signedFractionValue N:ℝ) := by rw [hn.2]; exact real_inner_self_nonneg
     exact_mod_cast h
   have hmval : (signedFractionValue m:ℝ)=mu b j i := hm.2
   have hpval : (signedFractionValue P:ℝ)=‖gs b i‖^2 := hp.2.trans (real_inner_self_eq_norm_sq _)
   have hnval : (signedFractionValue N:ℝ)=‖gs b j‖^2 := hn.2.trans (real_inner_self_eq_norm_sq _)
   change lovaszBad (lovaszQueryData (i.val,(List.ofFn A,List.ofFn G)))=true ↔_
   rw [hdata,lovaszBad_correct (m,(P,N)) hm.1 hp.1 hn.1 hp0 hn0,cond119_scalar b i hi]
   change signedFractionValue N+(signedFractionValue m)^2*signedFractionValue P<(3/4:ℚ)*signedFractionValue P ↔
     ‖gs b j‖^2+(mu b j i)^2*‖gs b i‖^2<(3/4:ℝ)*‖gs b i‖^2
   rw [← hmval,← hpval,← hnval]
   have hcast : (((signedFractionValue N+(signedFractionValue m)^2*signedFractionValue P):ℚ):ℝ)<
       ((((3/4:ℚ)*signedFractionValue P):ℚ):ℝ) ↔
       signedFractionValue N+(signedFractionValue m)^2*signedFractionValue P<(3/4:ℚ)*signedFractionValue P := Rat.cast_lt
   simpa only [Rat.cast_add,Rat.cast_pow,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] using hcast.symm

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLFindBadMath
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 theorem badList_mem (s : WordBasisState) (i : ℕ) :
     i∈badList s ↔ i< s.1.length-1 ∧ lovaszQuery (i,s)=true := by
   simp [badList]

 theorem findBadCode_member (s : WordBasisState) (h : (findBadCode s).1=true) :
     (findBadCode s).2∈badList s := by
   cases hs : badList s with
   | nil => simp [findBadCode,hs] at h
   | cons a xs => simp [findBadCode,hs]

 theorem findBadCode_empty (s : WordBasisState) (h : (findBadCode s).1=false) : badList s=[] := by
   cases hs : badList s with
   | nil => rfl
   | cons a xs => simp [findBadCode,hs] at h

 theorem findBadCode_some {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
     (A G : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (b i))
     (hG : ∀ i,RepresentsVector (G i) (gs b i))
     (h : (findBadCode (List.ofFn A,List.ofFn G)).1=true) :
     let k := (findBadCode (List.ofFn A,List.ofFn G)).2
     k+1< n ∧ Cond119 b (k+2) := by
   let s := (List.ofFn A,List.ofFn G)
   let k := (findBadCode s).2
   have hmem := (badList_mem s k).mp (findBadCode_member s h)
   have hk : k+1< n := by
     have hh : k< n-1 := by simpa only [s,List.length_ofFn] using hmem.1
     omega
   refine ⟨hk,?_⟩
   exact (lovaszQuery_correct b hb A G hA hG ⟨k,by omega⟩ hk).mp hmem.2

 theorem findBadCode_none {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
     (A G : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (b i))
     (hG : ∀ i,RepresentsVector (G i) (gs b i))
     (hsmall : ∀ i j : Fin n,j< i → |mu b i j|≤(1/2:ℝ))
     (h : (findBadCode (List.ofFn A,List.ofFn G)).1=false) : IsReduced b := by
   have hempty := findBadCode_empty (List.ofFn A,List.ofFn G) h
   refine ⟨hsmall,?_⟩
   intro i hi
   let p : Fin n := ⟨i,by omega⟩
   let j : Fin n := ⟨i+1,hi⟩
   have hnot : ¬Cond119 b (i+2) := by
     intro hbad
     have hquery := (lovaszQuery_correct b hb A G hA hG p hi).mpr hbad
     have hmem : i∈badList (List.ofFn A,List.ofFn G) := by
       apply (badList_mem _ _).mpr
       exact ⟨by simp only [List.length_ofFn]; omega,hquery⟩
     rw [hempty] at hmem
     exact List.not_mem_nil hmem
   have hpj : p≠j := by intro he; have hh:=congrArg Fin.val he; dsimp [p,j] at hh; omega
   change (3/4:ℝ)*‖gs b p‖^2≤‖gs b j+mu b j p • gs b p‖^2
   rw [LLLBounds.gs_lovasz_square b p j hpj]
   exact le_of_not_gt (fun hbad => hnot ((LLLBounds.cond119_scalar b p hi).mpr hbad))

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

 

 theorem swap_case {n : ℕ} {b d c : Fin n → Vec n} {k : ℕ}
     (hb : LinearIndependent ℝ b) (hpass : SizePass n b d)
     (hk : 2≤ k ∧ k≤ n) (hbad : Cond119 d k)
     (hc : c=d ∘ Equiv.swap (⟨k-2,by omega⟩:Fin n) ⟨k-1,by omega⟩) :
     Case1 (d,k) (c,k-1) := by
   refine ⟨hk,d,?_,hbad,hc,rfl⟩
   unfold Achieve118
   rw [dif_pos hk]
   left
   refine ⟨?_,rfl⟩
   exact pass_mu hpass hb ⟨k-1,by omega⟩ ⟨k-2,by omega⟩ (by simp; omega) (by change k-2< k-1; omega)

 theorem fullSwap_properties {n : ℕ} {b c : Fin n → Vec n}
     (hb : LinearIndependent ℝ b) (h : FullSwap b c) :
     LinearIndependent ℝ c ∧ latticeOf c=latticeOf b ∧
       potD c<(3/4:ℝ)*potD b ∧
       LLLFactor.Reduction.gram c n=LLLFactor.Reduction.gram b n := by
   obtain ⟨d,hpass,k,hk,hbad,hc⟩ := h
   have hd := pass_basis hpass hb
   have hcase := swap_case hb hpass hk hbad hc
   have hs := step_preserves_basis d c k (k-1) hd.1 (Or.inl hcase)
   have hp := (potD_case1_lt d c k (k-1) hd.1).1 hcase
   have hpot : potD d=potD b := by
     unfold potD
     apply Finset.prod_congr rfl
     intro i hi
     exact pass_gram hpass hb i (by have h:=Finset.mem_Ioo.mp hi; omega)
   refine ⟨hs.1,hs.2.trans hd.2,?_,?_⟩
   · simpa only [hpot] using hp.2.2
   · exact (hp.2.1 n le_rfl (by omega)).trans (pass_gram hpass hb n le_rfl)

 theorem fullSwap_integral {n : ℕ} {b c : Fin n → Vec n}
     (hb : IntegralRows b) (h : FullSwap b c) : IntegralRows c := by
   obtain ⟨d,hpass,k,hk,hbad,hc⟩ := h
   obtain ⟨B,hB⟩ := pass_integral hpass hb
   rw [hc,hB]
   exact ⟨B ∘ Equiv.swap _ _,rfl⟩

 

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

 theorem finishPass_continue (s : WordBasisState) (h : (findBadCode s).1=true) :
     finishPass s=(false,swapAdjacent [] ((findBadCode s).2,s.1)) := by
   unfold finishPass finishWithBad
   rw [h]
   rfl
 theorem finishPass_done (s : WordBasisState) (h : (findBadCode s).1=false) :
     finishPass s=(true,s.1) := by
   unfold finishPass finishWithBad
   rw [h]
   rfl

 theorem basisRound_correct {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
     (A : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (b i))
     (hcan : ∀ i,VectorCanonical (A i)) :
     (∃ (c : Fin n → Vec n) (A' : Fin n → SignedVector),
       basisRound (List.ofFn A)=(true,List.ofFn A') ∧ SizePass n b c ∧ IsReduced c ∧
       (∀ k,RepresentsVector (A' k) (c k)) ∧ (∀ k,VectorCanonical (A' k))) ∨
     (∃ (c : Fin n → Vec n) (A' : Fin n → SignedVector),
       basisRound (List.ofFn A)=(false,List.ofFn A') ∧ FullSwap b c ∧
       (∀ k,RepresentsVector (A' k) (c k)) ∧ (∀ k,VectorCanonical (A' k))) := by
   obtain ⟨d,A1,G,hpass,hexec,hA1,hcan1,hgs⟩ := sizePassCode_correct b hb A hA hcan
   have hd := (pass_basis hpass hb).1
   let s : WordBasisState := (List.ofFn A1,List.ofFn G)
   cases hflag : (findBadCode s).1 with
   | false =>
     left
     have hsmall : ∀ i j : Fin n,j< i → |mu d i j|≤(1/2:ℝ) :=
       fun i j hji => pass_mu hpass hb i j i.isLt hji
     have hred := findBadCode_none d hd A1 G hA1 hgs hsmall hflag
     refine ⟨d,A1,?_,hpass,hred,hA1,hcan1⟩
     rw [basisRound,hexec,finishPass_done s hflag]
   | true =>
     right
     let k := (findBadCode s).2
     have hbad := findBadCode_some d hd A1 G hA1 hgs hflag
     have hk : k+1< n := hbad.1
     let p : Fin n := ⟨k,by omega⟩
     let q : Fin n := ⟨k+1,hk⟩
     let c := d ∘ Equiv.swap p q
     let A' := A1 ∘ Equiv.swap p q
     have hfull : FullSwap b c := by
       refine ⟨d,hpass,k+2,⟨by omega,by omega⟩,hbad.2,?_⟩
       simp only [show k+2-2=k by omega,show k+2-1=k+1 by omega]
       rfl
     refine ⟨c,A',?_,hfull,?_,?_⟩
     · rw [basisRound,hexec,finishPass_continue s hflag]
       change (false,swapAdjacent [] (k,List.ofFn A1))=(false,List.ofFn A')
       rw [swapAdjacent_ofFn [] A1 p hk]
     · intro j
       exact hA1 (Equiv.swap p q j)
     · intro j
       exact hcan1 (Equiv.swap p q j)

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

 theorem fullSwap_gram_le {n : ℕ} {b c : Fin n → Vec n}
     (hb : LinearIndependent ℝ b) (h : FullSwap b c) (i : ℕ) (hi : i≤ n) :
     LLLFactor.Reduction.gram c i≤ LLLFactor.Reduction.gram b i := by
   obtain ⟨d,hpass,k,hk,hbad,hc⟩ := h
   have hd := (pass_basis hpass hb).1
   have hcase := swap_case hb hpass hk hbad hc
   have hp := (potD_case1_lt d c k (k-1) hd).1 hcase
   have hsame := pass_gram hpass hb i hi
   by_cases he : i=k-1
   · rw [he]
     have hpos := ((gram_eq_prod_gs d hd).1 (k-1) (by omega)).2
     have hbound : LLLFactor.Reduction.gram c (k-1)≤ LLLFactor.Reduction.gram d (k-1) := by linarith [hp.1]
     exact hbound.trans_eq (pass_gram hpass hb (k-1) (by omega))
   · exact (hp.2.1 i hi he).le.trans_eq hsame

 

 theorem fullSwap_norm {n : ℕ} {b c : Fin n → Vec n}
     (h : FullSwap b c) (hb : LinearIndependent ℝ b) (hint : IntegralRows b)
     (R : ℝ) (hR : 1≤ R) (hG : ∀ k≤ n,LLLFactor.Reduction.gram b k≤ R)
     (hstart : ∀ i,‖b i‖≤(n+1)*(R+1)) : ∀ i,‖c i‖≤(n+1)*(R+1) := by
   obtain ⟨d,hpass,k,hk,hbad,hc⟩ := h
   have hd := pass_prefix_norm hpass hb hint R hR hG hstart
   intro i
   rw [hc]
   exact hd _

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLLoopInvariant
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 theorem integral_gram_ge_one {n : ℕ} (b : Fin n → Vec n)
     (hb : LinearIndependent ℝ b) (hint : IntegralRows b) (k : ℕ) (hk : k≤ n) :
     1≤ LLLFactor.Reduction.gram b k := by
   obtain ⟨B,rfl⟩ := hint
   exact gram_ge_one B hb k hk

 

 theorem invariant_pass {n H : ℕ} {original b c : Fin n → Vec n}
     (hb : BasisInvariant original H b) (h : SizePass n b c) : BasisInvariant original H c := by
   refine ⟨(pass_basis h hb.linear).1,pass_integral h hb.integral,
     (pass_basis h hb.linear).2.trans hb.lattice,?_,?_⟩
   · intro k hk
     rw [pass_gram h hb.linear k hk]
     exact hb.gram k hk
   · exact pass_prefix_norm h hb.linear hb.integral (2^H) (one_le_pow₀ (by norm_num))
       (fun k hk => (hb.gram k hk).2) hb.norm

 theorem invariant_swap {n H : ℕ} {original b c : Fin n → Vec n}
     (hb : BasisInvariant original H b) (h : FullSwap b c) : BasisInvariant original H c := by
   have hc := fullSwap_properties hb.linear h
   have hint := fullSwap_integral hb.integral h
   refine ⟨hc.1,hint,hc.2.1.trans hb.lattice,?_,?_⟩
   · intro k hk
     exact ⟨integral_gram_ge_one c hc.1 hint k hk,
       (fullSwap_gram_le hb.linear h k hk).trans (hb.gram k hk).2⟩
   · exact fullSwap_norm h hb.linear hb.integral (2^H) (one_le_pow₀ (by norm_num))
       (fun k hk => (hb.gram k hk).2) hb.norm

end EdgeSublinearMWIS.Main.LLLBounds
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 

 theorem reductionGood_initial {n H : ℕ} (b : Fin n → Vec n)
     (hb : BasisInvariant b H b) (A : Fin n → SignedVector)
     (hA : ∀ k,RepresentsVector (A k) (b k)) (hcan : ∀ k,VectorCanonical (A k)) :
     ReductionGood b H 0 (false,List.ofFn A) := by
   refine ⟨b,A,rfl,hA,hcan,hb,?_,?_⟩
   · intro h
     simp at h
   · intro h
     exact .zero

 theorem reductionGood_step {n H t : ℕ} {original : Fin n → Vec n} {s : ReductionState}
     (h : ReductionGood original H t s) : ReductionGood original H (t+1) (reductionBody s) := by
   obtain ⟨b,A,hword,hA,hcan,hbasis,hred,htrace⟩ := h
   cases hflag : s.1 with
   | true =>
     have hbody : reductionBody s=s := by simp only [reductionBody,hflag,if_true]
     rw [hbody]
     refine ⟨b,A,hword,hA,hcan,hbasis,hred,?_⟩
     intro hh
     rw [hflag] at hh
     cases hh
   | false =>
     have hbody : reductionBody s=basisRound (List.ofFn A) := by
       simp only [reductionBody,hflag,Bool.false_eq_true,if_false,reductionActive,Function.comp_apply,hword]
     rw [hbody]
     rcases basisRound_correct b hbasis.linear A hA hcan with hdone|hmore
     · obtain ⟨c,A',hexec,hpass,hreduced,hA',hcan'⟩ := hdone
       rw [hexec]
       refine ⟨c,A',rfl,hA',hcan',invariant_pass hbasis hpass,fun _ => hreduced,?_⟩
       intro hh
       cases hh
     · obtain ⟨c,A',hexec,hswap,hA',hcan'⟩ := hmore
       rw [hexec]
       refine ⟨c,A',rfl,hA',hcan',invariant_swap hbasis hswap,?_,?_⟩
       · intro hh
         cases hh
       · intro hh
         exact .succ (htrace hflag) hswap

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

 theorem reductionGood_iterate {n H : ℕ} {b : Fin n → Vec n} {s : ReductionState}
     (h : ReductionGood b H 0 s) : ∀ t,ReductionGood b H t (reductionBody^[t] s) := by
   intro t
   induction t with
   | zero => exact h
   | succ t ih => rw [Function.iterate_succ_apply']; exact reductionGood_step ih

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLowerTrace
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 

 

 

 

 

 

 

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

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLowerWordTrace
noncomputable section

open scoped Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

end EdgeSublinearMWIS.Main.LLLBounds
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 

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

 theorem basisRound_polynomial_time :
     ∃ C q : ℕ,0< C ∧ ∀ (n H : ℕ) (b : Fin n → Vec n),
       LinearIndependent ℝ b → IntegralRows b →
       (∀ k≤ n,1≤ LLLFactor.Reduction.gram b k ∧ LLLFactor.Reduction.gram b k≤(2:ℝ)^H) →
       (∀ j,‖b j‖≤(n+1)*((2:ℝ)^H+1)) → ∀ (A : Fin n → SignedVector),
       (∀ k,RepresentsVector (A k) (b k)) → (∀ k,VectorCanonical (A k)) →
       basisRoundRealizer.time (List.ofFn A)≤ C*(volume (List.ofFn A)+n+H+4)^q ∧
       volume (basisRound (List.ofFn A))≤ C*(volume (List.ofFn A)+n+H+4)^q := by
   obtain ⟨C,p,hC,hpass⟩ := sizePassCode_polynomial_time
   obtain ⟨D,q,hD,hfinish⟩ := finishPass_polynomial
   let F := D*(C+1)^q+20*C+20
   let e := p+(p+1)*q+2
   refine ⟨F,e,by dsimp [F]; positivity,?_⟩
   intro n H b hb hint hG hstart A hA hcan
   let xs := List.ofFn A
   let z := volume xs+n+H+4
   let v := volume (sizePassCode xs)
   have hz : 1≤ z := by dsimp [z]; omega
   have hi := hpass n H b hb hint hG hstart A hA hcan
   have hh := hfinish (sizePassCode xs)
   have hbase : v+1≤ v+z := by omega
   have htime : finishPassRealizer.time (sizePassCode xs)≤ D*(v+z)^q :=
     hh.1.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hbase q))
   have hout : volume (finishPass (sizePassCode xs))≤ D*(v+z)^q :=
     hh.2.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hbase q))
   have hclock := RuntimeMath.polynomial_pipeline_clock z C p D q
     (sizePassCodeRealizer.time xs) v (finishPassRealizer.time (sizePassCode xs)) hz hi.1 hi.2 htime
   have hoclock := RuntimeMath.polynomial_pipeline_clock z C p D q
     (sizePassCodeRealizer.time xs) v (volume (finishPass (sizePassCode xs))) hz hi.1 hi.2 hout
   change basisRoundRealizer.time xs≤ F*z^e ∧ volume (basisRound xs)≤ F*z^e
   constructor
   · unfold basisRoundRealizer
     rw [Realizer.time_comp]
     exact hclock
   · change volume (finishPass (sizePassCode xs))≤ _
     dsimp [F,e] at *
     omega

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

 theorem reductionBody_polynomial_time :
     ∃ C q : ℕ,0< C ∧ ∀ (n H t : ℕ) (original : Fin n → Vec n) (s : ReductionState),
       ReductionGood original H t s →
       reductionBodyRealizer.time s≤ C*(volume s+n+H+4)^q ∧
       volume (reductionBody s)≤ C*(volume s+n+H+4)^q := by
   obtain ⟨C,q,hC,hround⟩ := basisRound_polynomial_time
   let pre : Realizer (fun s : ReductionState => (s.1,s)) := Realizer.fst.pair Realizer.id
   have hpreL : Linear pre := by apply linear_pair; exact linear_fst; exact linear_id
   obtain ⟨F,hF,hpre⟩ := hpreL
   refine ⟨100*C+F+2000,q+1,by omega,?_⟩
   intro n H t original s hgood
   obtain ⟨b,A,hword,hA,hcan,hb,hred,htrace⟩ := hgood
   let z := volume s+n+H+4
   have hz : 1≤ z := by dsimp [z]; omega
   have hs : volume s≤ z := by dsimp [z]; omega
   have hin : volume s+1≤ z := by dsimp [z]; omega
   have hpair : volume s=volume s.1+volume s.2+1 := by cases s; exact volume_pair _ _
   have hAvol : volume (List.ofFn A)≤ volume s := by rw [← hword]; omega
   have hbase : volume (List.ofFn A)+n+H+4≤ z :=
     Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hAvol n) H) 4
   have hr := hround n H b hb.linear hb.integral hb.gram hb.norm A hA hcan
   have hrt : basisRoundRealizer.time s.2≤ C*z^q := by
     rw [hword]
     exact hr.1.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
   have hrv : volume (basisRound s.2)≤ C*z^q := by
     rw [hword]
     exact hr.2.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
   have hactiveT : reductionActiveRealizer.time s≤ C*z^q+20*z := by
     unfold reductionActiveRealizer
     rw [Realizer.time_comp,Realizer.time_snd]
     nlinarith
   have hactiveV : volume (reductionActive s)≤ C*z^q := hrv
   have hpreT : pre.time s≤ F*z := (hpre s).1.trans (Nat.mul_le_mul_left F hin)
   have hbool := volume_bool s.1
   have hVp : volume (s.1,s)≤ z+4 := by simp only [volume_pair]; omega
   have hq : z^q≤ z^(q+1) := Nat.pow_le_pow_right hz (by omega)
   have hze : z≤ z^(q+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+1)
   have hCp := Nat.mul_le_mul_left C hq
   have hFp := Nat.mul_le_mul_left (F+2000) hze
   change reductionBodyRealizer.time s≤(100*C+F+2000)*z^(q+1) ∧
     volume (reductionBody s)≤(100*C+F+2000)*z^(q+1)
   constructor
   · unfold reductionBodyRealizer
     rw [Realizer.time_congr]
     change (pre.comp (Realizer.id.choose reductionActiveRealizer)).time s≤ _
     rw [Realizer.time_comp]
     change pre.time s+(Realizer.id.choose reductionActiveRealizer).time (s.1,s)+10*(volume (s.1,s)+1)≤ _
     rw [Realizer.time_choose]
     rw [Realizer.time_comp (Realizer.snd : Realizer (Prod.snd : Bool×ReductionState → ReductionState))
       (Realizer.id : Realizer (id : ReductionState → ReductionState)) (s.1,s)]
     rw [Realizer.time_comp (Realizer.snd : Realizer (Prod.snd : Bool×ReductionState → ReductionState))
       reductionActiveRealizer (s.1,s)]
     simp only [Realizer.time_snd,Realizer.time_id,Prod.snd,id_eq]
     nlinarith
   · have hout : volume (reductionBody s)≤ volume s+volume (reductionActive s) := by
       unfold reductionBody
       split <;> omega
     nlinarith

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

 theorem reductionGood_volume {n H t : ℕ} {original : Fin n → Vec n} {s : ReductionState}
     (h : ReductionGood original H t s) :
     volume s≤(n*(n*(14*(intermediateExponent n H+2)+1)+2)+1)+4 := by
   obtain ⟨b,A,hword,hA,hcan,hb,hred,htrace⟩ := h
   have hnorm : ∀ i,‖b i‖≤(2:ℝ)^(intermediateExponent n H) := by
     intro i
     exact (hb.norm i).trans ((size_constant_bound n H).trans
       (pow_le_pow_right₀ (by norm_num) (by dsimp [intermediateExponent]; omega)))
   have hv := integer_matrix_word_volume b hb.integral hnorm A hA hcan
   have hp : volume s=volume s.1+volume s.2+1 := by cases s; exact volume_pair _ _
   have hbool := volume_bool s.1
   rw [hword] at hp
   omega

 theorem reductionLoop_polynomial_time :
     ∃ C q : ℕ,0< C ∧ ∀ (n H N : ℕ) (b : Fin n → Vec n),
       BasisInvariant b H b → ∀ A : Fin n → SignedVector,
       (∀ k,RepresentsVector (A k) (b k)) → (∀ k,VectorCanonical (A k)) →
       reductionLoopRealizer.time (N,List.ofFn A)≤ C*(volume (N,List.ofFn A)+n+H+4)^q ∧
       volume (reductionLoop (N,List.ofFn A))≤ C*(volume (N,List.ofFn A)+n+H+4)^q := by
   obtain ⟨C,q,hC,hbody⟩ := reductionBody_polynomial_time
   let K := C*310^q
   let e := 4*q+7
   let pre : Realizer (fun s : ℕ×List SignedVector => (s.1,(false,s.2))) :=
     Realizer.fst.pair ((Realizer.constant false).pair Realizer.snd)
   have hpreL : Linear pre := by
     apply linear_pair
     · exact linear_fst
     · exact linear_pair (linear_constant false) linear_snd
   obtain ⟨F,hF,hpre⟩ := hpreL
   refine ⟨10000*K+F+4000000,e,by positivity,?_⟩
   intro n H N b hb A hA hcan
   let input := (N,List.ofFn A)
   let initial : ReductionState := (false,List.ofFn A)
   let z := volume input+n+H+4
   have hz : 1≤ z := by dsimp [z]; omega
   have hn : n≤ z := by dsimp [z]; omega
   have hH : H≤ z := by dsimp [z]; omega
   have hN : N+1≤ z := by
     have hh : volume input=(2*N+1)+volume (List.ofFn A)+1 := by simp only [input,volume_pair,volume_nat]
     dsimp only [z]
     omega
   have hgood (j : ℕ) : ReductionGood b H j (reductionBody^[j] initial) :=
     reductionGood_iterate (reductionGood_initial b hb A hA hcan) j
   have hV : ∀ j≤ N,volume (reductionBody^[j] initial)≤304*z^4 := by
     intro j hj
     have hv := reductionGood_volume (hgood j)
     have hm := intermediate_matrix_numeric n H z hz hn hH
     have h1 : 1≤ z^4 := one_le_pow₀ hz
     nlinarith
   have hT : ∀ j< N,reductionBodyRealizer.time (reductionBody^[j] initial)≤ K*z^(4*q) := by
     intro j hj
     have hh := (hbody n H j b (reductionBody^[j] initial) (hgood j)).1
     have hv := hV j hj.le
     have hzz : z≤ z^4 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤4)
     have h1 : 1≤ z^4 := one_le_pow₀ hz
     have hbase : volume (reductionBody^[j] initial)+n+H+4≤310*z^4 := by nlinarith
     have hm := hh.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
     simpa only [K,mul_pow,← pow_mul,Nat.mul_assoc] using hm
   have hit := Realizer.time_iterate_le reductionBodyRealizer N initial (K*z^(4*q)) (304*z^4) hT hV
   have hinside : K*z^(4*q)+304*z^4+N+1≤ K*z^(4*q)+304*z^4+z := by omega
   have hm := Nat.mul_le_mul_left 10000 (Nat.mul_le_mul hN hinside)
   have heq : 10000*(z*(K*z^(4*q)+304*z^4+z))=
       10000*K*z^(4*q+1)+3040000*z^5+10000*z^2 := by simp only [pow_succ]; ring
   rw [heq] at hm
   have hiter : reductionBodyRealizer.iterate.time (N,initial)≤10000*K*z^(4*q+1)+3040000*z^5+10000*z^2 :=
     hit.trans (by simpa only [Nat.mul_assoc] using hm)
   have hp1 : z^(4*q+1)≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hp2 : z^5≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hp3 : z^2≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hp4 : z^4≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hpz : z≤ z^e := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by dsimp [e]; omega : 1≤ e)
   have hpret : pre.time input≤ F*z := (hpre input).1.trans (Nat.mul_le_mul_left F (by dsimp [z]; omega))
   have hpreV : volume (N,initial)≤ z := by
     have hbf := volume_bool false
     dsimp [initial,input,z]
     simp only [volume_pair,volume_nat]
     omega
   change reductionLoopRealizer.time input≤(10000*K+F+4000000)*z^e ∧
     volume (reductionLoop input)≤(10000*K+F+4000000)*z^e
   constructor
   · unfold reductionLoopRealizer
     rw [Realizer.time_comp]
     have ht1 := Nat.mul_le_mul_left (10000*K) hp1
     have ht2 := Nat.mul_le_mul_left 3040000 hp2
     have ht3 := Nat.mul_le_mul_left 10000 hp3
     have ht4 := Nat.mul_le_mul_left (F+1000) hpz
     change pre.time input+reductionBodyRealizer.iterate.time (N,initial)+10*(volume (N,initial)+1)≤ _
     nlinarith
   · have hv := hV N le_rfl
     change volume (reductionBody^[N] initial)≤ _
     have hm := Nat.mul_le_mul_left 304 hp4
     have hcoef : 304≤10000*K+F+4000000 := by omega
     exact hv.trans (hm.trans (Nat.mul_le_mul_right _ hcoef))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLInitialInvariant
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 theorem integer_row_norm {n L : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hB : ∀ i j,|B i j|≤(2:ℤ)^L) (i : Fin n) : ‖embed B i‖≤ n*(2:ℝ)^L := by
   have hnorm : ‖embed B i‖^2≤(n:ℝ)*((2:ℝ)^L)^2 := by
     rw [EuclideanSpace.real_norm_sq_eq]
     calc
       _≤∑ _j : Fin n,((2:ℝ)^L)^2 := by
         apply Finset.sum_le_sum
         intro j hj
         have hh : |(B i j:ℝ)|≤(2:ℝ)^L := by exact_mod_cast hB i j
         have hv := abs_le.mp hh
         change (B i j:ℝ)^2≤((2:ℝ)^L)^2
         nlinarith
       _=_ := by simp
   have hn : (1:ℝ)≤ n := by exact_mod_cast (show 1≤ n by have hh:=i.isLt; omega)
   have hn2 : (n:ℝ)≤(n:ℝ)^2 := by nlinarith
   have hprod := mul_le_mul_of_nonneg_right hn2 (sq_nonneg ((2:ℝ)^L))
   have hN : (0:ℝ)≤ n*(2:ℝ)^L := by positivity
   nlinarith [norm_nonneg (embed B i)]

 theorem initial_basis_invariant {n L H : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hb : LinearIndependent ℝ (embed B)) (hB : ∀ i j,|B i j|≤(2:ℤ)^L)
     (hL : L≤ H) (hJ : n*n+(n+2*L)*n≤ H) (hP : n*(n*n+(n+2*L)*n)≤ H) :
     BasisInvariant (embed B) H (embed B) ∧ potD (embed B)≤(2:ℝ)^H := by
   refine ⟨⟨hb,⟨B,rfl⟩,rfl,?_,?_⟩,?_⟩
   · intro k hk
     exact ⟨gram_ge_one B hb k hk,(gram_initial_upper B hB k hk).trans
       (pow_le_pow_right₀ (by norm_num) hJ)⟩
   · intro i
     have hn := integer_row_norm B hB i
     have hpow : (2:ℝ)^L≤(2:ℝ)^H := pow_le_pow_right₀ (by norm_num) hL
     calc
       _≤(n:ℝ)*(2:ℝ)^L := hn
       _≤(n:ℝ)*(2:ℝ)^H := mul_le_mul_of_nonneg_left hpow (by positivity)
       _≤(n+1:ℝ)*((2:ℝ)^H+1) := by
         have hp : (0:ℝ)≤2^H := by positivity
         have hn0 : (0:ℝ)≤ n := Nat.cast_nonneg _
         nlinarith
   · exact (potential_initial_upper B hb hB).trans (pow_le_pow_right₀ (by norm_num) hP)

 

 theorem encoded_exponent_bounds (S n L : ℕ) (hn : n≤ S) (hL : L≤ S) :
     L≤ encodedExponent S ∧ n*n+(n+2*L)*n≤ encodedExponent S ∧
       n*(n*n+(n+2*L)*n)≤ encodedExponent S := by
   have hS2 := Nat.mul_le_mul hn hn
   have hLn := Nat.mul_le_mul hL hn
   have hJ : n*n+(n+2*L)*n≤4*S^2 := by nlinarith
   have hp2 : S^2≤(S+1)^5 := (Nat.pow_le_pow_left (Nat.le_succ S) 2).trans
     (Nat.pow_le_pow_right (by omega : 1≤ S+1) (by omega))
   have hp3 : S^3≤(S+1)^5 := (Nat.pow_le_pow_left (Nat.le_succ S) 3).trans
     (Nat.pow_le_pow_right (by omega : 1≤ S+1) (by omega))
   have hp1 : S≤(S+1)^5 := by
     calc
       S≤ S+1 := Nat.le_succ S
       _≤(S+1)^5 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤ S+1) (by omega : 1≤5)
   have hpot := Nat.mul_le_mul hn hJ
   have hEq : S*(4*S^2)=4*S^3 := by ring
   rw [hEq] at hpot
   dsimp [encodedExponent]
   constructor
   · nlinarith
   constructor <;> nlinarith

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
 theorem volume_pair_eta {β γ : Type} [Coding β] [Coding γ] (s : β×γ) : volume s=volume s.1+volume s.2+1 := by cases s;exact volume_pair _ _
 
 
 
 
 
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

 theorem readWord_rest_volume (L : List Bool) : volume (readWord L).2≤ volume L := by
   have hh := readWord_volume L
   have hp := volume_pos (readWord L).1
   omega
 
 theorem readRational_rest_volume (L : List Bool) : volume (readRational L).2≤ volume L := by
   exact (readWord_rest_volume (readWord L.tail).2).trans ((readWord_rest_volume L.tail).trans (tailList_volume L))
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
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

 theorem readMany_remaining_volume (n : ℕ) (L : List Bool) : volume (readMany n L).2≤ volume L := by
   have h (j : ℕ) (s : BatchState) : volume (batchStep^[j] s).1≤ volume s.1 := by
     induction j with
     | zero => exact le_rfl
     | succ j ih =>
       rw [Function.iterate_succ_apply']
       exact (readRational_rest_volume (batchStep^[j] s).1).trans ih
   exact h n (L,[])

 
 
 theorem readMatrixRow_polynomial : PolyBound readMatrixRow := polynomial_comp
   (linear_polynomial (linear_pair linear_fst (linear_comp linear_snd linear_fst))) readMany_polynomial
 
 
 theorem readMatrixStep_polynomial : PolyBound readMatrixStepRealizer := polynomial_pair
   (linear_polynomial linear_fst)
   (polynomial_pair (polynomial_comp readMatrixRow_polynomial (linear_polynomial linear_snd))
     (polynomial_comp (polynomial_pair (polynomial_comp readMatrixRow_polynomial (linear_polynomial linear_fst))
       (linear_polynomial (linear_comp linear_snd linear_snd))) (linear_polynomial linear_cons)))

 theorem readMatrix_iterate_bound (C q : ℕ)
     (hrow : ∀ n L,volume (readMany n L).1≤ C*(volume n+volume L+2)^q)
     (s : MatrixReadState) (j : ℕ) :
     (readMatrixStep^[j] s).1=s.1 ∧ volume (readMatrixStep^[j] s).2.1≤ volume s.2.1 ∧
       volume (readMatrixStep^[j] s)≤ volume s+j*(C*(volume s.1+volume s.2.1+2)^q+1) := by
   induction j with
   | zero => simp
   | succ j ih =>
     let t := readMatrixStep^[j] s
     have hr := readMany_remaining_volume t.1 t.2.1
     have he := hrow t.1 t.2.1
     have he' : volume (readMany t.1 t.2.1).1≤ C*(volume s.1+volume s.2.1+2)^q := by
       rw [ih.1] at he ⊢
       exact he.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add_left ih.2.1 _) _) q))
     rw [Function.iterate_succ_apply']
     refine ⟨ih.1,hr.trans ih.2.1,?_⟩
     have hi := ih.2.2
     have ht : volume t=volume t.1+volume t.2.1+volume t.2.2+2 := by rw [volume_pair_eta t,volume_pair_eta t.2]; omega
     have hn : volume (readMatrixStep t)=volume t.1+volume (readMany t.1 t.2.1).2+
         volume (readMany t.1 t.2.1).1+volume t.2.2+3 := by simp only [readMatrixStep,volume_pair,volume_cons]; omega
     change volume (readMatrixStep t)≤ _
     nlinarith

 theorem readMatrix_iterate_polynomial : PolyBound readMatrixStepRealizer.iterate := by
   obtain ⟨C,q,hC,hR⟩ := readMany_polynomial
   have hrow : ∀ n L,volume (readMany n L).1≤ C*(volume n+volume L+2)^q := by
     intro n L
     have h := (hR (n,L)).2
     rw [volume_pair_eta (readMany n L)] at h
     simp only [volume_pair] at h
     have heq : volume n+volume L+1+1=volume n+volume L+2 := by omega
     rw [heq] at h
     omega
   apply polynomial_iterate_growth readMatrixStep_polynomial (C+10) (q+2)
   intro s j
   have h := (readMatrix_iterate_bound C q hrow s j).2.2
   let z := volume s+j+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hs : volume s≤ z := by dsimp [z]; omega
   have hj : j≤ z := by dsimp [z]; omega
   have hbase : volume s.1+volume s.2.1+2≤ z := by
     dsimp [z]
     rw [volume_pair_eta s,volume_pair_eta s.2]
     omega
   have hq := Nat.pow_le_pow_left hbase q
   have h1 : 1≤ z^q := one_le_pow₀ hz
   have hm := Nat.mul_le_mul hj (show C*(volume s.1+volume s.2.1+2)^q+1≤(C+1)*z^q by nlinarith)
   have he : z*((C+1)*z^q)=(C+1)*z^(q+1) := by rw [pow_succ]; ring
   rw [he] at hm
   have hp : z^(q+1)≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hl : z≤ z^(q+2) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+2)
   change volume (readMatrixStep^[j] s)≤(C+10)*z^(q+2)
   nlinarith [Nat.mul_le_mul_left (C+1) hp]

 
 
 theorem readMatrixRows_polynomial : PolyBound readMatrixRowsRealizer := polynomial_comp
   (polynomial_comp (linear_polynomial (linear_pair linear_fst (linear_pair linear_fst
     (linear_pair linear_snd (linear_constant ([] : List (List SignedWords))))))) readMatrix_iterate_polynomial)
   (polynomial_pair (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_snd)) reverse_polynomial_generic)
     (linear_polynomial (linear_comp linear_snd linear_fst)))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLBitProgramCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 
 theorem encodedExponent_polynomial : PolyBound encodedExponentRealizer :=
   polynomial_comp (polynomial_pair (linear_polynomial (linear_constant (100:ℕ)))
     (polynomial_comp (linear_polynomial natSucc_linear) naturalFifth_polynomial)) naturalProduct_polynomial
 
 
 theorem reductionCount_polynomial : PolyBound reductionCountRealizer :=
   polynomial_comp (polynomial_pair (linear_polynomial (linear_constant (4:ℕ)))
     (polynomial_comp encodedExponent_polynomial (linear_polynomial natSucc_linear))) naturalProduct_polynomial
 
 
 theorem parseIntegerMatrix_polynomial : PolyBound parseIntegerMatrixRealizer :=
   polynomial_comp (polynomial_comp readNatural_polynomial readMatrixRows_polynomial) (linear_polynomial linear_fst)
 
 
 theorem prepareReduction_polynomial : PolyBound prepareReductionRealizer :=
   polynomial_pair (polynomial_comp listLength_polynomial reductionCount_polynomial) parseIntegerMatrix_polynomial

 
 
 theorem serializeRow_polynomial : PolyBound serializeRowRealizer := by
   unfold serializeRowRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_mapList rationalBits_polynomial) flattenList_polynomial
 
 
 theorem serializePayload_polynomial : PolyBound serializePayloadRealizer := by
   unfold serializePayloadRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_mapList serializeRow_polynomial) flattenList_polynomial
 
 theorem serializeMatrix_polynomial : PolyBound serializeMatrixRealizer :=
   polynomial_comp (polynomial_pair (polynomial_comp listLength_polynomial naturalCode_polynomial)
     serializePayload_polynomial) appendBits_polynomial
 
 
 theorem finishReduction_polynomial : PolyBound finishReductionRealizer :=
   polynomial_comp (linear_polynomial linear_snd) serializeMatrix_polynomial
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.IntegerMatrixEncoding
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 theorem integerCode_bits (z : ℤ) : (integerCode z).bits=encodeRat (z:ℚ) := by
   simp [integerCode,RationalCode.bits,encodeRat]
 theorem integerCode_value (z : ℤ) : (integerCode z).value=(z:ℚ) := by simp [integerCode,RationalCode.value]
 theorem integerCode_den (z : ℤ) : 0< value (codeWords (integerCode z)).2.2 := by
   change 0< value (natBits 1)
   rw [value_natBits]
   omega
 theorem integerCode_canonical (z : ℤ) : SignedCanonical (codeWords (integerCode z)) := by
   change signedReduced (codeWords (integerCode z))=codeWords (integerCode z)
   rw [signedReduced_canonical _ (integerCode_den z),signedFractionValue_code,integerCode_value]
   simp only [Rat.num_intCast,Rat.den_intCast,codeWords,integerCode]
   rfl

 
 

 theorem integerWords_rep {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
     ∀ i,RepresentsVector (integerWords B i) (LLLBounds.embed B i) := by
   intro i
   refine ⟨fun j => codeWords (integerCode (B i j)),rfl,fun j => integerCode_den _,?_⟩
   intro j
   rw [signedFractionValue_code,integerCode_value,Rat.cast_intCast]
   rfl
 theorem integerWords_canonical {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
     ∀ i,VectorCanonical (integerWords B i) := by
   intro i s hs
   obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hs
   exact integerCode_canonical _

 theorem integerMatrixInput_length {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
     (integerMatrixInput B).length=(encodeNat n).length+∑ i,∑ j,(encodeRat (B i j:ℚ)).length := by
   simp [integerMatrixInput,List.length_flatten,List.map_ofFn,List.sum_ofFn]
 theorem integer_encoding_positive (z : ℤ) : 1≤(encodeRat (z:ℚ)).length := by
   simp only [encodeRat,Rat.num_intCast,Rat.den_intCast,encodeInt,List.length_append,List.length_singleton]
   omega
 theorem integerMatrixInput_order {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : n≤(integerMatrixInput B).length := by
   have hh : n*n≤∑ i,∑ j,(encodeRat (B i j:ℚ)).length := by
     calc
       n*n=∑ _i : Fin n,∑ _j : Fin n,1 := by simp
       _≤ _ := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => integer_encoding_positive _))
   rw [integerMatrixInput_length]
   have hn : n≤ n*n := Nat.le_mul_self n
   omega
 theorem integerMatrixInput_entries {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
     ∀ i j,|B i j|≤(2:ℤ)^((integerMatrixInput B).length) := by
   intro i j
   have hlocal : (natBits (B i j).natAbs).length≤(encodeRat (B i j:ℚ)).length := by
     simp only [encodeRat,Rat.num_intCast,Rat.den_intCast,encodeInt,encodeNat,
       List.length_append,List.length_replicate,List.length_singleton]
     omega
   have hi : (encodeRat (B i j:ℚ)).length≤∑ k,∑ l,(encodeRat (B k l:ℚ)).length := by
     have h1 : (encodeRat (B i j:ℚ)).length≤∑ l,(encodeRat (B i l:ℚ)).length :=
       Finset.single_le_sum (f := fun l : Fin n => (encodeRat (B i l:ℚ)).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
     have h2 : (∑ l,(encodeRat (B i l:ℚ)).length)≤∑ k,∑ l,(encodeRat (B k l:ℚ)).length :=
       Finset.single_le_sum (f := fun k : Fin n => ∑ l,(encodeRat (B k l:ℚ)).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
     exact h1.trans h2
   have hwhole : (natBits (B i j).natAbs).length≤(integerMatrixInput B).length := by
     rw [integerMatrixInput_length]
     omega
   have hv := (value_lt (natBits (B i j).natAbs)).le
   rw [value_natBits] at hv
   have hbound := hv.trans (Nat.pow_le_pow_right (by omega : 1≤2) hwhole)
   have hc : ((B i j).natAbs:ℤ)≤(2:ℤ)^((integerMatrixInput B).length) := by exact_mod_cast hbound
   simpa only [Int.natCast_natAbs] using hc

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

 theorem readMatrixStep_codes (n : ℕ) (rows : List (List RationalCode))
     (hlen : ∀ row∈rows,row.length=n) (rest : List Bool) (acc : List SignedVector) :
     readMatrixStep^[rows.length] (n,(rows.flatMap (fun row => row.flatMap RationalCode.bits)++rest,acc))=
       (n,(rest,(rows.map (List.map codeWords)).reverse++acc)) := by
   induction rows generalizing acc with
   | nil => simp
   | cons row rows ih =>
     have hr := hlen row (by simp)
     have hs : ∀ a∈rows,a.length=n := by intro a ha; exact hlen a (by simp [ha])
     rw [List.length_cons,Function.iterate_succ_apply]
     simp only [List.flatMap_cons,List.append_assoc,readMatrixStep]
     rw [← hr,readMany_codes,hr]
     rw [ih hs,List.map_cons,List.reverse_cons]
     simp only [List.append_assoc,List.singleton_append]

 theorem readMatrixRows_codes (n : ℕ) (rows : List (List RationalCode))
     (hrows : rows.length=n) (hlen : ∀ row∈rows,row.length=n) (rest : List Bool) :
     readMatrixRows (n,rows.flatMap (fun row => row.flatMap RationalCode.bits)++rest)=
       (rows.map (List.map codeWords),rest) := by
   dsimp only [readMatrixRows]
   rw [← hrows,readMatrixStep_codes rows.length rows (by simpa only [hrows] using hlen)]
   simp

 theorem integerMatrixInput_rows {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
     integerMatrixInput B=encodeNat n++
       (List.ofFn (fun i => List.ofFn (fun j => integerCode (B i j)))).flatMap
         (fun row => row.flatMap RationalCode.bits) := by
   simp only [integerMatrixInput,List.flatMap_def,List.map_ofFn,Function.comp_def,integerCode_bits]

 theorem parseIntegerMatrix_correct_raw {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
     readMatrixRows (readNatural (integerMatrixInput B))=(List.ofFn (integerWords B),[]) := by
   have hn := integerMatrixInput_order B
   have hnat : n≤(integerMatrixInput B).length+1 := by omega
   rw [integerMatrixInput_rows] at hnat ⊢
   rw [readNatural_encoded n _ hnat]
   have hr := readMatrixRows_codes n
     (List.ofFn (fun i => List.ofFn (fun j => integerCode (B i j))))
     (by simp) (by intro row hrow; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow; simp) []
   simp only [List.append_nil,List.map_ofFn] at hr
   have he : (List.ofFn (fun i => List.ofFn (fun j => integerCode (B i j)))).map (List.map codeWords)=List.ofFn (integerWords B) := by
     rw [List.map_ofFn]
     apply congrArg List.ofFn
     funext i
     change (List.ofFn (fun j => integerCode (B i j))).map codeWords=List.ofFn (fun j => codeWords (integerCode (B i j)))
     rw [List.map_ofFn]
     rfl
   rw [← he,List.map_ofFn]
   exact hr

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

 

 

 theorem parseIntegerMatrix_correct {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
     parseIntegerMatrix (integerMatrixInput B)=List.ofFn (integerWords B) :=
   congrArg Prod.fst (parseIntegerMatrix_correct_raw B)

 theorem integer_input_invariant {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hb : LinearIndependent ℝ (embed B)) :
     BasisInvariant (embed B) (encodedExponent (integerMatrixInput B).length) (embed B) ∧
       potD (embed B)≤(2:ℝ)^(encodedExponent (integerMatrixInput B).length) := by
   have hs := encoded_exponent_bounds (integerMatrixInput B).length n (integerMatrixInput B).length
     (integerMatrixInput_order B) le_rfl
   exact initial_basis_invariant B hb (integerMatrixInput_entries B) hs.1 hs.2.1 hs.2.2

 

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

 theorem prepareReduction_integer {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
     prepareReduction (integerMatrixInput B)=
       (4*(encodedExponent (integerMatrixInput B).length+1),List.ofFn (integerWords B)) := by
   simp only [prepareReduction,parseIntegerMatrix_correct,reductionCount]

 theorem integerLLL_loop_clock :
     ∃ C q : ℕ,0< C ∧ ∀ n (B : Matrix (Fin n) (Fin n) ℤ),
       LinearIndependent ℝ (embed B) →
       reductionLoopRealizer.time (prepareReduction (integerMatrixInput B))≤
         C*(volume (prepareReduction (integerMatrixInput B))+1)^q ∧
       volume (reductionLoop (prepareReduction (integerMatrixInput B)))≤
         C*(volume (prepareReduction (integerMatrixInput B))+1)^q := by
   obtain ⟨C,q,hC,ht⟩ := reductionLoop_polynomial_time
   refine ⟨C*4^q,q,by positivity,?_⟩
   intro n B hb
   let H := encodedExponent (integerMatrixInput B).length
   let A := integerWords B
   let input := prepareReduction (integerMatrixInput B)
   have heq : input=(4*(H+1),List.ofFn A) := prepareReduction_integer B
   have hh := ht n H (4*(H+1)) (embed B) (integer_input_invariant B hb).1 A
     (integerWords_rep B) (integerWords_canonical B)
   rw [← heq] at hh
   have hv : volume input=2*(4*(H+1))+1+volume (List.ofFn A)+1 := by rw [heq,volume_pair,volume_nat]
   have hn : n≤ volume (List.ofFn A) := by simpa only [List.length_ofFn] using length_volume (List.ofFn A)
   have hbase : volume input+n+H+4≤4*(volume input+1) := by omega
   have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q)
   rw [mul_pow] at hp
   have hm : C*(4^q*(volume input+1)^q)=(C*4^q)*(volume input+1)^q := by ring
   rw [hm] at hp
   exact ⟨hh.1.trans hp,hh.2.trans hp⟩

 theorem integerLLL_core_clock :
     ∃ C q : ℕ,0< C ∧ ∀ n (B : Matrix (Fin n) (Fin n) ℤ),
       LinearIndependent ℝ (embed B) →
       (prepareReductionRealizer.comp reductionLoopRealizer).time (integerMatrixInput B)≤
         C*(volume (integerMatrixInput B)+1)^q ∧
       volume (reductionLoop (prepareReduction (integerMatrixInput B)))≤
         C*(volume (integerMatrixInput B)+1)^q := by
   obtain ⟨A,p,hA,hpre⟩ := prepareReduction_polynomial
   obtain ⟨D,q,hD,hloop⟩ := integerLLL_loop_clock
   refine ⟨D*(A+1)^q+20*A+20,p+(p+1)*q+2,by positivity,?_⟩
   intro n B hb
   let L := integerMatrixInput B
   let z := volume L+1
   let v := volume (prepareReduction L)
   have hz : 1≤ z := by dsimp [z]; omega
   have hi := hpre L
   have hl := hloop n B hb
   have hbase : v+1≤ v+z := by omega
   have htime := hl.1.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hbase q))
   have hout := hl.2.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hbase q))
   have hpipe := RuntimeMath.polynomial_pipeline_clock z A p D q
     (prepareReductionRealizer.time L) v (reductionLoopRealizer.time (prepareReduction L)) hz hi.1 hi.2 htime
   have hopipe := RuntimeMath.polynomial_pipeline_clock z A p D q
     (prepareReductionRealizer.time L) v (volume (reductionLoop (prepareReduction L))) hz hi.1 hi.2 hout
   constructor
   · rw [Realizer.time_comp]
     exact hpipe
   · change volume (reductionLoop (prepareReduction L))≤(D*(A+1)^q+20*A+20)*z^(p+(p+1)*q+2)
     omega

 theorem integerLLL_polynomial_time :
     ∃ C q : ℕ,0< C ∧ ∀ n (B : Matrix (Fin n) (Fin n) ℤ),
       LinearIndependent ℝ (embed B) →
       integerLLLRealizer.time (integerMatrixInput B)≤ C*(volume (integerMatrixInput B)+1)^q ∧
       volume (integerLLL (integerMatrixInput B))≤ C*(volume (integerMatrixInput B)+1)^q := by
   obtain ⟨A,p,hA,hcore⟩ := integerLLL_core_clock
   obtain ⟨D,q,hD,hpost⟩ := finishReduction_polynomial
   refine ⟨D*(A+1)^q+20*A+20,p+(p+1)*q+2,by positivity,?_⟩
   intro n B hb
   let L := integerMatrixInput B
   let z := volume L+1
   let v := volume (reductionLoop (prepareReduction L))
   have hz : 1≤ z := by dsimp [z]; omega
   have hi := hcore n B hb
   have hl := hpost (reductionLoop (prepareReduction L))
   have hbase : v+1≤ v+z := by omega
   have htime := hl.1.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hbase q))
   have hout := hl.2.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hbase q))
   have hpipe := RuntimeMath.polynomial_pipeline_clock z A p D q
     ((prepareReductionRealizer.comp reductionLoopRealizer).time L) v
       (finishReductionRealizer.time (reductionLoop (prepareReduction L))) hz hi.1 hi.2 htime
   have hopipe := RuntimeMath.polynomial_pipeline_clock z A p D q
     ((prepareReductionRealizer.comp reductionLoopRealizer).time L) v
       (volume (finishReduction (reductionLoop (prepareReduction L)))) hz hi.1 hi.2 hout
   constructor
   · have he := Realizer.time_comp (prepareReductionRealizer.comp reductionLoopRealizer) finishReductionRealizer L
     simp only [Function.comp_apply] at he
     have ht : integerLLLRealizer.time L=
         (prepareReductionRealizer.comp reductionLoopRealizer).time L+
           finishReductionRealizer.time (reductionLoop (prepareReduction L))+10*(v+1) := he
     rw [ht]
     exact hpipe
   · have hbound : volume (finishReduction (reductionLoop (prepareReduction L)))≤(D*(A+1)^q+20*A+20)*z^(p+(p+1)*q+2) := by omega
     simpa only [integerLLL,Function.comp_apply,L,z] using hbound

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

open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds EdgeSublinearMWIS.Main.LLLBounds

theorem solution :
    ∃ C q : ℕ,0 < C ∧ ∀ n (B : Matrix (Fin n) (Fin n) ℤ),
      LinearIndependent ℝ (embed B) →
      integerLLLRealizer.time (integerMatrixInput B) ≤ C*(volume (integerMatrixInput B)+1)^q ∧
      volume (integerLLL (integerMatrixInput B)) ≤ C*(volume (integerMatrixInput B)+1)^q := by
  exact integerLLL_polynomial_time
