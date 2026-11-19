-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.exact_binary_oracle_feasibility
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:56:55.97549+00:00
-- url     : https://prove2.me/submissions/f20ca005-4869-4fcf-81ca-da2479840de2

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
import Theorems.Thm_EdgeSublinearMWIS_Main_integer_lll_bit_clock
import Theorems.Thm_EdgeSublinearMWIS_Main_binary_oracle_prefix_invariant
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
theorem admissible_prefix_sound {N : ℕ} (E : Program) (hE : ImplementsBinaryOracle E)
    (bound : Polynomial ℕ) (Orig : Finset (Fin N → Bool))
    (qs : List (Fin N → ℚ)) (cuts : List (RationalHalfspace N))
    (hadm : AdmissibleDialogue E bound N Orig qs cuts) (i : ℕ) (hi : i ≤ cuts.length) :
    CoreGeometry N Orig (oracleTranscriptState (cuts.take i)).2 ∧
      ((oracleTranscriptState (cuts.take i)).1=true → binaryHull Orig=∅) :=
  EdgeSublinearMWIS.Main.binary_oracle_prefix_invariant E hE bound Orig qs cuts hadm i hi
end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds EdgeSublinearMWIS.Main.LLLBounds
theorem integerLLL_polynomial_time :
    ∃ C q : ℕ,0 < C ∧ ∀ n (B : Matrix (Fin n) (Fin n) ℤ),
      LinearIndependent ℝ (embed B) →
      integerLLLRealizer.time (integerMatrixInput B) ≤ C*(volume (integerMatrixInput B)+1)^q ∧
      volume (integerLLL (integerMatrixInput B)) ≤ C*(volume (integerMatrixInput B)+1)^q :=
  EdgeSublinearMWIS.Main.integer_lll_bit_clock
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

 theorem natBits_length (n : ℕ) : (natBits n).length ≤ n := by
  simpa only [natBits, List.length_map] using
    (Nat.digits_length_le_iff (by decide : 1 < 2) n).mpr (show n < 2 ^ n from Nat.lt_two_pow_self)

 theorem encodeNat_length (n : ℕ) : (encodeNat n).length ≤ 2 * n + 1 := by
  have h := natBits_length n
  simp only [encodeNat, List.length_append, List.length_replicate, List.length_singleton]
  omega

 

 

 

 

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

 
 
 theorem valueStep_polynomial : PolyBound valueStepRealizer := by
   unfold valueStepRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair
     (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_snd)) BinaryGcd.nat_add_polynomial)
     (linear_polynomial (linear_comp linear_fst boolNat_linear))) BinaryGcd.nat_add_polynomial
 
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

 
 
 
 
 
 

 
 theorem map_range_ofFn {α : Type} (n : ℕ) (f : ℕ → α) : (List.range n).map f=List.ofFn (fun i : Fin n => f i.val) := by
   rw [← finRange_val n,List.map_map]
   simp only [List.finRange,List.map_ofFn,Function.comp_def,id_eq]
 
 

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

 
 theorem arrayPairAt_polynomial (a : α) (b : β) : PolyBound (arrayPairAt a b) := polynomial_pair
   (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) linear_fst)) (lookupList_polynomial a))
   (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd linear_snd) linear_fst)) (lookupList_polynomial b))
 
 
 theorem arrayPairs_polynomial (a : α) (b : β) : PolyBound (arrayPairsRealizer a b) := polynomial_comp
   (polynomial_pair (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) listLength_polynomial) range_polynomial)
     (linear_polynomial linear_id)) (polynomial_mapEnvironment (arrayPairAt_polynomial a b))
 theorem arrayPairs_ofFn {n : ℕ} (a : α) (b : β) (f : Fin n → α) (g : Fin n → β) :
     arrayPairs a b (List.ofFn f,List.ofFn g)=List.ofFn (fun i => (f i,g i)) := by
   simp only [arrayPairs,List.length_ofFn]
   rw [map_range_ofFn]
   congr 1
   funext i
   rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn]
   rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn]
   simp [i.isLt]

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
 

 
 
 theorem vectorAdd_polynomial : PolyBound vectorAddRealizer :=
   polynomial_comp vectorPairs_polynomial (polynomial_mapList canonicalAdd_polynomial)
 
 
 theorem vectorSub_polynomial : PolyBound vectorSubRealizer :=
   polynomial_comp vectorPairs_polynomial (polynomial_mapList canonicalSub_polynomial)
 
 
 theorem vectorScale_polynomial : PolyBound vectorScaleRealizer := polynomial_mapEnvironment canonicalMul_polynomial

 
 theorem vectorSub_ofFn {n : ℕ} (a b : Fin n → SignedWords) :
     vectorSub (List.ofFn a,List.ofFn b)=List.ofFn (fun i => canonicalSub (a i,b i)) := by
   rw [vectorSub,vectorPairs_ofFn,List.map_ofFn]
   rfl
 theorem vectorAdd_ofFn {n : ℕ} (a b : Fin n → SignedWords) :
     vectorAdd (List.ofFn a,List.ofFn b)=List.ofFn (fun i => canonicalAdd (a i,b i)) := by
   rw [vectorAdd,vectorPairs_ofFn,List.map_ofFn]
   rfl
 theorem vectorScale_ofFn {n : ℕ} (a : Fin n → SignedWords) (b : SignedWords) :
     vectorScale (List.ofFn a,b)=List.ofFn (fun i => canonicalMul (a i,b)) := by
   rw [vectorScale,List.map_ofFn]
   rfl

 
 
 
 
 
 

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

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedFloorCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 theorem floorDivision_polynomial : PolyBound floorDivisionRealizer := polynomial_comp (linear_polynomial linear_snd) divide_polynomial
 
 
 theorem floorRoundUp_polynomial : PolyBound floorRoundUpRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial linear_fst)
     (polynomial_comp (polynomial_comp (polynomial_comp floorDivision_polynomial (linear_polynomial linear_snd)) trim_polynomial) (linear_polynomial nonempty_linear)))
   (linear_polynomial linear_and)
 
 
 theorem floorIncrement_polynomial : PolyBound floorIncrementRealizer := polynomial_comp
   (polynomial_pair floorRoundUp_polynomial (linear_polynomial linear_id))
   (polynomial_choose (linear_polynomial (linear_constant [true])) (linear_polynomial (linear_constant ([]:List Bool))))
 
 
 theorem floorMagnitude_polynomial : PolyBound floorMagnitudeRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp floorDivision_polynomial (linear_polynomial linear_fst)) floorIncrement_polynomial) sumWords_polynomial
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedFloorMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 theorem trim_empty_iff_zero (A : List Bool) : (trim A).isEmpty=true ↔ value A=0 := by
   constructor
   · intro h
     have he : trim A=[] := List.isEmpty_iff.mp h
     have hv := trim_value A
     rw [he] at hv
     simpa only [value] using hv.symm
   · intro h
     by_contra hn
     have hne : trim A≠[] := by intro he; simp [he] at hn
     have hp := BinaryGcd.value_positive (trim A) (trim_idem A) hne
     rw [trim_value,h] at hp
     omega

 theorem floorRoundUp_iff (s : SignedWords) (hd : 0< value s.2.2) :
     floorRoundUp s=true ↔ s.1=true ∧ value s.2.1%value s.2.2≠0 := by
   simp only [floorRoundUp,Bool.and_eq_true,Bool.not_eq_true']
   have he : (trim (floorDivision s).2).isEmpty=false ↔ value s.2.1%value s.2.2≠0 := by
     rw [Bool.eq_false_iff]
     have hz : (trim (floorDivision s).2).isEmpty=true ↔ value s.2.1%value s.2.2=0 := by
       simpa only [floorDivision,(divide_value _ _ hd).2] using trim_empty_iff_zero (floorDivision s).2
     exact not_congr hz
   rw [he]

 theorem floorMagnitude_value (s : SignedWords) (hd : 0< value s.2.2) :
     value (floorMagnitude s)=value s.2.1/value s.2.2+
       if s.1=true ∧ value s.2.1%value s.2.2≠0 then 1 else 0 := by
   rw [floorMagnitude,sumWords_value,floorDivision,(divide_value _ _ hd).1]
   dsimp only [floorIncrement]
   by_cases h : floorRoundUp s=true
   · rw [if_pos h,if_pos ((floorRoundUp_iff s hd).mp h)]
     simp [value]
   · rw [if_neg h,if_neg (by intro hh; exact h ((floorRoundUp_iff s hd).mpr hh))]
     simp [value]

 theorem floor_nat_fraction (a d : ℕ) (_hd : 0< d) :
     Int.floor ((a:ℚ)/d)=(a/d:ℕ) := by
   rw [Rat.floor_natCast_div_natCast]
   rfl

 theorem floor_neg_nat_fraction (a d : ℕ) (hd : 0< d) :
     Int.floor (-(a:ℚ)/d)= -((a/d+(if a%d≠0 then 1 else 0):ℕ):ℤ) := by
   have hdZ : (0:ℤ)< d := by exact_mod_cast hd
   have hdiv : ((d:ℤ)∣(a:ℤ)) ↔ a%d=0 := by
     rw [Int.natCast_dvd_natCast,Nat.dvd_iff_mod_eq_zero]
   rw [←Int.cast_natCast a,←Int.cast_neg,Rat.floor_intCast_div_natCast,Int.neg_ediv]
   rw [Int.sign_eq_one_of_pos hdZ]
   by_cases he : a%d=0
   · simp only [hdiv,he,if_true,not_true_eq_false,if_false,Nat.add_zero,sub_zero]
     rfl
   · simp only [hdiv,he,if_false,not_false_eq_true,if_true,Nat.cast_add,Nat.cast_one]
     rw [Int.natCast_ediv]
     simp only [if_pos he,Nat.cast_one]
     ring

 
 theorem signedFloorWords_correct (s : SignedWords) (hd : 0< value s.2.2) :
     signedFractionValue (signedFloorWords s)=(Int.floor (signedFractionValue s):ℚ) := by
   rcases s with ⟨b,N,D⟩
   rw [signedFloorWords,signedFractionValue]
   simp only [value,Bool.toNat_true,Nat.mul_zero,Nat.add_zero,Int.cast_one,div_one]
   cases b
   · rw [signedValue,floorMagnitude_value _ hd]
     simp only [Bool.false_eq_true,false_and,if_false,Nat.add_zero,signedFractionValue,signedValue,Int.cast_natCast]
     rw [floor_nat_fraction _ _ hd]
     simp only [Nat.cast_one,div_one]
     simp only [Int.cast_natCast]
   · rw [signedValue,floorMagnitude_value _ hd]
     simp only [if_true,true_and,signedFractionValue,signedValue,Int.cast_natCast,Int.cast_neg]
     rw [floor_neg_nat_fraction _ _ hd]
     simp only [Int.cast_neg,Int.cast_natCast,Nat.cast_one,div_one]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.IntegerRootStep
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.IntegerRoot
 
 theorem step_square (root rem digit : ℕ) :
     (step root rem digit).1^2+(step root rem digit).2=4*(root^2+rem)+digit := by
   dsimp only [step]
   split_ifs with h
   · simp only
     ring
   · have hh : 4*root+1≤4*rem+digit := by omega
     have hs := Nat.sub_add_cancel hh
     simp only
     nlinarith
 theorem step_remainder (root rem digit : ℕ) (hr : rem≤2*root) (hd : digit≤3) :
     (step root rem digit).2≤2*(step root rem digit).1 := by
   dsimp only [step]
   split_ifs with h
   · simp only
     omega
   · simp only
     omega
 theorem square_characterization (N root rem : ℕ) (hN : N=root^2+rem) (hr : rem≤2*root) : Nat.sqrt N=root := by
   apply le_antisymm
   · apply Nat.le_of_lt_succ
     apply Nat.sqrt_lt.mpr
     nlinarith
   · apply Nat.le_sqrt.mpr
     nlinarith
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
 theorem difference_length_le (A B : List Bool) : (BinarySubtract.difference A B).length≤ A.length := by
   have hv : value (BinarySubtract.difference A B)<2^A.length :=
     (by rw [BinarySubtract.difference_value]; exact (Nat.sub_le _ _).trans_lt (value_lt A))
   have hh := trim_length_of_lt _ _ hv
   rwa [difference_canonical] at hh
 
 
 
 
 
 
 theorem rootNextRemainder_linear : Linear rootNextRemainderRealizer := linear_comp
   (linear_pair (linear_comp linear_fst linear_fst) (linear_comp (linear_pair (linear_comp linear_fst linear_snd) (linear_comp linear_snd linear_snd)) linear_cons)) linear_cons
 theorem rootTrial_linear : Linear rootTrialRealizer := linear_comp
   (linear_pair (linear_constant true) (linear_comp (linear_pair (linear_constant false) (linear_comp linear_snd linear_fst)) linear_cons)) linear_cons
 
 
 theorem rootTakeBit_polynomial : PolyBound rootTakeBitRealizer := polynomial_comp
   (polynomial_comp (linear_polynomial (linear_pair rootNextRemainder_linear rootTrial_linear)) BinarySubtract.less_polynomial) (linear_polynomial linear_not)
 
 theorem rootDifference_polynomial : PolyBound rootDifferenceRealizer := polynomial_comp
   (linear_polynomial (linear_pair rootNextRemainder_linear rootTrial_linear)) BinarySubtract.difference_polynomial
 
 
 theorem rootWordStep_polynomial : PolyBound rootWordStepRealizer := polynomial_pair
   (polynomial_comp (polynomial_pair rootTakeBit_polynomial (linear_polynomial (linear_comp linear_snd linear_fst))) (linear_polynomial linear_cons))
   (polynomial_comp (polynomial_pair rootTakeBit_polynomial (linear_polynomial linear_id))
     (polynomial_choose rootDifference_polynomial (linear_polynomial rootNextRemainder_linear)))
 theorem rootWordStep_length (s : RootStepWords) :
     (rootWordStep s).1.length+(rootWordStep s).2.length≤ s.2.1.length+s.2.2.length+3 := by
   have hh := difference_length_le (rootNextRemainder s) (rootTrial s)
   unfold rootWordStep
   split_ifs <;> simp only [List.length_cons,rootNextRemainder] at hh ⊢ <;> omega
 theorem rootWordStep_values (s : RootStepWords) :
     (value (rootWordStep s).1,value (rootWordStep s).2)=
       IntegerRoot.step (value s.2.1) (value s.2.2) (s.1.1.toNat+2*s.1.2.toNat) := by
   have hnext : value (rootNextRemainder s)=4*value s.2.2+(s.1.1.toNat+2*s.1.2.toNat) := by simp only [rootNextRemainder,value];ring
   have htrial : value (rootTrial s)=4*value s.2.1+1 := by simp only [rootTrial,value,Bool.toNat_true,Bool.toNat_false];ring
   have hless : BinarySubtract.less (rootNextRemainder s) (rootTrial s)=
       decide (4*value s.2.2+(s.1.1.toNat+2*s.1.2.toNat)<4*value s.2.1+1) := by
     apply Bool.eq_iff_iff.mpr
     simpa only [decide_eq_true_eq,hnext,htrial] using BinarySubtract.less_iff (rootNextRemainder s) (rootTrial s)
   by_cases h : 4*value s.2.2+(s.1.1.toNat+2*s.1.2.toNat)<4*value s.2.1+1
   · simp only [rootWordStep,rootTakeBit,hless,h,decide_true,Bool.not_true,if_false,value,Bool.toNat_false,Nat.zero_add,IntegerRoot.step]
     simp only [h,if_true,hnext,Bool.false_eq_true,if_false]
   · simp only [rootWordStep,rootTakeBit,hless,h,decide_false,Bool.not_false,if_true,value,Bool.toNat_true,IntegerRoot.step]
     simp only [h,if_false,BinarySubtract.difference_value,hnext,htrial]
     congr 1
     omega
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryPairs
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 theorem quarterFull_linear : Linear quarterFull := linear_pair (linear_constant false)
   (linear_pair (linear_constant false) (linear_comp (linear_pair
     (linear_pair (linear_comp (linear_comp linear_snd linear_snd) linear_fst) linear_fst)
     (linear_comp (linear_comp linear_snd linear_snd) linear_snd)) linear_cons))
 theorem quarterHalf_linear : Linear quarterHalf := linear_pair (linear_constant true)
   (linear_pair linear_fst (linear_comp (linear_comp linear_snd linear_snd) linear_snd))
 
 theorem quarterStep_linear : Linear quarterStepRealizer := by
   unfold quarterStepRealizer
   apply linear_congr
   exact linear_comp (linear_pair (linear_comp linear_snd linear_fst) linear_id) (linear_choose quarterFull_linear quarterHalf_linear)
 theorem quarterStep_volume (s : Bool×QuarterState) : volume (quarterStep s)≤ volume s.2+12 := by
   rcases s with ⟨b,w,c,acc⟩
   cases b <;> cases w <;> cases c <;> simp [quarterStep,volume_pair,volume_cons] <;> omega
 theorem quarterFold_volume (L : List Bool) (s : QuarterState) :
     volume (L.foldl (fun s b => quarterStep (b,s)) s)≤ volume s+12*L.length := by
   induction L generalizing s with
   | nil => simp
   | cons b L ih =>
     rw [List.foldl_cons]
     have hi := ih (quarterStep (b,s))
     have hs := quarterStep_volume (b,s)
     change volume (quarterStep (b,s))≤ volume s+12 at hs
     simp only [List.length_cons]
     omega
 theorem quarterFold_polynomial : PolyBound quarterStepRealizer.fold := by
   apply polynomial_fold_bounded (linear_polynomial quarterStep_linear) 13
   intro L s j hj
   have hh := quarterFold_volume (L.take j) s
   have hl := length_volume L
   simp only [List.length_take] at hh
   simp only [volume_pair]
   omega
 
 
 theorem quarterFinish_linear : Linear quarterFinishRealizer := by
   unfold quarterFinishRealizer
   apply linear_congr
   exact linear_comp (linear_pair linear_fst linear_id)
     (linear_choose (linear_comp (linear_pair (linear_pair (linear_comp linear_snd linear_fst) (linear_constant false))
       (linear_comp linear_snd linear_snd)) linear_cons) (linear_comp linear_snd linear_snd))
 
 
 theorem quarterPairs_polynomial : PolyBound quarterPairsRealizer := polynomial_comp
   (polynomial_comp (linear_polynomial (linear_pair linear_id (linear_constant (false,(false,([] : List (Bool×Bool))))))) quarterFold_polynomial)
   (linear_polynomial quarterFinish_linear)
 
 theorem quarterPairs_acc (L : List Bool) (acc : List (Bool×Bool)) :
     quarterFinish (L.foldl (fun s b => quarterStep (b,s)) (false,(false,acc)))=(quarterLittle L).reverse++acc := by
   induction L using List.twoStepInduction generalizing acc with
   | nil => rfl
   | singleton b => rfl
   | cons_cons b c L ih ih2 =>
     simp only [List.foldl_cons,quarterStep,Bool.false_eq_true,if_false,if_true]
     change quarterFinish (L.foldl (fun s b => quarterStep (b,s)) (false,(false,(b,c)::acc)))=_
     rw [ih]
     simp only [quarterLittle,List.reverse_cons,List.append_assoc,List.singleton_append]
 theorem quarterPairs_eq (L : List Bool) : quarterPairs L=(quarterLittle L).reverse := by
   simpa only [quarterPairs,List.append_nil] using quarterPairs_acc L []
 
 theorem quarterValue_little (L : List Bool) : quarterValue (quarterLittle L)=value L := by
   induction L using List.twoStepInduction with
   | nil => rfl
   | singleton b => simp [quarterLittle,quarterValue,value]
   | cons_cons b c L ih ih2 => simp only [quarterLittle,quarterValue,ih,value];ring
 theorem quarterValue_fold (L : List (Bool×Bool)) :
     L.reverse.foldl (fun N d => 4*N+(d.1.toNat+2*d.2.toNat)) 0=quarterValue L := by
   induction L with
   | nil => rfl
   | cons d L ih =>
     rw [List.reverse_cons,List.foldl_append,ih]
     simp only [List.foldl_cons,List.foldl_nil,quarterValue]
     ring
 theorem quarterPairs_value (L : List Bool) :
     (quarterPairs L).foldl (fun N d => 4*N+(d.1.toNat+2*d.2.toNat)) 0=value L := by
   rw [quarterPairs_eq,quarterValue_fold,quarterValue_little]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryRoot
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 theorem rootWordFold_length (L : List (Bool×Bool)) (s : RootWords) :
     (rootWordFold L s).1.length+(rootWordFold L s).2.length≤ s.1.length+s.2.length+3*L.length := by
   induction L generalizing s with
   | nil => simp [rootWordFold]
   | cons d L ih =>
     change (rootWordFold L (rootWordStep (d,s))).1.length+(rootWordFold L (rootWordStep (d,s))).2.length≤ _
     have hi := ih (rootWordStep (d,s))
     have hs := rootWordStep_length (d,s)
     change (rootWordStep (d,s)).1.length+(rootWordStep (d,s)).2.length≤ s.1.length+s.2.length+3 at hs
     simp only [List.length_cons]
     omega
 theorem rootWordFold_polynomial : PolyBound rootWordStepRealizer.fold := by
   apply polynomial_fold_bounded rootWordStep_polynomial 20
   intro L s j hj
   let t := rootWordFold (L.take j) s
   have hlen := rootWordFold_length (L.take j) s
   change t.1.length+t.2.length≤ s.1.length+s.2.length+3*(L.take j).length at hlen
   have ht1 := BinaryAdder.volume_bits t.1
   have ht2 := BinaryAdder.volume_bits t.2
   have htv : volume t=volume t.1+volume t.2+1 := by cases t;exact volume_pair _ _
   have hs1 := bits_length_volume s.1
   have hs2 := bits_length_volume s.2
   have hsv : volume s=volume s.1+volume s.2+1 := by cases s;exact volume_pair _ _
   have hL := length_volume L
   change volume t≤20*(volume (L,s)+1)
   simp only [volume_pair,List.length_take] at hlen ⊢
   omega
 
 theorem rootWordFold_values (L : List (Bool×Bool)) (s : RootWords) :
     (value (rootWordFold L s).1,value (rootWordFold L s).2)=L.foldl rootNatStep (value s.1,value s.2) := by
   induction L generalizing s with
   | nil => rfl
   | cons d L ih =>
     change (value (rootWordFold L (rootWordStep (d,s))).1,value (rootWordFold L (rootWordStep (d,s))).2)=_
     rw [ih,rootWordStep_values]
     rfl
 theorem rootNatFold_square (L : List (Bool×Bool)) (s : ℕ×ℕ) :
     (L.foldl rootNatStep s).1^2+(L.foldl rootNatStep s).2=
       L.foldl (fun N d => 4*N+(d.1.toNat+2*d.2.toNat)) (s.1^2+s.2) := by
   induction L generalizing s with
   | nil => rfl
   | cons d L ih =>
     rw [List.foldl_cons,ih,List.foldl_cons]
     unfold rootNatStep
     rw [IntegerRoot.step_square]
 theorem rootNatFold_remainder (L : List (Bool×Bool)) (s : ℕ×ℕ) (hs : s.2≤2*s.1) :
     (L.foldl rootNatStep s).2≤2*(L.foldl rootNatStep s).1 := by
   induction L generalizing s with
   | nil => exact hs
   | cons d L ih =>
     rw [List.foldl_cons]
     apply ih
     have hd : d.1.toNat+2*d.2.toNat≤3 := by rcases d with ⟨a,b⟩;cases a <;> cases b <;> decide
     exact IntegerRoot.step_remainder s.1 s.2 _ hs hd
 theorem rootFold_sqrt (L : List Bool) :
     value (rootWordFold (quarterPairs L) ([],[])).1=Nat.sqrt (value L) := by
   let s := (quarterPairs L).foldl rootNatStep (0,0)
   have hv := rootWordFold_values (quarterPairs L) ([],[])
   change (value (rootWordFold (quarterPairs L) ([],[])).1,value (rootWordFold (quarterPairs L) ([],[])).2)=s at hv
   have hs := rootNatFold_square (quarterPairs L) (0,0)
   change s.1^2+s.2=(quarterPairs L).foldl (fun N d => 4*N+(d.1.toNat+2*d.2.toNat)) (0^2+0) at hs
   simp only [zero_pow (by decide : 2≠0),Nat.zero_add,quarterPairs_value] at hs
   have hr := rootNatFold_remainder (quarterPairs L) (0,0) (by omega)
   have hroot := IntegerRoot.square_characterization (value L) s.1 s.2 hs.symm hr
   have hh := congrArg Prod.fst hv
   exact hh.trans hroot.symm
 
 
 theorem integerRootWord_polynomial : PolyBound integerRootWordRealizer := polynomial_comp
   (polynomial_comp (polynomial_comp (polynomial_pair quarterPairs_polynomial (linear_polynomial (linear_constant (([] : List Bool),([] : List Bool)))))
     rootWordFold_polynomial) (linear_polynomial linear_fst)) trim_polynomial
 theorem integerRootWord_correct (L : List Bool) : integerRootWord L=natBits (Nat.sqrt (value L)) := by
   rw [integerRootWord,trim_eq_natBits,rootFold_sqrt]
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedDyadicRound
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 theorem dyadicZeros_polynomial : PolyBound dyadicZeros := polynomial_comp
   (linear_polynomial (linear_pair linear_snd (linear_constant false))) replicateList_polynomial
 
 theorem dyadicNumerator_polynomial : PolyBound dyadicNumerator := polynomial_comp
   (polynomial_pair dyadicZeros_polynomial (linear_polynomial (linear_comp (linear_comp linear_fst linear_snd) linear_fst))) appendBits_polynomial
 
 
 
 theorem dyadicDenominator_polynomial : PolyBound dyadicDenominator := polynomial_comp
   (polynomial_pair dyadicZeros_polynomial (linear_polynomial (linear_constant [true]))) appendBits_polynomial
 
 
 
 theorem zeroPrefix_value (p : ℕ) (A : List Bool) : value (List.replicate p false++A)=2^p*value A := by
   induction p with
   | zero => simp
   | succ p ih =>
     simp only [List.replicate_succ,List.cons_append,value,Bool.toNat_false,Nat.zero_add,ih,pow_succ]
     ring
 
 
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RationalRoot
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 theorem rootDoubleInput_polynomial : PolyBound rootDoubleInputRealizer := polynomial_pair
   (linear_polynomial (linear_pair (linear_constant false) linear_fst))
   (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_snd)) BinaryGcd.nat_add_polynomial)
 
 
 
 
 
 
 
 
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryWordProduct
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 theorem productWordStep_polynomial : PolyBound productWordStepRealizer := multiply_polynomial
 theorem productWordFold_length (xs : List (List Bool)) (b : List Bool) :
     (xs.foldl (fun b a => productWordStep (a,b)) b).length≤ b.length+(xs.map List.length).sum := by
   induction xs generalizing b with
   | nil => simp
   | cons a xs ih =>
     rw [List.foldl_cons]
     have hh := ih (productWordStep (a,b))
     have hm := multiply_length a b
     simp only [List.map_cons,List.sum_cons]
     exact hh.trans (by dsimp [productWordStep]; omega)
 theorem productWordFold_polynomial : PolyBound productWordStepRealizer.fold := by
   apply polynomial_fold_power productWordStep_polynomial 10 1
   intro xs b j hj
   clear hj
   have hs : (xs.map List.length).sum≤ volume xs := by
     induction xs with
     | nil => simp
     | cons a xs ih =>
       simp only [List.map_cons,List.sum_cons,volume_cons]
       have ha := bits_length_volume a
       omega
   have hsum : ((xs.take j).map List.length).sum≤(xs.map List.length).sum := by
     rw [List.map_take]
     have he : (((xs.map List.length).take j)++((xs.map List.length).drop j)).sum=
         ((xs.map List.length).take j).sum+((xs.map List.length).drop j).sum := List.sum_append
     rw [List.take_append_drop] at he
     omega
   have hh := productWordFold_length (xs.take j) b
   have hv := BinaryAdder.volume_bits ((xs.take j).foldl (fun b a => productWordStep (a,b)) b)
   have hb := bits_length_volume b
   simp only [pow_one,volume_pair]
   omega
 
 
 theorem wordProduct_polynomial : PolyBound wordProductRealizer :=
   polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial (linear_constant [true]))) productWordFold_polynomial
 theorem wordProduct_value (xs : List (List Bool)) : value (wordProduct xs)=(xs.map value).prod := by
   have h (xs : List (List Bool)) (b : List Bool) :
       value (xs.foldl (fun b a => productWordStep (a,b)) b)=value b*(xs.map value).prod := by
     induction xs generalizing b with
     | nil => simp
     | cons a xs ih =>
       rw [List.foldl_cons,ih]
       simp only [productWordStep,multiply_value,List.map_cons,List.prod_cons]
       ring
   simpa [wordProduct,value] using h xs [true]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryPowerTwoCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 theorem powerTwoWord_polynomial : PolyBound powerTwoWordRealizer :=
   polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial
     (linear_pair linear_id (linear_constant false))) replicateList_polynomial)
       (linear_polynomial (linear_constant [true]))) appendBits_polynomial
 theorem powerTwoWord_value (k : ℕ) : value (powerTwoWord k)=2^k := by
   induction k with
   | zero => simp [powerTwoWord,value]
   | succ k ih =>
     have he : powerTwoWord (k+1)=false::powerTwoWord k := by simp only [powerTwoWord,List.replicate_succ,List.cons_append]
     rw [he,value,Bool.toNat_false,zero_add,ih,pow_succ]
     omega

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

 
 
 theorem upperRootInput_polynomial : PolyBound upperRootInputRealizer := polynomial_pair
   (linear_polynomial (linear_constant true)) (polynomial_pair
     (polynomial_comp rootDoubleInput_polynomial dyadicNumerator_polynomial)
     (linear_polynomial (linear_comp linear_fst linear_snd)))
 
 
 theorem upperRootInteger_polynomial : PolyBound upperRootIntegerRealizer :=
   polynomial_comp (polynomial_comp upperRootInput_polynomial floorMagnitude_polynomial) integerRootWord_polynomial
 
 
 theorem upperRootSumInput_polynomial : PolyBound upperRootSumInputRealizer :=
   polynomial_pair upperRootInteger_polynomial (linear_polynomial (linear_constant [true]))
 
 
 theorem upperRootMagnitude_polynomial : PolyBound upperRootMagnitudeRealizer :=
   polynomial_comp upperRootSumInput_polynomial sumWords_polynomial
 
 
 theorem sqrtUpperWords_polynomial : PolyBound sqrtUpperWordsRealizer := polynomial_pair
   (linear_polynomial (linear_constant false)) (polynomial_pair upperRootMagnitude_polynomial
     (polynomial_comp (linear_polynomial linear_snd) powerTwoWord_polynomial))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedFloorDyadic
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 theorem scaledFloorInput_polynomial : PolyBound scaledFloorInputRealizer := polynomial_pair
   (linear_polynomial (linear_comp linear_fst linear_fst))
   (polynomial_pair dyadicNumerator_polynomial (linear_polynomial (linear_comp (linear_comp linear_fst linear_snd) linear_snd)))
 
 
 theorem signedFloorDyadic_polynomial : PolyBound signedFloorDyadicRealizer := polynomial_pair
   (linear_polynomial (linear_comp linear_fst linear_fst))
   (polynomial_pair (polynomial_comp scaledFloorInput_polynomial floorMagnitude_polynomial) dyadicDenominator_polynomial)
 theorem scaledFloorInput_value (s : SignedWords) (p : ℕ) :
     signedFractionValue (scaledFloorInput (s,p))=signedFractionValue s*(2:ℚ)^p := by
   rcases s with ⟨b,N,D⟩
   cases b <;> simp [scaledFloorInput,signedFractionValue,signedValue,zeroPrefix_value] <;> ring
 theorem signedFloorDyadic_correct (s : SignedWords) (p : ℕ) (hd : 0< value s.2.2) :
     0< value (signedFloorDyadic (s,p)).2.2 ∧
       signedFractionValue (signedFloorDyadic (s,p))=
         GLS.RationalRounding.roundDown (signedFractionValue s) (2^p) := by
   have hd' : 0< value (scaledFloorInput (s,p)).2.2 := hd
   have h := signedFloorWords_correct (scaledFloorInput (s,p)) hd'
   rw [scaledFloorInput_value] at h
   have he : signedFractionValue (signedFloorDyadic (s,p))=
       signedFractionValue (signedFloorWords (scaledFloorInput (s,p)))/(2:ℚ)^p := by
     simp only [signedFractionValue,signedFloorDyadic,signedFloorWords,scaledFloorInput,zeroPrefix_value]
     have hone : value [true]=1 := by decide
     rw [hone,Nat.mul_one,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,div_one]
   refine ⟨?_,?_⟩
   · change 0< value (List.replicate p false++[true])
     rw [zeroPrefix_value]
     simp [value]
   · rw [he,h]
     simp only [GLS.RationalRounding.roundDown,Nat.cast_pow,Nat.cast_ofNat]

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

 
 
 
 theorem matrixVector_polynomial : PolyBound matrixVectorRealizer := polynomial_mapEnvironment signedDot_polynomial
 
 
 theorem matrixScale_polynomial : PolyBound matrixScaleRealizer := polynomial_mapEnvironment vectorScale_polynomial
 
 
 theorem matrixSub_polynomial : PolyBound matrixSubRealizer :=
   polynomial_comp (arrayPairs_polynomial ([]:SignedVector) ([]:SignedVector)) (polynomial_mapList vectorSub_polynomial)
 
 
 theorem matrixAdd_polynomial : PolyBound matrixAddRealizer :=
   polynomial_comp (arrayPairs_polynomial ([]:SignedVector) ([]:SignedVector)) (polynomial_mapList vectorAdd_polynomial)
 
 
 theorem outerRow_polynomial : PolyBound outerRowRealizer :=
   polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) vectorScale_polynomial
 
 
 theorem matrixOuter_polynomial : PolyBound matrixOuterRealizer := polynomial_mapEnvironment outerRow_polynomial
 
 
 theorem floorVector_polynomial : PolyBound floorVectorRealizer := polynomial_mapEnvironment signedFloorDyadic_polynomial
 
 
 theorem floorMatrix_polynomial : PolyBound floorMatrixRealizer := polynomial_mapEnvironment floorVector_polynomial

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

 
 
 
 theorem diagonalWordAt_polynomial : PolyBound diagonalWordAtRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) (lookupList_polynomial ([]:SignedVector)))
     (linear_polynomial linear_fst)) (lookupList_polynomial signedZero)
 
 
 theorem diagonalEntryAt_polynomial : PolyBound diagonalEntryAtRealizer :=
   polynomial_pair (linear_polynomial linear_fst) diagonalWordAt_polynomial
 
 
 theorem diagonalEntries_polynomial : PolyBound diagonalEntriesRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp listLength_polynomial range_polynomial) (linear_polynomial linear_id))
   (polynomial_mapEnvironment diagonalEntryAt_polynomial)
 
 
 theorem diagonalCompare_polynomial : PolyBound diagonalCompareRealizer := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp (linear_comp linear_snd linear_snd) linear_snd)
     (linear_comp (linear_comp linear_fst linear_snd) linear_snd))) fractionLE_polynomial
 
 
 theorem diagonalMaxStep_polynomial : PolyBound diagonalMaxStepRealizer := polynomial_comp
   (polynomial_pair diagonalCompare_polynomial (linear_polynomial linear_id))
   (polynomial_choose (linear_polynomial linear_fst) (linear_polynomial linear_snd))
 theorem diagonalMaxStep_select (a b : DiagonalEntry) : diagonalMaxStep (a,b)=a ∨ diagonalMaxStep (a,b)=b := by
   unfold diagonalMaxStep
   split_ifs <;> simp
 theorem diagonalMaxFold_polynomial : PolyBound diagonalMaxStepRealizer.fold :=
   polynomial_fold_select diagonalMaxStep_polynomial (fun a b => diagonalMaxStep_select a b)
 
 
 theorem diagonalWinner_polynomial : PolyBound diagonalWinnerRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial linear_id) (headList_polynomial (0,signedZero))) diagonalMaxFold_polynomial
 
 
 theorem maximumDiagonal_polynomial : PolyBound maximumDiagonalRealizer := polynomial_comp diagonalEntries_polynomial diagonalWinner_polynomial

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RationalVectorAppend
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 theorem represents_append {n : ℕ} (A : SignedVector) (v : Vec n) (hA : RepresentsVector A v)
     (s : SignedWords) (hs : 0< value s.2.2) (r : ℝ) (hr : (signedFractionValue s:ℝ)=r) :
     RepresentsVector (A++[s]) (WithLp.toLp 2 (Fin.snoc (fun i => v i) r)) := by
   obtain ⟨a,rfl,ha,hv⟩ := hA
   refine ⟨Fin.snoc a s,?_,?_,?_⟩
   · rw [List.ofFn_succ']
     simp only [Fin.snoc_castSucc,Fin.snoc_last,List.concat_eq_append]
   · intro i
     refine Fin.lastCases ?_ (fun j => ?_) i
     · simpa only [Fin.snoc_last] using hs
     · simpa only [Fin.snoc_castSucc] using ha j
   · intro i
     refine Fin.lastCases ?_ (fun j => ?_) i
     · simpa only [Fin.snoc_last,WithLp.ofLp_toLp] using hr
     · simpa only [Fin.snoc_castSucc,WithLp.ofLp_toLp] using hv j

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BorderedMatrix
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.InverseMath

 
 theorem border_cast_cast {K : Type} [Zero K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (b : Fin n → K) (c : K) (i j : Fin n) :
     border A b c i.castSucc j.castSucc=A i j := by simp only [border,Fin.lastCases_castSucc,Fin.snoc_castSucc]
 theorem border_cast_last {K : Type} [Zero K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (b : Fin n → K) (c : K) (i : Fin n) :
     border A b c i.castSucc (Fin.last n)=b i := by simp only [border,Fin.lastCases_castSucc,Fin.snoc_last]
 theorem border_last_cast {K : Type} [Zero K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (b : Fin n → K) (c : K) (j : Fin n) :
     border A b c (Fin.last n) j.castSucc=b j := by simp only [border,Fin.lastCases_last,Fin.snoc_castSucc]
 theorem border_last_last {K : Type} [Zero K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (b : Fin n → K) (c : K) :
     border A b c (Fin.last n) (Fin.last n)=c := by simp only [border,Fin.lastCases_last,Fin.snoc_last]

 theorem border_mulVec {K : Type} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
     (b x : Fin n → K) (c t : K) :
     (border A b c) *ᵥ (Fin.snoc x t)=Fin.snoc (A *ᵥ x+t • b) (b ⬝ᵥ x+c*t) := by
   funext i
   refine Fin.lastCases ?_ (fun j => ?_) i
   · simp only [mulVec,dotProduct,Fin.sum_univ_castSucc,border_last_cast,border_last_last,
       Fin.snoc_castSucc,Fin.snoc_last]
   · simp only [mulVec,dotProduct,Fin.sum_univ_castSucc,border_cast_cast,border_cast_last,
       Fin.snoc_castSucc,Fin.snoc_last,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
     ring

 theorem border_quadratic {K : Type} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
     (b x : Fin n → K) (c t : K) :
     (Fin.snoc x t) ⬝ᵥ ((border A b c) *ᵥ (Fin.snoc x t))=
       x ⬝ᵥ (A *ᵥ x)+t*(x ⬝ᵥ b)+t*(b ⬝ᵥ x)+c*t^2 := by
   rw [border_mulVec]
   simp only [dotProduct,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,
     Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
   have he : (∑ i,x i*(t*b i))=t*(∑ i,x i*b i) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
   rw [he]
   ring

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













end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.IntegralLLLClosure
noncomputable section

open scoped Classical
open Matrix LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds













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

 

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLSizeStepCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLSizeStepSemantics
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLReductionBasis
noncomputable section

set_option backward.isDefEq.respectTransparency false
open LLLFactor.Reduction LLLFactor.RedBasis
namespace EdgeSublinearMWIS.Main.LLLBounds







end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLRowReduction
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds



 

 

 

 

 

 

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

 
 
 
 
 
 
 
 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLSizePass
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 



 

 

 

 

 

 

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

 theorem natSubtract_polynomial : PolyBound Realizer.sub := by
   refine ⟨10000000001,2,by omega,?_⟩
   rintro ⟨a,b⟩
   have ht := Realizer.time_sub_le a b
   have hbase : a+b+1≤ volume (a,b)+1 := by simp only [volume_pair,volume_nat]; omega
   have hp := Nat.pow_le_pow_left hbase 2
   constructor
   · exact ht.trans (by nlinarith)
   · simp only [volume_nat,volume_pair]
     have hs := Nat.sub_le a b
     nlinarith [Nat.one_le_pow 2 (2*a+1+(2*b+1)+1+1) (by omega)]
 
 theorem takeList_polynomial : PolyBound (takeList (α:=α)) := by
   unfold takeList
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp (polynomial_pair
     (polynomial_comp (linear_polynomial linear_snd) reverse_polynomial_generic)
     (polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) listLength_polynomial)
       (linear_polynomial linear_fst)) natSubtract_polynomial)) dropList_polynomial) reverse_polynomial_generic

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

 
 
 theorem matrixColumn_polynomial : PolyBound matrixColumnRealizer := polynomial_mapEnvironment (lookupList_polynomial signedZero)
 
 
 theorem appendCoordinate_polynomial : PolyBound appendCoordinateRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial linear_fst)
     (linear_polynomial (linear_comp (linear_pair linear_snd (linear_constant ([]:SignedVector))) linear_cons))) appendList_polynomial
 
 
 theorem appendColumn_polynomial : PolyBound appendColumnRealizer :=
   polynomial_comp (arrayPairs_polynomial ([]:SignedVector) signedZero) (polynomial_mapList appendCoordinate_polynomial)
 
 
 theorem borderMatrixWords_polynomial : PolyBound borderMatrixWordsRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial (linear_pair linear_fst (linear_comp linear_snd linear_fst))) appendColumn_polynomial)
     (polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) appendCoordinate_polynomial)
       (linear_polynomial (linear_constant ([]:SignedMatrix)))) (linear_polynomial linear_cons))) appendList_polynomial

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

 
 

 theorem represents_rational_dot {n : ℕ} (A B : SignedVector) (a b : Fin n → ℚ)
     (hA : RepresentsVector A (rationalVector a)) (hB : RepresentsVector B (rationalVector b)) :
     0< value (signedDot (A,B)).2.2 ∧ signedFractionValue (signedDot (A,B))=a ⬝ᵥ b := by
   have hh := represents_dot hA hB
   refine ⟨hh.1,?_⟩
   apply Rat.cast_injective (α:=ℝ)
   rw [hh.2]
   simp [rationalVector,PiLp.inner_apply,dotProduct,mul_comm]

 theorem represents_rational_scale {n : ℕ} (A : SignedVector) (a : Fin n → ℚ)
     (hA : RepresentsVector A (rationalVector a)) (s : SignedWords) (hs : 0< value s.2.2) :
     RepresentsVector (vectorScale (A,s)) (rationalVector (signedFractionValue s • a)) := by
   have hh := represents_scale hA s hs
   have he : (signedFractionValue s:ℝ) • rationalVector a=rationalVector (signedFractionValue s • a) := by
     ext i
     simp [rationalVector,smul_eq_mul]
   exact he ▸ hh

 theorem represents_matrix_vector {n : ℕ} (bs : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ)
     (hA : RepresentsMatrix bs A) (v : SignedVector) (x : Fin n → ℚ)
     (hv : RepresentsVector v (rationalVector x)) :
     RepresentsVector (matrixVector (bs,v)) (rationalVector (A *ᵥ x)) := by
   obtain ⟨rows,rfl,hrows⟩ := hA
   refine ⟨fun i => signedDot (rows i,v),?_,?_,?_⟩
   · simp only [matrixVector,List.map_ofFn]; rfl
   · intro i; exact (represents_rational_dot (rows i) v (A i) x (hrows i) hv).1
   · intro i
     rw [(represents_rational_dot (rows i) v (A i) x (hrows i) hv).2]
     rfl

 theorem represents_matrix_scale {n : ℕ} (bs : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ)
     (hA : RepresentsMatrix bs A) (s : SignedWords) (hs : 0< value s.2.2) :
     RepresentsMatrix (matrixScale (bs,s)) (signedFractionValue s • A) := by
   obtain ⟨rows,rfl,hrows⟩ := hA
   refine ⟨fun i => vectorScale (rows i,s),?_,?_⟩
   · simp only [matrixScale,List.map_ofFn]; rfl
   · intro i; exact represents_rational_scale (rows i) (A i) (hrows i) s hs

 theorem represents_rational_sub {n : ℕ} (A B : SignedVector) (a b : Fin n → ℚ)
     (hA : RepresentsVector A (rationalVector a)) (hB : RepresentsVector B (rationalVector b)) :
     RepresentsVector (vectorSub (A,B)) (rationalVector (a-b)) := by
   have hh := represents_sub hA hB
   have he : rationalVector a-rationalVector b=rationalVector (a-b) := by ext i; simp [rationalVector]
   exact he ▸ hh

 theorem represents_matrix_sub {n : ℕ} (bs cs : SignedMatrix) (A B : Matrix (Fin n) (Fin n) ℚ)
     (hA : RepresentsMatrix bs A) (hB : RepresentsMatrix cs B) :
     RepresentsMatrix (matrixSub (bs,cs)) (A-B) := by
   obtain ⟨rows,rfl,hrows⟩ := hA
   obtain ⟨cols,rfl,hcols⟩ := hB
   refine ⟨fun i => vectorSub (rows i,cols i),?_,?_⟩
   · simp only [matrixSub,Function.comp_apply,arrayPairs_ofFn,List.map_ofFn]; rfl
   · intro i; exact represents_rational_sub _ _ _ _ (hrows i) (hcols i)

 theorem represents_matrix_outer {n : ℕ} (as bs : SignedVector) (a b : Fin n → ℚ)
     (ha : RepresentsVector as (rationalVector a)) (hb : RepresentsVector bs (rationalVector b)) :
     RepresentsMatrix (matrixOuter (as,bs)) (Matrix.vecMulVec a b) := by
   obtain ⟨words,rfl,hden,hval⟩ := ha
   refine ⟨fun i => outerRow (words i,bs),?_,?_⟩
   · simp only [matrixOuter,List.map_ofFn]; rfl
   · intro i
     have hh := represents_rational_scale bs b hb (words i) (hden i)
     have he : signedFractionValue (words i)=a i := Rat.cast_injective (α:=ℝ) (hval i)
     rw [he] at hh
     exact hh

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

 
 
 theorem normalizeVector_polynomial : PolyBound normalizeVectorRealizer := polynomial_mapList signedReduced_polynomial
 
 
 theorem normalizeMatrix_polynomial : PolyBound normalizeMatrixRealizer := polynomial_mapList normalizeVector_polynomial
 theorem normalizeVector_rep {n : ℕ} {A : SignedVector} {v : Vec n} (hA : RepresentsVector A v) :
     RepresentsVector (normalizeVector A) v ∧ VectorCanonical (normalizeVector A) := by
   obtain ⟨a,rfl,ha,hv⟩ := hA
   have he : normalizeVector (List.ofFn a)=List.ofFn (fun i => signedReduced (a i)) := by
     simp only [normalizeVector,List.map_ofFn]; rfl
   rw [he]
   constructor
   · refine ⟨fun i => signedReduced (a i),rfl,?_,?_⟩
     · intro i; exact signedReduced_denpos (a i) (ha i)
     · intro i; rw [signedReduced_value (a i) (ha i)]; exact hv i
   · intro s hs
     obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hs
     exact signedReduced_idempotent (a i) (ha i)
 theorem normalizeMatrix_rep {n : ℕ} {bs : SignedMatrix} {A : Matrix (Fin n) (Fin n) ℚ}
     (hA : RepresentsMatrix bs A) :
     RepresentsMatrix (normalizeMatrix bs) A ∧ ∀ row∈normalizeMatrix bs,VectorCanonical row := by
   obtain ⟨rows,rfl,hrows⟩ := hA
   have he : normalizeMatrix (List.ofFn rows)=List.ofFn (fun i => normalizeVector (rows i)) := by
     simp only [normalizeMatrix,List.map_ofFn]; rfl
   rw [he]
   refine ⟨⟨fun i => normalizeVector (rows i),rfl,fun i => (normalizeVector_rep (hrows i)).1⟩,?_⟩
   intro row hrow
   obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
   exact (normalizeVector_rep (hrows i)).2
 theorem rational_vector_word_volume {n H : ℕ} (A : SignedVector) (a : Fin n → ℚ)
     (hA : RepresentsVector A (rationalVector a)) (hcan : VectorCanonical A)
     (hsize : ∀ i,(a i).num.natAbs≤2^H ∧ (a i).den≤2^H) :
     volume A≤ n*(14*(H+2)+1)+1 := by
   obtain ⟨words,rfl,hD,hv⟩ := hA
   have hs : ∀ i,volume (words i)≤14*(H+2) := by
     intro i
     have he : signedFractionValue (words i)=a i := Rat.cast_injective (α:=ℝ) (hv i)
     have hw := signedCanonical_width (words i) (hcan _ (List.mem_ofFn.mpr ⟨i,rfl⟩)) (hD i) H
       (by simpa only [he] using (hsize i).1) (by simpa only [he] using (hsize i).2)
     exact (signedVolume_width (words i)).trans (Nat.mul_le_mul_left 14 hw)
   have hh := volume_list_le (List.ofFn words) (14*(H+2)) (by
     intro s hs'; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hs'; exact hs i)
   simpa only [List.length_ofFn] using hh

 theorem rational_matrix_word_volume {n H : ℕ} (bs : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ)
     (hA : RepresentsMatrix bs A) (hcan : ∀ row∈bs,VectorCanonical row)
     (hsize : ∀ i j,(A i j).num.natAbs≤2^H ∧ (A i j).den≤2^H) :
     volume bs≤ n*(n*(14*(H+2)+1)+2)+1 := by
   obtain ⟨rows,rfl,hrows⟩ := hA
   have hrow (i : Fin n) : volume (rows i)≤ n*(14*(H+2)+1)+1 :=
     rational_vector_word_volume (rows i) (A i) (hrows i)
       (hcan _ (List.mem_ofFn.mpr ⟨i,rfl⟩)) (hsize i)
   have hh := volume_list_le (List.ofFn rows) (n*(14*(H+2)+1)+1) (by
     intro row hrow'; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow'; exact hrow i)
   simpa only [List.length_ofFn] using hh

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
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationBasisCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 theorem unsignedInteger_linear : Linear unsignedIntegerRealizer :=
   linear_pair (linear_constant false) (linear_pair linear_id (linear_constant [true]))
 
 
 theorem diagonalWord_polynomial : PolyBound diagonalWordRealizer := by
   unfold diagonalWordRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (polynomial_comp
     (linear_polynomial (linear_pair linear_fst (linear_comp linear_snd linear_fst))) eqNat_polynomial)
       (linear_polynomial linear_id))
     (polynomial_choose (linear_polynomial (linear_comp linear_snd linear_snd))
       (linear_polynomial (linear_constant zeroSignedWord)))
 
 
 theorem approximationDiagonal_polynomial : PolyBound approximationDiagonalRealizer :=
   polynomial_comp (polynomial_pair (polynomial_comp
     (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) range_polynomial) (linear_polynomial linear_snd))
       (polynomial_mapEnvironment diagonalWord_polynomial)) (linear_polynomial (linear_constant [zeroSignedWord]))) appendList_polynomial
 
 
 theorem approximationRowEnvironment_linear : Linear approximationRowEnvironment :=
   linear_pair (linear_comp linear_snd linear_fst) (linear_pair linear_fst (linear_comp linear_snd linear_snd))
 
 theorem approximationDiagonalRows_polynomial : PolyBound approximationDiagonalRowsRealizer :=
   polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) range_polynomial) (linear_polynomial linear_id))
     (polynomial_mapEnvironment (polynomial_comp (linear_polynomial approximationRowEnvironment_linear) approximationDiagonal_polynomial))
 
 
 theorem approximationLastRow_polynomial : PolyBound approximationLastRowRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (polynomial_pair (linear_polynomial linear_fst)
     (linear_polynomial (linear_comp (linear_comp linear_snd linear_fst) unsignedInteger_linear))) vectorScale_polynomial)
     (polynomial_comp (polynomial_pair (linear_polynomial (linear_comp (linear_comp linear_snd linear_snd) unsignedInteger_linear))
       (linear_polynomial (linear_constant ([]:SignedVector)))) (linear_polynomial linear_cons))) appendList_polynomial
 
 theorem approximationWords_polynomial : PolyBound approximationWordsRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) listLength_polynomial)
     (linear_polynomial (linear_comp (linear_comp linear_snd linear_fst) unsignedInteger_linear))) approximationDiagonalRows_polynomial)
     (polynomial_comp (polynomial_pair approximationLastRow_polynomial (linear_polynomial (linear_constant ([]:List SignedVector))))
       (linear_polynomial linear_cons))) appendList_polynomial

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

 
 
 
 
 theorem naturalSignedWord_polynomial : PolyBound naturalSignedWordRealizer :=
   polynomial_comp naturalWord_polynomial (linear_polynomial unsignedInteger_linear)
 
 
 theorem shapeDimensionSquare_polynomial : PolyBound shapeDimensionSquareRealizer :=
   polynomial_comp (polynomial_pair naturalSignedWord_polynomial naturalSignedWord_polynomial) canonicalMul_polynomial
 
 
 theorem shapeDimensionDenominator_polynomial : PolyBound shapeDimensionDenominatorRealizer := polynomial_comp
   (polynomial_pair shapeDimensionSquare_polynomial (linear_polynomial (linear_constant scalarOne))) canonicalSub_polynomial
 
 
 theorem shapeDimensionCoefficient_polynomial : PolyBound shapeDimensionCoefficientRealizer :=
   polynomial_comp (polynomial_pair shapeDimensionSquare_polynomial shapeDimensionDenominator_polynomial) canonicalDiv_polynomial
 
 
 theorem nextDimensionWord_polynomial : PolyBound nextDimensionWordRealizer := polynomial_comp
   (polynomial_pair naturalSignedWord_polynomial (linear_polynomial (linear_constant scalarOne))) canonicalAdd_polynomial
 
 
 theorem shapeCutDenominator_polynomial : PolyBound shapeCutDenominatorRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) nextDimensionWord_polynomial) (linear_polynomial linear_snd)) canonicalMul_polynomial
 
 
 theorem shapeCutCoefficient_polynomial : PolyBound shapeCutCoefficientRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_constant scalarTwo)) shapeCutDenominator_polynomial) canonicalDiv_polynomial
 
 
 theorem centerCutCoefficient_polynomial : PolyBound centerCutCoefficientRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_constant scalarOne)) shapeCutDenominator_polynomial) canonicalDiv_polynomial

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

 
 
 
 theorem inverseOriginalRow_polynomial : PolyBound inverseOriginalRow := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) linear_fst)) (lookupList_polynomial ([]:SignedVector))
 
 theorem inverseOriginalPivot_polynomial : PolyBound inverseOriginalPivotRealizer := polynomial_comp
   (polynomial_pair inverseOriginalRow_polynomial (linear_polynomial linear_fst)) (lookupList_polynomial signedZero)
 
 
 theorem inverseColumn_polynomial : PolyBound inverseColumnRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial linear_fst)
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) linear_fst)) matrixColumn_polynomial)) takeList_polynomial
 
 
 theorem inverseZ_polynomial : PolyBound inverseZRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_snd)) inverseColumn_polynomial) matrixVector_polynomial
 
 
 theorem inverseSchur_polynomial : PolyBound inverseSchurRealizer := polynomial_comp
   (polynomial_pair inverseOriginalPivot_polynomial (polynomial_comp (polynomial_pair inverseColumn_polynomial inverseZ_polynomial) signedDot_polynomial)) canonicalSub_polynomial
 
 
 theorem inverseReciprocal_polynomial : PolyBound inverseReciprocalRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_constant scalarOne)) inverseSchur_polynomial) canonicalDiv_polynomial
 
 
 theorem inverseNegative_polynomial : PolyBound inverseNegativeRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_constant signedZero)) inverseReciprocal_polynomial) canonicalSub_polynomial
 
 
 theorem inverseUpperBlock_polynomial : PolyBound inverseUpperBlockRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_snd))
     (polynomial_comp (polynomial_pair (polynomial_comp (polynomial_pair inverseZ_polynomial inverseZ_polynomial) matrixOuter_polynomial)
       inverseReciprocal_polynomial) matrixScale_polynomial)) matrixAdd_polynomial
 
 
 theorem inverseBorderVector_polynomial : PolyBound inverseBorderVectorRealizer := polynomial_comp
   (polynomial_pair inverseZ_polynomial inverseNegative_polynomial) vectorScale_polynomial
 
 
 theorem inverseNextData_polynomial : PolyBound inverseNextDataRealizer :=
   polynomial_pair inverseUpperBlock_polynomial (polynomial_pair inverseBorderVector_polynomial inverseReciprocal_polynomial)
 
 
 theorem inverseNext_polynomial : PolyBound inverseNextRealizer := polynomial_comp
   (polynomial_comp inverseNextData_polynomial borderMatrixWords_polynomial) normalizeMatrix_polynomial
 
 
 theorem inverseStep_polynomial : PolyBound inverseStepRealizer :=
   polynomial_pair (linear_polynomial (linear_comp linear_snd linear_fst)) inverseNext_polynomial

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

 
 
 theorem matrixInverseInitialize_polynomial : PolyBound matrixInverseInitializeRealizer := polynomial_pair
   (polynomial_comp listLength_polynomial range_polynomial)
   (linear_polynomial (linear_pair linear_id (linear_constant ([]:SignedMatrix))))
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RationalVectorTake
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 

 theorem represents_lookup {n : ℕ} (A : SignedVector) (x : Vec n) (h : RepresentsVector A x)
     (i : Fin n) (default : SignedWords) :
     0< value ((A.drop i.val).headD default).2.2 ∧
       (signedFractionValue ((A.drop i.val).headD default):ℝ)=x i := by
   obtain ⟨a,rfl,ha,hv⟩ := h
   rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn]
   simp only [i.isLt,dif_pos,Option.getD_some]
   exact ⟨ha i,hv i⟩

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

 theorem represents_rational_append {n : ℕ} (A : SignedVector) (a : Fin n → ℚ)
     (hA : RepresentsVector A (rationalVector a)) (s : SignedWords) (hs : 0< value s.2.2) :
     RepresentsVector (appendCoordinate (A,s)) (rationalVector (Fin.snoc a (signedFractionValue s))) := by
   have hh := represents_append A (rationalVector a) hA s hs (signedFractionValue s:ℝ) rfl
   have he : WithLp.toLp 2 (Fin.snoc (fun i => rationalVector a i) (signedFractionValue s:ℝ))=
       rationalVector (Fin.snoc a (signedFractionValue s)) := by
     ext i
     refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [rationalVector,WithLp.ofLp_toLp,Fin.snoc_castSucc,Fin.snoc_last]
   exact he ▸ hh

 theorem matrixColumn_correct {n : ℕ} (bs : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ)
     (hA : RepresentsMatrix bs A) (j : Fin n) :
     RepresentsVector (matrixColumn (bs,j.val)) (rationalVector (fun i => A i j)) := by
   obtain ⟨rows,rfl,hrows⟩ := hA
   refine ⟨fun i => ((rows i).drop j.val).headD signedZero,?_,?_,?_⟩
   · simp only [matrixColumn,List.map_ofFn]; rfl
   · intro i; exact (represents_lookup (rows i) (rationalVector (A i)) (hrows i) j signedZero).1
   · intro i; exact (represents_lookup (rows i) (rationalVector (A i)) (hrows i) j signedZero).2

 theorem borderMatrixWords_correct {n : ℕ} (bs : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ)
     (hA : RepresentsMatrix bs A) (vs : SignedVector) (b : Fin n → ℚ)
     (hv : RepresentsVector vs (rationalVector b)) (s : SignedWords) (hs : 0< value s.2.2) :
     RepresentsMatrix (borderMatrixWords (bs,(vs,s))) (InverseMath.border A b (signedFractionValue s)) := by
   obtain ⟨rows,rfl,hrows⟩ := hA
   obtain ⟨words,hw,hD,hval⟩ := hv
   have hv' : RepresentsVector vs (rationalVector b) := ⟨words,hw,hD,hval⟩
   have hvals : ∀ i,signedFractionValue (words i)=b i := by intro i; exact Rat.cast_injective (α:=ℝ) (hval i)
   let out : Fin n → SignedVector := fun i => appendCoordinate (rows i,words i)
   let last := appendCoordinate (vs,s)
   refine ⟨Fin.snoc out last,?_,?_⟩
   · simp only [borderMatrixWords,appendColumn,Function.comp_apply]
     rw [hw,arrayPairs_ofFn,List.map_ofFn,List.ofFn_succ']
     simp only [Fin.snoc_castSucc,Fin.snoc_last,List.concat_eq_append,out,last,hw,Function.comp_def]
   · intro i
     refine Fin.lastCases ?_ (fun i => ?_) i
     · have hh := represents_rational_append vs b hv' s hs
       simpa only [InverseMath.border,Fin.lastCases_last,Fin.snoc_last,last] using hh
     · have hh := represents_rational_append (rows i) (A i) (hrows i) (words i) (hD i)
       rw [hvals] at hh
       simpa only [InverseMath.border,Fin.lastCases_castSucc,Fin.snoc_castSucc,out] using hh

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

 

 theorem inv_symmetric {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : A.IsSymm) :
     A⁻¹.IsSymm := by
   have he : (A⁻¹).transpose=A⁻¹ := by rw [Matrix.transpose_nonsing_inv,hA.eq]
   exact he

 theorem sum_scale {K : Type} [CommRing K] {n : ℕ} (f z : Fin n → K) (r : K) :
     (∑ l,f l*(r*z l))=r*(∑ l,f l*z l) := by
   rw [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro l hl
   ring
 theorem sum_rank {K : Type} [CommRing K] {n : ℕ} (f w z : Fin n → K) (r v : K) :
     (∑ l,f l*(w l+r*(z l*v)))=(∑ l,f l*w l)+(r*v)*(∑ l,f l*z l) := by
   calc
     _=∑ l,(f l*w l+(r*v)*(f l*z l)) := by apply Finset.sum_congr rfl; intro l hl; ring
     _=_ := by rw [Finset.sum_add_distrib,←Finset.mul_sum]

 theorem borderInv_mul {K : Type} [Field K] {n : ℕ}
     (A B : Matrix (Fin n) (Fin n) K) (b z : Fin n → K) (c t : K)
     (hAB : A*B=1) (hAz : A *ᵥ z=b) (hBz : ∀ j,∑ i,b i*B i j=z j)
     (ht : t=c-b ⬝ᵥ z) (ht0 : t≠0) :
     border A b c*borderInv B z t=1 := by
   have hentry (i j : Fin n) : ∑ l,A i l*B l j=if i=j then 1 else 0 := by
     have he := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j) hAB
     simpa only [Matrix.mul_apply,Matrix.one_apply] using he
   have haz (i : Fin n) : ∑ l,A i l*z l=b i := congrFun hAz i
   have hts : c-(∑ i,b i*z i)=t := ht.symm
   have htz : t⁻¹*t=1 := inv_mul_cancel₀ ht0
   ext i j
   refine Fin.lastCases ?_ (fun i => ?_) i
   · refine Fin.lastCases ?_ (fun j => ?_) j
     · simp only [Matrix.mul_apply,Fin.sum_univ_castSucc,borderInv,border_last_cast,border_cast_last,
         border_last_last,Pi.smul_apply,smul_eq_mul,Matrix.one_apply,if_true]
       have he : (∑ l,b l*(-t⁻¹*z l))+c*t⁻¹=t⁻¹*(c-∑ l,b l*z l) := by
         rw [sum_scale]
         ring
       rw [he,hts,htz]
     · have hne : Fin.last n≠j.castSucc := (Fin.castSucc_ne_last j).symm
       simp only [Matrix.mul_apply,Fin.sum_univ_castSucc,borderInv,border_last_cast,border_cast_cast,
         border_last_last,Matrix.add_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul,
         Matrix.one_apply,if_neg hne]
       have he : (∑ l,b l*(B l j+t⁻¹*(z l*z j)))+c*(-t⁻¹*z j)=
           (∑ l,b l*B l j)+t⁻¹*z j*(∑ l,b l*z l-c) := by
         rw [sum_rank]
         ring
       rw [he,hBz]
       have hs : (∑ l,b l*z l)-c= -t := by rw [ht]; simp only [dotProduct]; ring
       rw [hs]
       calc
         _=z j-(t⁻¹*t)*z j := by ring
         _=0 := by rw [htz]; ring
   · refine Fin.lastCases ?_ (fun j => ?_) j
     · simp only [Matrix.mul_apply,Fin.sum_univ_castSucc,borderInv,border_cast_cast,border_cast_last,
         border_last_last,Pi.smul_apply,smul_eq_mul,Matrix.one_apply,Fin.castSucc_ne_last,if_false]
       have he : (∑ l,A i l*(-t⁻¹*z l))+b i*t⁻¹=t⁻¹*(-(∑ l,A i l*z l)+b i) := by
         rw [sum_scale]
         ring
       rw [he,haz]
       ring
     · simp only [Matrix.mul_apply,Fin.sum_univ_castSucc,borderInv,border_cast_cast,border_cast_last,
         border_last_cast,Matrix.add_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul,
         Matrix.one_apply,Fin.castSucc_inj]
       have he : (∑ l,A i l*(B l j+t⁻¹*(z l*z j)))+b i*(-t⁻¹*z j)=
           (∑ l,A i l*B l j)+t⁻¹*z j*((∑ l,A i l*z l)-b i) := by
         rw [sum_rank]
         ring
       rw [he,hentry,haz]
       ring

 theorem border_inverse {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
     (hA : IsUnit A.det) (hsym : A.IsSymm) (b : Fin n → K) (c : K)
     (ht : c-b ⬝ᵥ (A⁻¹ *ᵥ b)≠0) :
     (border A b c)⁻¹=borderInv A⁻¹ (A⁻¹ *ᵥ b) (c-b ⬝ᵥ (A⁻¹ *ᵥ b)) := by
   apply Matrix.inv_eq_right_inv
   apply borderInv_mul A A⁻¹ b (A⁻¹ *ᵥ b) c _ (Matrix.mul_nonsing_inv A hA)
   · rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv A hA,Matrix.one_mulVec]
   · intro j
     simp only [Matrix.mulVec,dotProduct]
     apply Finset.sum_congr rfl
     intro i hi
     rw [(inv_symmetric A hsym).apply i j]
     ring
   · rfl
   · exact ht

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.BorderedPositive
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.InverseMath

 theorem border_principal_positive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (c : ℝ)
     (hM : (border A b c).PosDef) : A.PosDef := by
   have hp := hM.submatrix (Fin.castSucc_injective n)
   have he : (border A b c).submatrix Fin.castSucc Fin.castSucc=A := by
     ext i j
     exact border_cast_cast A b c i j
   rwa [he] at hp

 theorem border_schur_positive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (c : ℝ)
     (hM : (border A b c).PosDef) : 0< c-b ⬝ᵥ (A⁻¹ *ᵥ b) := by
   have hp := border_principal_positive A b c hM
   have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hp.det_pos)
   let z := A⁻¹ *ᵥ b
   have hz : A *ᵥ z=b := by dsimp only [z]; rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv A hunit,Matrix.one_mulVec]
   let x : Fin (n+1) → ℝ := Fin.snoc (-z) 1
   have hx : x≠0 := by
     intro he
     have hl := congrFun he (Fin.last n)
     simp only [x,Fin.snoc_last,Pi.zero_apply,one_ne_zero] at hl
   have hpos := hM.dotProduct_mulVec_pos hx
   simp only [star_trivial] at hpos
   rw [show x=Fin.snoc (-z) 1 from rfl,border_quadratic] at hpos
   simp only [Matrix.mulVec_neg,hz,neg_dotProduct,dotProduct_neg,neg_neg,one_mul,one_pow,mul_one] at hpos
   rw [dotProduct_comm z b] at hpos
   linarith

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

 
 
 theorem castMatrix_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) : castMatrix A i j=(A i j:ℝ) := rfl
 theorem castMatrix_unit {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : (castMatrix A).PosDef) : IsUnit A.det := by
   apply isUnit_iff_ne_zero.mpr
   intro hz
   have hh := hA.det_pos
   have he : (A.det:ℝ)=(castMatrix A).det := Rat.cast_det A
   rw [←he,hz,Rat.cast_zero] at hh
   exact (lt_irrefl _ hh)
 theorem castMatrix_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsUnit A.det) :
     castMatrix A⁻¹=(castMatrix A)⁻¹ := by
   let F : Matrix (Fin n) (Fin n) ℚ →+* Matrix (Fin n) (Fin n) ℝ := (Rat.castHom ℝ).mapMatrix
   have hh := congrArg F (Matrix.mul_nonsing_inv A hA)
   rw [map_mul,map_one] at hh
   exact (Matrix.inv_eq_right_inv hh).symm
 theorem castVector_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
     castVector (A *ᵥ b)=(castMatrix A) *ᵥ (castVector b) := by
   funext i
   simp [castVector,castMatrix,Matrix.mulVec,dotProduct]
 theorem castMatrix_border {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) (c : ℚ) :
     castMatrix (border A b c)=border (castMatrix A) (castVector b) (c:ℝ) := by
   ext i j
   refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
     simp only [castMatrix_apply,border_last_last,border_last_cast,border_cast_last,border_cast_cast,castVector]
 theorem rational_border_positive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) (c : ℚ)
     (hM : (castMatrix (border A b c)).PosDef) :
     (castMatrix A).PosDef ∧ 0< c-b ⬝ᵥ (A⁻¹ *ᵥ b) := by
   rw [castMatrix_border] at hM
   have hP := border_principal_positive _ _ _ hM
   have hQ := border_schur_positive _ _ _ hM
   have hunit := castMatrix_unit A hP
   refine ⟨hP,?_⟩
   apply (Rat.cast_pos (K:=ℝ)).mp
   have he : ((c-b ⬝ᵥ (A⁻¹ *ᵥ b):ℚ):ℝ)=(c:ℝ)-(castVector b) ⬝ᵥ ((castMatrix A)⁻¹ *ᵥ castVector b) := by
     rw [←castMatrix_inv A hunit,←castVector_mulVec]
     simp [castVector,dotProduct]
   rw [he]
   exact hQ

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

 
 
 theorem principal_succ {K : Type} [Zero K] {n k : ℕ} (A : Matrix (Fin n) (Fin n) K)
     (hs : A.IsSymm) (hk : k< n) :
     principal A (k+1) (by omega)=border (principal A k (by omega)) (principalColumn A hk) (A ⟨k,hk⟩ ⟨k,hk⟩) := by
   ext i j
   refine Fin.lastCases ?_ (fun i => ?_) i
   · refine Fin.lastCases ?_ (fun j => ?_) j
     · rw [border_last_last]; rfl
     · rw [border_last_cast]
       exact hs.apply _ _
   · refine Fin.lastCases ?_ (fun j => ?_) j
     · rw [border_cast_last]; rfl
     · rw [border_cast_cast]; rfl
 theorem principal_positive {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
     (hA : (castMatrix A).PosDef) (hk : k≤ n) : (castMatrix (principal A k hk)).PosDef := by
   have hh := hA.submatrix (Fin.castLE_injective hk)
   exact hh
 theorem principal_symmetric {K : Type} {n k : ℕ} (A : Matrix (Fin n) (Fin n) K)
     (hs : A.IsSymm) (hk : k≤ n) : (principal A k hk).IsSymm := by
   change (principal A k hk).transpose=principal A k hk
   ext i j
   exact hs.apply _ _
 theorem principal_border_inverse {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
     (hA : (castMatrix A).PosDef) (hs : A.IsSymm) (hk : k< n) :
     (principal A (k+1) (by omega))⁻¹=
       borderInv (principal A k (by omega))⁻¹ ((principal A k (by omega))⁻¹ *ᵥ principalColumn A hk)
         (A ⟨k,hk⟩ ⟨k,hk⟩-principalColumn A hk ⬝ᵥ ((principal A k (by omega))⁻¹ *ᵥ principalColumn A hk)) := by
   have hp := principal_positive A hA (by omega : k+1≤ n)
   rw [principal_succ A hs hk] at hp ⊢
   have hschur := rational_border_positive _ _ _ hp
   exact border_inverse _ (castMatrix_unit _ hschur.1) (principal_symmetric A hs (by omega)) _ _ (ne_of_gt hschur.2)

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.VectorPrefix
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 theorem array_lookup_ofFn {α : Type} {n : ℕ} (a : Fin n → α) (i : Fin n) (default : α) :
     ((List.ofFn a).drop i.val).headD default=a i := by
   rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn]
   simp [i.isLt]

 theorem take_ofFn_prefix {α : Type} {n k : ℕ} (hk : k≤ n) (a : Fin n → α) :
     (List.ofFn a).take k=List.ofFn (fun i : Fin k => a (Fin.castLE hk i)) := by
   apply List.ext_getElem
   · simp only [List.length_take,List.length_ofFn,Nat.min_eq_left hk]
   · intro j hj hk'
     simp only [List.getElem_take,List.getElem_ofFn,Fin.castLE_mk]

 theorem represents_take_prefix {n k : ℕ} (hk : k≤ n) (A : SignedVector) (v : Vec n)
     (hA : RepresentsVector A v) :
     RepresentsVector (A.take k) (WithLp.toLp 2 (fun i : Fin k => v (Fin.castLE hk i))) := by
   obtain ⟨a,rfl,ha,hv⟩ := hA
   refine ⟨fun i => a (Fin.castLE hk i),take_ofFn_prefix hk a,
     fun i => ha (Fin.castLE hk i),fun i => hv (Fin.castLE hk i)⟩

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

 

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLPassNorm
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 

 

 

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

 

 

 

 

 

 

 

 

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLBitGrowthPower
noncomputable section

open scoped Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 

 

 

 

 

 

 

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

 
 
 
 
 
 
 
 theorem parseIntegerMatrix_polynomial : PolyBound parseIntegerMatrixRealizer :=
   polynomial_comp (polynomial_comp readNatural_polynomial readMatrixRows_polynomial) (linear_polynomial linear_fst)
 
 
 

 
 
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

 theorem serializeRow_rep {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (A : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (embed B i)) (i : Fin n) :
     serializeRow (A i)=(List.ofFn (fun j => encodeRat (B i j:ℚ))).flatten := by
   obtain ⟨a,ha,hd,hv⟩ := hA i
   rw [ha]
   simp only [serializeRow,List.flatMap_def,List.map_ofFn]
   congr 1
   apply congrArg List.ofFn
   funext j
   have hq : signedFractionValue (a j)=(B i j:ℚ) := Rat.cast_injective (α:=ℝ) (hv j)
   have hb : rationalBits (a j)=encodeRat (signedFractionValue (a j)) :=
     rationalBits_correct (a j).1 (a j).2.1 (a j).2.2 (hd j)
   simpa only [Function.comp_apply] using hb.trans (congrArg encodeRat hq)

 theorem serializeMatrix_rep {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (A : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (embed B i)) :
     serializeMatrix (List.ofFn A)=integerMatrixInput B := by
   simp only [serializeMatrix,integerMatrixInput,List.length_ofFn,List.flatMap_def,List.map_ofFn,
     Function.comp_def,serializeRow_rep B A hA]

 

 

 

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

 theorem represents_unique {n : ℕ} {A : SignedVector} {u v : LLLFactor.RedBasis.Vec n}
     (hu : RepresentsVector A u) (hv : RepresentsVector A v) : u=v := by
   obtain ⟨a,ha,hd,hua⟩ := hu
   obtain ⟨b,hb,he,hvb⟩ := hv
   have hab : a=b := List.ofFn_inj.mp (ha.symm.trans hb)
   subst b
   ext i
   exact (hua i).symm.trans (hvb i)

 

 

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

 

 theorem approximationBasis_cast {n : ℕ} (a : Fin n → ℤ) (T U : ℤ) (i : Fin n) (j : Fin (n+1)) :
     approximationBasis a T U i.castSucc j=if i.castSucc=j then T else 0 := by
   simp only [approximationBasis,Fin.val_castSucc,dif_pos i.isLt]
 theorem approximationBasis_last {n : ℕ} (a : Fin n → ℤ) (T U : ℤ) (j : Fin n) :
     approximationBasis a T U (Fin.last n) j.castSucc=a j := by
   simp [approximationBasis,j.isLt]
 theorem approximationBasis_last_last {n : ℕ} (a : Fin n → ℤ) (T U : ℤ) :
     approximationBasis a T U (Fin.last n) (Fin.last n)=U := by
   simp [approximationBasis]
 theorem approximationBasis_det {n : ℕ} (a : Fin n → ℤ) (T U : ℤ) :
     (approximationBasis a T U).det=T^n*U := by
   rw [Matrix.det_of_isLowerTriangular]
   · rw [Fin.prod_univ_castSucc]
     simp only [approximationBasis_cast,ite_true,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
       approximationBasis_last_last]
   · intro i j hij
     have hi : i.val< n := by have hj:=j.isLt; change i.val< j.val at hij; omega
     have hne : i≠j := by intro he; subst j; exact (lt_irrefl _ hij)
     simp only [approximationBasis,dif_pos hi,if_neg hne]

 theorem embed_independent_of_det_ne_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hB : B.det≠0) : LinearIndependent ℝ (embed B) := by
   have hr : (B.map (Int.castRingHom ℝ)).det≠0 := by
     have he : (B.map (Int.castRingHom ℝ)).det=(B.det:ℝ) := (Int.cast_det B).symm
     rw [he]
     exact_mod_cast hB
   have hlin := Matrix.linearIndependent_rows_of_det_ne_zero hr
   exact hlin.map' (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap
     (LinearMap.ker_eq_bot.mpr (WithLp.toLp_injective 2))

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

 theorem unsignedInteger_den (A : List Bool) : 0< value (unsignedIntegerWord A).2.2 := by change 0< value [true]; decide
 theorem unsignedInteger_value (A : List Bool) : signedFractionValue (unsignedIntegerWord A)=(value A:ℚ) := by
   simp [unsignedIntegerWord,signedFractionValue,signedValue,value]
 theorem zeroSigned_den : 0< value zeroSignedWord.2.2 := by decide
 theorem zeroSigned_value : signedFractionValue zeroSignedWord=0 := by
   simp [zeroSignedWord,signedFractionValue,signedValue,value]

 theorem diagonal_rep {n : ℕ} (i : Fin n) (T : List Bool) (a : Fin n → ℤ) (U : ℤ) :
     RepresentsVector (approximationDiagonal (n,(i.val,unsignedIntegerWord T)))
       (embed (approximationBasis a (value T:ℤ) U) i.castSucc) := by
   let v : Vec n := WithLp.toLp 2 (fun j => if j=i then (value T:ℝ) else 0)
   have hrow : RepresentsVector ((List.range n).map (fun j => diagonalWord (j,(i.val,unsignedIntegerWord T)))) v := by
     refine ⟨fun j => if j=i then unsignedIntegerWord T else zeroSignedWord,?_,?_,?_⟩
     · rw [map_range_ofFn]
       congr 1
       funext j
       simp only [diagonalWord,Fin.ext_iff]
     · intro j
       dsimp only
       by_cases hj : j=i
       · simp only [if_pos hj]; exact unsignedInteger_den T
       · simp only [if_neg hj]; exact zeroSigned_den
     · intro j
       dsimp only [v,WithLp.ofLp_toLp]
       split_ifs <;> simp only [unsignedInteger_value,zeroSigned_value,Rat.cast_natCast,Rat.cast_zero]
   have hh := represents_append _ v hrow zeroSignedWord zeroSigned_den 0 (by rw [zeroSigned_value,Rat.cast_zero])
   have he : WithLp.toLp 2 (Fin.snoc (fun j => v j) (0:ℝ))=
       embed (approximationBasis a (value T:ℤ) U) i.castSucc := by
     ext j
     refine Fin.lastCases ?_ (fun k => ?_) j
     · simp [approximationBasis_cast,embed]
     · simp only [WithLp.ofLp_toLp,Fin.snoc_castSucc,v,embed,approximationBasis_cast,Fin.castSucc_inj]
       by_cases h : k=i
       · subst k; simp
       · simp [h,Ne.symm h]
   exact he ▸ hh

 theorem approximationWords_rep {n : ℕ} (a : Fin n → ℤ) (T U : List Bool)
     (A : Fin n → SignedWords) (hA : ∀ i,0< value (A i).2.2)
     (hval : ∀ i,(signedFractionValue (A i):ℝ)*(value T:ℝ)=(a i:ℝ)) :
     ∃ rows : Fin (n+1) → SignedVector,
       approximationWords (List.ofFn A,(T,U))=List.ofFn rows ∧
       ∀ i,RepresentsVector (rows i) (embed (approximationBasis a (value T:ℤ) (value U:ℤ)) i) := by
   let row : Fin n → SignedVector := fun i => approximationDiagonal (n,(i.val,unsignedIntegerWord T))
   let last := vectorScale (List.ofFn A,unsignedIntegerWord T)++[unsignedIntegerWord U]
   refine ⟨Fin.snoc row last,?_,?_⟩
   · simp only [approximationWords,List.length_ofFn,approximationDiagonalRows,List.ofFn_succ',
       Fin.snoc_castSucc,Fin.snoc_last,List.concat_eq_append]
     rw [map_range_ofFn]
   · intro i
     refine Fin.lastCases ?_ (fun j => ?_) i
     case refine_2.refine_2 =>
       simpa only [Fin.snoc_castSucc,row] using diagonal_rep j T a (value U:ℤ)
     let v : Vec n := WithLp.toLp 2 (fun j => (signedFractionValue (A j):ℝ))
     have hv : RepresentsVector (List.ofFn A) v := ⟨A,rfl,hA,fun _ => rfl⟩
     have hscale := represents_scale hv (unsignedIntegerWord T) (unsignedInteger_den T)
     have hh := represents_append _ _ hscale (unsignedIntegerWord U) (unsignedInteger_den U)
       (value U:ℝ) (by rw [unsignedInteger_value,Rat.cast_natCast])
     have he : WithLp.toLp 2 (Fin.snoc (fun j => ((signedFractionValue (unsignedIntegerWord T):ℝ) • v) j) (value U:ℝ))=
         embed (approximationBasis a (value T:ℤ) (value U:ℤ)) (Fin.last n) := by
       ext j
       refine Fin.lastCases ?_ (fun k => ?_) j
       · simp only [WithLp.ofLp_toLp,Fin.snoc_last,embed,approximationBasis_last_last,Int.cast_natCast]
       · simp only [WithLp.ofLp_toLp,Fin.snoc_castSucc,PiLp.smul_apply,v,smul_eq_mul,
           unsignedInteger_value,Rat.cast_natCast,embed,approximationBasis_last]
         rw [mul_comm,hval]
     simpa only [Fin.snoc_last,last] using (he ▸ hh)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidScalarSemantics
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 theorem scalarOne_den : 0< value scalarOne.2.2 := unsignedInteger_den _
 theorem scalarTwo_den : 0< value scalarTwo.2.2 := unsignedInteger_den _
 theorem scalarOne_value : signedFractionValue scalarOne=1 := by simp [scalarOne,unsignedInteger_value,value]
 theorem scalarTwo_value : signedFractionValue scalarTwo=2 := by simp [scalarTwo,unsignedInteger_value,value]
 theorem naturalSignedWord_den (n : ℕ) : 0< value (naturalSignedWord n).2.2 := unsignedInteger_den _
 theorem naturalSignedWord_value (n : ℕ) : signedFractionValue (naturalSignedWord n)=(n:ℚ) := by
   rw [naturalSignedWord,Function.comp_apply,unsignedInteger_value,value_natBits]
 theorem shapeDimensionSquare_correct (n : ℕ) :
     0< value (shapeDimensionSquare n).2.2 ∧ signedFractionValue (shapeDimensionSquare n)=(n:ℚ)^2 := by
   refine ⟨canonicalMul_denpos _ _ (naturalSignedWord_den n) (naturalSignedWord_den n),?_⟩
   rw [shapeDimensionSquare,Function.comp_apply,canonicalMul_value _ _ (naturalSignedWord_den n) (naturalSignedWord_den n),naturalSignedWord_value]
   ring
 theorem shapeDimensionDenominator_correct (n : ℕ) :
     0< value (shapeDimensionDenominator n).2.2 ∧ signedFractionValue (shapeDimensionDenominator n)=(n:ℚ)^2-1 := by
   refine ⟨canonicalSub_denpos _ _ (shapeDimensionSquare_correct n).1 scalarOne_den,?_⟩
   rw [shapeDimensionDenominator,canonicalSub_value _ _ (shapeDimensionSquare_correct n).1 scalarOne_den,
     (shapeDimensionSquare_correct n).2,scalarOne_value]
 theorem shapeDimensionCoefficient_correct (n : ℕ) (hn : 2≤ n) :
     0< value (shapeDimensionCoefficient n).2.2 ∧
       signedFractionValue (shapeDimensionCoefficient n)=(n:ℚ)^2/((n:ℚ)^2-1) := by
   have hnQ : (2:ℚ)≤ n := by exact_mod_cast hn
   have hne : signedFractionValue (shapeDimensionDenominator n)≠0 := by
     rw [(shapeDimensionDenominator_correct n).2]
     nlinarith
   have hnum := signed_num_positive_of_nonzero _ hne
   refine ⟨canonicalDiv_denpos _ _ (shapeDimensionSquare_correct n).1 hnum,?_⟩
   rw [shapeDimensionCoefficient,canonicalDiv_value _ _ (shapeDimensionSquare_correct n).1 hnum,
     (shapeDimensionSquare_correct n).2,(shapeDimensionDenominator_correct n).2]
 theorem nextDimensionWord_correct (n : ℕ) :
     0< value (nextDimensionWord n).2.2 ∧ signedFractionValue (nextDimensionWord n)=(n:ℚ)+1 := by
   refine ⟨canonicalAdd_denpos _ _ (naturalSignedWord_den n) scalarOne_den,?_⟩
   rw [nextDimensionWord,canonicalAdd_value _ _ (naturalSignedWord_den n) scalarOne_den,naturalSignedWord_value,scalarOne_value]
 theorem shapeCutDenominator_correct (n : ℕ) (q : SignedWords) (hq : 0< value q.2.2) :
     0< value (shapeCutDenominator (n,q)).2.2 ∧
       signedFractionValue (shapeCutDenominator (n,q))=((n:ℚ)+1)*signedFractionValue q := by
   refine ⟨canonicalMul_denpos _ _ (nextDimensionWord_correct n).1 hq,?_⟩
   rw [shapeCutDenominator,canonicalMul_value _ _ (nextDimensionWord_correct n).1 hq,(nextDimensionWord_correct n).2]
 theorem shapeCutCoefficient_correct (n : ℕ) (q : SignedWords) (hq : 0< value q.2.2)
     (hne : signedFractionValue q≠0) :
     0< value (shapeCutCoefficient (n,q)).2.2 ∧
       signedFractionValue (shapeCutCoefficient (n,q))=2/(((n:ℚ)+1)*signedFractionValue q) := by
   have hdne : signedFractionValue (shapeCutDenominator (n,q))≠0 := by
     rw [(shapeCutDenominator_correct n q hq).2]
     exact mul_ne_zero (by positivity) hne
   have hnum := signed_num_positive_of_nonzero _ hdne
   refine ⟨canonicalDiv_denpos _ _ scalarTwo_den hnum,?_⟩
   rw [shapeCutCoefficient,Function.comp_apply,canonicalDiv_value _ _ scalarTwo_den hnum,
     scalarTwo_value,(shapeCutDenominator_correct n q hq).2]
 theorem centerCutCoefficient_correct (n : ℕ) (q : SignedWords) (hq : 0< value q.2.2)
     (hne : signedFractionValue q≠0) :
     0< value (centerCutCoefficient (n,q)).2.2 ∧
       signedFractionValue (centerCutCoefficient (n,q))=1/(((n:ℚ)+1)*signedFractionValue q) := by
   have hdne : signedFractionValue (shapeCutDenominator (n,q))≠0 := by
     rw [(shapeCutDenominator_correct n q hq).2]
     exact mul_ne_zero (by positivity) hne
   have hnum := signed_num_positive_of_nonzero _ hdne
   refine ⟨canonicalDiv_denpos _ _ scalarOne_den hnum,?_⟩
   rw [centerCutCoefficient,Function.comp_apply,canonicalDiv_value _ _ scalarOne_den hnum,
     scalarOne_value,(shapeCutDenominator_correct n q hq).2]

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

 theorem represents_rational_add {n : ℕ} (A B : SignedVector) (a b : Fin n → ℚ)
     (hA : RepresentsVector A (rationalVector a)) (hB : RepresentsVector B (rationalVector b)) :
     RepresentsVector (vectorAdd (A,B)) (rationalVector (a+b)) := by
   obtain ⟨as,rfl,ha,hav⟩ := hA
   obtain ⟨bs,rfl,hb,hbv⟩ := hB
   refine ⟨fun i => canonicalAdd (as i,bs i),vectorAdd_ofFn as bs,?_,?_⟩
   · intro i; exact canonicalAdd_denpos _ _ (ha i) (hb i)
   · intro i
     rw [canonicalAdd_value _ _ (ha i) (hb i),Rat.cast_add,hav,hbv]
     simp [rationalVector]

 theorem represents_matrix_add {n : ℕ} (bs cs : SignedMatrix) (A B : Matrix (Fin n) (Fin n) ℚ)
     (hA : RepresentsMatrix bs A) (hB : RepresentsMatrix cs B) :
     RepresentsMatrix (matrixAdd (bs,cs)) (A+B) := by
   obtain ⟨rows,rfl,hrows⟩ := hA
   obtain ⟨cols,rfl,hcols⟩ := hB
   refine ⟨fun i => vectorAdd (rows i,cols i),?_,?_⟩
   · simp only [matrixAdd,Function.comp_apply,arrayPairs_ofFn,List.map_ofFn]; rfl
   · intro i; exact represents_rational_add _ _ _ _ (hrows i) (hcols i)

 theorem represents_floor_vector {n : ℕ} (A : SignedVector) (a : Fin n → ℚ)
     (hA : RepresentsVector A (rationalVector a)) (p : ℕ) :
     RepresentsVector (floorVector (A,p)) (rationalVector (fun i => GLS.RationalRounding.roundDown (a i) (2^p))) := by
   obtain ⟨as,rfl,ha,hav⟩ := hA
   refine ⟨fun i => signedFloorDyadic (as i,p),?_,?_,?_⟩
   · simp only [floorVector,List.map_ofFn]; rfl
   · intro i; exact (signedFloorDyadic_correct (as i) p (ha i)).1
   · intro i
     rw [(signedFloorDyadic_correct (as i) p (ha i)).2]
     have he : signedFractionValue (as i)=a i := Rat.cast_injective (α:=ℝ) (hav i)
     rw [he]
     rfl

 theorem represents_floor_matrix {n : ℕ} (bs : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ)
     (hA : RepresentsMatrix bs A) (p : ℕ) :
     RepresentsMatrix (floorMatrix (bs,p)) (fun i j => GLS.RationalRounding.roundDown (A i j) (2^p)) := by
   obtain ⟨rows,rfl,hrows⟩ := hA
   refine ⟨fun i => floorVector (rows i,p),?_,?_⟩
   · simp only [floorMatrix,List.map_ofFn]; rfl
   · intro i; exact represents_floor_vector (rows i) (A i) (hrows i) p

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

 theorem inverseColumn_correct {n k : ℕ} (hk : k< n) (orig inv : SignedMatrix)
     (A : Matrix (Fin n) (Fin n) ℚ) (hA : RepresentsMatrix orig A) :
     RepresentsVector (inverseColumn (k,(orig,inv))) (rationalVector (principalColumn A hk)) := by
   have hh := matrixColumn_correct orig A hA (⟨k,hk⟩:Fin n)
   have hp := represents_take_prefix (by omega : k≤ n) _ _ hh
   exact hp
 theorem inversePivot_correct {n k : ℕ} (hk : k< n) (orig : SignedMatrix)
     (A : Matrix (Fin n) (Fin n) ℚ) (hA : RepresentsMatrix orig A) :
     0< value ((((orig.drop k).headD []).drop k).headD signedZero).2.2 ∧
       signedFractionValue ((((orig.drop k).headD []).drop k).headD signedZero)=A ⟨k,hk⟩ ⟨k,hk⟩ := by
   obtain ⟨rows,rfl,hrows⟩ := hA
   have he := array_lookup_ofFn rows (⟨k,hk⟩:Fin n) ([]:SignedVector)
   dsimp only at he
   rw [he]
   have hh := represents_lookup (rows ⟨k,hk⟩) _ (hrows ⟨k,hk⟩) (⟨k,hk⟩:Fin n) signedZero
   exact ⟨hh.1,Rat.cast_injective (α:=ℝ) hh.2⟩

 theorem inverseNext_correct {n k : ℕ} (hk : k< n) (orig inv : SignedMatrix)
     (A : Matrix (Fin n) (Fin n) ℚ) (hA : RepresentsMatrix orig A)
     (B : Matrix (Fin k) (Fin k) ℚ) (hB : RepresentsMatrix inv B)
     (ht : A ⟨k,hk⟩ ⟨k,hk⟩-principalColumn A hk ⬝ᵥ (B *ᵥ principalColumn A hk)≠0) :
     RepresentsMatrix (inverseNext (k,(orig,inv)))
       (borderInv B (B *ᵥ principalColumn A hk)
         (A ⟨k,hk⟩ ⟨k,hk⟩-principalColumn A hk ⬝ᵥ (B *ᵥ principalColumn A hk))) ∧
       ∀ row∈inverseNext (k,(orig,inv)),VectorCanonical row := by
   let s := (k,(orig,inv))
   let b := principalColumn A hk
   let z := B *ᵥ b
   let t := A ⟨k,hk⟩ ⟨k,hk⟩-b ⬝ᵥ z
   have hcol := inverseColumn_correct hk orig inv A hA
   have hz := represents_matrix_vector inv B hB (inverseColumn s) b hcol
   have hpiv := inversePivot_correct hk orig A hA
   have hdot := represents_rational_dot (inverseColumn s) (inverseZ s) b z hcol hz
   have hschurD : 0< value (inverseSchur s).2.2 := canonicalSub_denpos _ _ hpiv.1 hdot.1
   have hschur : signedFractionValue (inverseSchur s)=t := by
     rw [inverseSchur,canonicalSub_value _ _ hpiv.1 hdot.1,hpiv.2,hdot.2]
   have hnum : 0< value (inverseSchur s).2.1 := signed_num_positive_of_nonzero _ (by rw [hschur]; exact ht)
   have hrecD : 0< value (inverseReciprocal s).2.2 := canonicalDiv_denpos _ _ scalarOne_den hnum
   have hrec : signedFractionValue (inverseReciprocal s)=t⁻¹ := by
     rw [inverseReciprocal,Function.comp_apply,canonicalDiv_value _ _ scalarOne_den hnum,scalarOne_value,hschur,one_div]
   have hnegD : 0< value (inverseNegative s).2.2 := canonicalSub_denpos _ _ zero_denpos hrecD
   have hneg : signedFractionValue (inverseNegative s)= -t⁻¹ := by
     rw [inverseNegative,canonicalSub_value _ _ zero_denpos hrecD,zero_value,hrec,zero_sub]
   have houter := represents_matrix_outer (inverseZ s) (inverseZ s) z z hz hz
   have hcorr := represents_matrix_scale (matrixOuter (inverseZ s,inverseZ s)) _ houter (inverseReciprocal s) hrecD
   rw [hrec] at hcorr
   have hupper := represents_matrix_add inv _ B _ hB hcorr
   have hvec := represents_rational_scale (inverseZ s) z hz (inverseNegative s) hnegD
   rw [hneg] at hvec
   have hborder := borderMatrixWords_correct (inverseUpperBlock s) _ hupper (inverseBorderVector s) _ hvec (inverseReciprocal s) hrecD
   rw [hrec] at hborder
   have hh := normalizeMatrix_rep hborder
   exact hh

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

 theorem rational_symmetric_of_positive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
     (hA : (castMatrix A).PosDef) : A.IsSymm := by
   have hs : (castMatrix A).IsSymm := isHermitian_iff_isSymm.mp hA.isHermitian
   change A.transpose=A
   ext i j
   exact Rat.cast_injective (α:=ℝ) (hs.apply _ _)

 
 theorem inversePrefix_succ (orig : SignedMatrix) (k : ℕ) :
     inversePrefix orig (k+1)=inverseStep (k,inversePrefix orig k) := by
   simp only [inversePrefix,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
 theorem inversePrefix_correct {n : ℕ} (orig : SignedMatrix)
     (A : Matrix (Fin n) (Fin n) ℚ) (hA : RepresentsMatrix orig A)
     (hp : (castMatrix A).PosDef) (k : ℕ) (hk : k≤ n) :
     (inversePrefix orig k).1=orig ∧
       RepresentsMatrix (inversePrefix orig k).2 ((principal A k hk)⁻¹) ∧
       ∀ row∈(inversePrefix orig k).2,VectorCanonical row := by
   induction k with
   | zero =>
     refine ⟨rfl,?_,?_⟩
     · refine ⟨fun i : Fin 0 => i.elim0,rfl,?_⟩
       intro i
       exact i.elim0
     · intro row hrow
       cases hrow
   | succ k ih =>
     have hkn : k< n := by omega
     have hprev := ih (by omega)
     have hs := rational_symmetric_of_positive A hp
     have hpos := principal_positive A hp hk
     rw [principal_succ A hs hkn] at hpos
     have hschur := (rational_border_positive _ _ _ hpos).2
     have hnext := inverseNext_correct hkn orig (inversePrefix orig k).2 A hA
       ((principal A k (by omega))⁻¹) hprev.2.1 (ne_of_gt hschur)
     rw [←principal_border_inverse A hp hs hkn] at hnext
     have he : inversePrefix orig k=(orig,(inversePrefix orig k).2) := Prod.ext hprev.1 rfl
     rw [inversePrefix_succ,he]
     exact ⟨rfl,hnext.1,hnext.2⟩

 theorem matrixInverseWords_correct {n : ℕ} (orig : SignedMatrix)
     (A : Matrix (Fin n) (Fin n) ℚ) (hA : RepresentsMatrix orig A)
     (hp : (castMatrix A).PosDef) :
     RepresentsMatrix (matrixInverseWords orig) A⁻¹ ∧
       ∀ row∈matrixInverseWords orig,VectorCanonical row := by
   have hh := inversePrefix_correct orig A hA hp n le_rfl
   have hn : orig.length=n := by obtain ⟨rows,hr,hrows⟩ := hA; rw [hr,List.length_ofFn]
   have hfull : principal A n le_rfl=A := by ext i j; rfl
   rw [hfull] at hh
   simpa only [matrixInverseWords,Function.comp_apply,matrixInverseFold,hn,inversePrefix] using hh.2

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GLSDeterminantBounds
noncomputable section
-- Adapted from EdouardBonnet/lax-109476, commit0a042604c7ae1ef4cd9a4c7d82eb902f313d4864.
-- Apache-2.0; original license retained in external-lp/LICENSE.

open scoped BigOperators Matrix

namespace EdgeSublinearMWIS.Main.GLS.DeterminantBounds

/-- Cancellation in an integer quotient never enlarges numerator or denominator. -/
theorem integer_ratio_num_den_bound (a b : ℤ) (hb : b ≠ 0) :
    ((a : ℚ) / b).num.natAbs ≤ a.natAbs ∧
      ((a : ℚ) / b).den ≤ b.natAbs := by
  obtain ⟨c, hn, hd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den a (d := b) hb
  have hc : c ≠ 0 := by
    intro h
    rw [h, zero_mul] at hd
    exact hb hd
  have hcpos := Int.natAbs_pos.mpr hc
  have hna : a.natAbs = c.natAbs * ((a : ℚ) / b).num.natAbs := by
    simpa only [Int.natAbs_mul] using congrArg Int.natAbs hn
  have hda : b.natAbs = c.natAbs * ((a : ℚ) / b).den := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hd
  constructor
  · rw [hna]
    exact Nat.le_mul_of_pos_left _ hcpos
  · rw [hda]
    exact Nat.le_mul_of_pos_left _ hcpos

/-- The permutation formula bounds an integer determinant by `k! H^k`. -/
theorem determinant_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (H : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ H) :
    A.det.natAbs ≤ (Fintype.card ι).factorial * H ^ Fintype.card ι := by
  have hentry : ∀ i j, |A i j| ≤ (H : ℤ) := by
    intro i j
    simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr (hA i j))
  have hd : |A.det| ≤ ((Fintype.card ι).factorial : ℤ) * (H : ℤ) ^ Fintype.card ι := by
    rw [Matrix.det_apply']
    calc
      _ ≤ ∑ σ : Equiv.Perm ι, |(Equiv.Perm.sign σ : ℤ) * ∏ i, A (σ i) i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ σ : Equiv.Perm ι, ∏ i, |A (σ i) i| := by
        congr 1
        funext σ
        have hs : |(Equiv.Perm.sign σ : ℤ)| = 1 := by
          exact Int.isUnit_iff_abs_eq.mp (Equiv.Perm.sign σ).isUnit
        rw [abs_mul, hs, one_mul, Finset.abs_prod]
      _ ≤ ∑ _σ : Equiv.Perm ι, ∏ _i : ι, (H : ℤ) := by
        apply Finset.sum_le_sum
        intro σ _
        exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hentry _ i)
      _ = _ := by simp [Fintype.card_perm]
  have hd' : (A.det.natAbs : ℤ) ≤
      ((Fintype.card ι).factorial * H ^ Fintype.card ι : ℕ) := by
    simpa only [Int.natCast_natAbs, Nat.cast_mul, Nat.cast_pow] using hd
  exact Int.ofNat_le.mp hd'

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

 theorem inverse_integer_ratio {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
     (M : Matrix (Fin n) (Fin n) ℤ) (D : ℤ) (hD : D≠0) (hM : M.map (Int.cast:ℤ→ℚ)=(D:ℚ) • A)
     (hdet : M.det≠0) (i j : Fin n) : A⁻¹ i j=((D*M.adjugate i j:ℤ):ℚ)/(M.det:ℚ) := by
   let N : Matrix (Fin n) (Fin n) ℚ := M.map (Int.cast:ℤ→ℚ)
   have hdetN : N.det=(M.det:ℚ) := (Int.cast_det M).symm
   have hu : IsUnit N.det := isUnit_iff_ne_zero.mpr (by rw [hdetN]; exact_mod_cast hdet)
   have hinv : A⁻¹=(D:ℚ) • N⁻¹ := by
     apply Matrix.inv_eq_right_inv
     calc
       A*((D:ℚ) • N⁻¹)=((D:ℚ) • A)*N⁻¹ := by rw [Matrix.mul_smul,Matrix.smul_mul]
       _=N*N⁻¹ := by rw [←hM]
       _=1 := Matrix.mul_nonsing_inv N hu
   have hadj : N.adjugate=M.adjugate.map (Int.cast:ℤ→ℚ) := ((Int.castRingHom ℚ).map_adjugate M).symm
   rw [hinv,Matrix.smul_apply,smul_eq_mul,Matrix.inv_def,Matrix.smul_apply,smul_eq_mul,
     Ring.inverse_eq_inv,hdetN,hadj]
   simp only [Matrix.map_apply,Int.cast_mul,div_eq_mul_inv]
   ring

 theorem integer_adjugate_bound {n L : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
     (hM : ∀ i j,(M i j).natAbs≤2^L) (i j : Fin n) :
     (M.adjugate i j).natAbs≤ n.factorial*(2^L)^n := by
   rw [Matrix.adjugate_apply]
   have hentry : ∀ r s,((M.updateRow j (Pi.single i 1)) r s).natAbs≤2^L := by
     intro r s
     by_cases hr : r=j
     · subst r
       simp only [Matrix.updateRow_self,Pi.single_apply]
       split_ifs
       · exact Nat.one_le_pow _ _ (by omega)
       · simp
     · simpa only [Matrix.updateRow_apply,hr,if_false] using hM r s
   simpa only [Fintype.card_fin] using GLS.DeterminantBounds.determinant_bound (M.updateRow j (Pi.single i 1)) (2^L) hentry

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

 
 theorem matrixDen_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : 0< matrixDen A :=
   Finset.prod_pos (fun i _ => Finset.prod_pos (fun j _ => (A i j).den_pos))
 theorem denominator_dvd_matrixDen {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
     (A i j).den∣matrixDen A :=
   (Finset.dvd_prod_of_mem (fun j => (A i j).den) (Finset.mem_univ j)).trans
     (Finset.dvd_prod_of_mem (fun i => ∏ j,(A i j).den) (Finset.mem_univ i))
 theorem matrixDen_bound {n H : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : ∀ i j,(A i j).den≤2^H) :
     matrixDen A≤2^(n*n*H) := by
   have hinner (i : Fin n) : (∏ j,(A i j).den)≤(2^H)^n := by
     calc
       _≤∏ _j : Fin n,2^H := Finset.prod_le_prod' (fun j _ => hA i j)
       _=_ := by simp
   calc
     _≤∏ _i : Fin n,(2^H)^n := Finset.prod_le_prod' (fun i _ => hinner i)
     _=2^(n*n*H) := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul]; congr 1; ring
 
 theorem clearedMatrix_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
     (clearedMatrix A).map (Int.cast:ℤ→ℚ)=(matrixDen A:ℚ) • A := by
   ext i j
   have hm : (matrixDen A/(A i j).den)*(A i j).den=matrixDen A := Nat.div_mul_cancel (denominator_dvd_matrixDen A i j)
   have hd : ((A i j).den:ℚ)≠0 := by exact_mod_cast ne_of_gt (A i j).den_pos
   have he := (A i j).num_div_den
   simp only [Matrix.map_apply,clearedMatrix,Int.cast_mul,Int.cast_natCast,Matrix.smul_apply,smul_eq_mul]
   conv_rhs => rw [←he]
   field_simp
   have hq : (matrixDen A/(A i j).den:ℕ)*( (A i j).den:ℚ)=(matrixDen A:ℚ) := by exact_mod_cast hm
   nlinarith only [congrArg (fun x : ℚ => (A i j).num*x) hq]
 theorem clearedMatrix_bound {n N H : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hn : n≤ N)
     (hA : ∀ i j,(A i j).num.natAbs≤2^H ∧ (A i j).den≤2^H) :
     ∀ i j,((clearedMatrix A) i j).natAbs≤2^((N*N+1)*H) := by
   intro i j
   have hD := matrixDen_bound A (fun i j => (hA i j).2)
   have h1 : n*n*H≤ N*N*H := Nat.mul_le_mul_right H (Nat.mul_le_mul hn hn)
   have hD' := hD.trans (Nat.pow_le_pow_right (by omega : 1≤2) h1)
   have hquot : matrixDen A/(A i j).den≤ matrixDen A := Nat.div_le_self _ _
   calc
     _=(A i j).num.natAbs*(matrixDen A/(A i j).den) := by simp only [clearedMatrix,Int.natAbs_mul,Int.natAbs_natCast]
     _≤2^H*2^(N*N*H) := Nat.mul_le_mul (hA i j).1 (hquot.trans hD')
     _=2^((N*N+1)*H) := by rw [←pow_add]; congr 1; ring
 theorem clearedMatrix_det_ne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hA : IsUnit A.det) :
     (clearedMatrix A).det≠0 := by
   have he : ((clearedMatrix A).det:ℚ)=(matrixDen A:ℚ)^n*A.det := by
     rw [Int.cast_det,clearedMatrix_cast,Matrix.det_smul,Fintype.card_fin]
   have hD : (matrixDen A:ℚ)≠0 := by exact_mod_cast ne_of_gt (matrixDen_pos A)
   have hne : ((clearedMatrix A).det:ℚ)≠0 := by rw [he]; exact mul_ne_zero (pow_ne_zero _ hD) (isUnit_iff_ne_zero.mp hA)
   exact_mod_cast hne

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

 
 theorem inverse_height_bound {n N H : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (hn : n≤ N)
     (hA : ∀ i j,(A i j).num.natAbs≤2^H ∧ (A i j).den≤2^H) (hunit : IsUnit A.det) :
     ∀ i j,(A⁻¹ i j).num.natAbs≤2^(inverseHeight N H) ∧ (A⁻¹ i j).den≤2^(inverseHeight N H) := by
   intro i j
   let M := clearedMatrix A
   let D := matrixDen A
   let L := (N*N+1)*H
   let J := N*N+L*N
   have hM : ∀ i j,(M i j).natAbs≤2^L := clearedMatrix_bound A hn hA
   have hdet := clearedMatrix_det_ne A hunit
   have hDpos : 0< D := matrixDen_pos A
   have hD0 : (D:ℤ)≠0 := by exact_mod_cast ne_of_gt hDpos
   have hD : D≤2^(N*N*H) := by
     have h := matrixDen_bound A (fun i j => (hA i j).2)
     exact h.trans (Nat.pow_le_pow_right (by omega : 1≤2) (Nat.mul_le_mul_right H (Nat.mul_le_mul hn hn)))
   have hfac : n.factorial≤2^(N*N) := (LLLBounds.factorial_le_two_square n).trans
     (Nat.pow_le_pow_right (by omega : 1≤2) (Nat.mul_le_mul hn hn))
   have hpow : (2^L)^n≤2^(L*N) := by rw [←pow_mul]; exact Nat.pow_le_pow_right (by omega : 1≤2) (Nat.mul_le_mul_left L hn)
   have hprod : n.factorial*(2^L)^n≤2^J := by
     have hh := Nat.mul_le_mul hfac hpow
     simpa only [J,pow_add] using hh
   have hadj := (integer_adjugate_bound M hM i j).trans hprod
   have hdetbd : M.det.natAbs≤2^J := by
     have hh := GLS.DeterminantBounds.determinant_bound M (2^L) hM
     simp only [Fintype.card_fin] at hh
     exact hh.trans hprod
   have hformula := inverse_integer_ratio A M (D:ℤ) hD0 (clearedMatrix_cast A) hdet i j
   have hratio := GLS.DeterminantBounds.integer_ratio_num_den_bound ((D:ℤ)*M.adjugate i j) M.det hdet
   rw [←hformula] at hratio
   have hnum : ((D:ℤ)*M.adjugate i j).natAbs≤2^(inverseHeight N H) := by
     rw [Int.natAbs_mul,Int.natAbs_natCast]
     have hh := Nat.mul_le_mul hD hadj
     simpa only [inverseHeight,J,L,pow_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hh
   have hden : 2^J≤2^(inverseHeight N H) := Nat.pow_le_pow_right (by omega : 1≤2) (by dsimp [J,L,inverseHeight]; omega)
   exact ⟨hratio.1.trans hnum,hratio.2.trans (hdetbd.trans hden)⟩

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

 theorem inverseHeight_power_bound (n H z : ℕ) (hz : 1≤ z) (hn : n≤ z) (hH : H≤ z) : inverseHeight n H≤4*z^4 := by
   have hn2 := Nat.mul_le_mul hn hn
   have hz2 : 1≤ z^2 := one_le_pow₀ hz
   have h1 := Nat.mul_le_mul hn2 hH
   have h2 : (n*n+1)*H*n≤2*z^4 := by
     have ha : n*n+1≤2*z^2 := by nlinarith
     have hb := Nat.mul_le_mul hH hn
     have hh := Nat.mul_le_mul ha hb
     have he : (n*n+1)*(H*n)=(n*n+1)*H*n := by ring
     rw [he] at hh
     nlinarith only [hh]
   have hp2 : z^2≤ z^4 := Nat.pow_le_pow_right hz (by omega)
   have hp3 : z^3≤ z^4 := Nat.pow_le_pow_right hz (by omega)
   dsimp [inverseHeight]
   nlinarith

 theorem inversePrefix_volume {n H : ℕ} (orig : SignedMatrix)
     (A : Matrix (Fin n) (Fin n) ℚ) (hA : RepresentsMatrix orig A)
     (hp : (castMatrix A).PosDef)
     (hsize : ∀ i j,(A i j).num.natAbs≤2^H ∧ (A i j).den≤2^H)
     (k : ℕ) (hk : k≤ n) :
     volume (inversePrefix orig k)≤ volume orig+(n*(n*(14*(inverseHeight n H+2)+1)+2)+1)+1 := by
   have hh := inversePrefix_correct orig A hA hp k hk
   have hprincipal := principal_positive A hp hk
   have hinv := inverse_height_bound (principal A k hk) hk
     (fun i j => hsize _ _) (castMatrix_unit _ hprincipal)
   have hvol := rational_matrix_word_volume (inversePrefix orig k).2 _ hh.2.1 hh.2.2 hinv
   have hm : k*(k*(14*(inverseHeight n H+2)+1)+2)+1≤ n*(n*(14*(inverseHeight n H+2)+1)+2)+1 := by gcongr
   have he := volume_pair_eta (inversePrefix orig k)
   rw [hh.1] at he
   omega

 theorem inversePrefix_volume_power {n H : ℕ} (orig : SignedMatrix)
     (A : Matrix (Fin n) (Fin n) ℚ) (hA : RepresentsMatrix orig A)
     (hp : (castMatrix A).PosDef)
     (hsize : ∀ i j,(A i j).num.natAbs≤2^H ∧ (A i j).den≤2^H)
     (k : ℕ) (hk : k≤ n) (z : ℕ) (hinput : volume orig+n+H+4≤ z) :
     volume (inversePrefix orig k)≤400*z^6 := by
   have hz : 1≤ z := by omega
   have hn : n≤ z := by omega
   have hH : H≤ z := by omega
   have hvol := inversePrefix_volume orig A hA hp hsize k hk
   have hJ := inverseHeight_power_bound n H z hz hn hH
   have hp4 : 1≤ z^4 := one_le_pow₀ hz
   have hbase : 14*(inverseHeight n H+2)+1≤85*z^4 := by nlinarith
   have hn2 : n*n≤ z^2 := by nlinarith [Nat.mul_le_mul hn hn]
   have hm := Nat.mul_le_mul hn2 hbase
   have hp2 : z^2≤ z^6 := Nat.pow_le_pow_right hz (by omega)
   have hp1 : z≤ z^6 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤6)
   have he : z^2*(85*z^4)=85*z^6 := by ring
   rw [he] at hm
   have h0 : 1≤ z^6 := one_le_pow₀ hz
   nlinarith

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

 theorem matrixInverseFold_polynomial_time :
     ∃ C q : ℕ,0< C ∧ ∀ n H (orig : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ),
       RepresentsMatrix orig A → (castMatrix A).PosDef →
       (∀ i j,(A i j).num.natAbs≤2^H ∧ (A i j).den≤2^H) →
       matrixInverseFoldRealizer.time orig≤ C*(volume orig+n+H+4)^q ∧
       volume (matrixInverseFold orig)≤ C*(volume orig+n+H+4)^q := by
   obtain ⟨C,q,hC,hfold⟩ := polynomial_composed_fold_clock matrixInverseInitialize_polynomial inverseStep_polynomial 400 6
   refine ⟨C,q,hC,?_⟩
   intro n H orig A hA hp hsize
   have hn : orig.length=n := by obtain ⟨rows,hr,hrows⟩ := hA; rw [hr,List.length_ofFn]
   let z := volume orig+n+H+4
   have hz : volume orig+1≤ z := by dsimp [z]; omega
   have hpref : ∀ j,j≤(matrixInverseInitialize orig).1.length →
       volume (((matrixInverseInitialize orig).1.take j).foldl (fun state i => inverseStep (i,state)) (matrixInverseInitialize orig).2)≤400*z^6 := by
     intro j hj
     change j≤(List.range orig.length).length at hj
     simp only [List.length_range,hn] at hj
     change volume (((List.range orig.length).take j).foldl (fun state i => inverseStep (i,state)) (orig,[]))≤ _
     rw [hn,List.take_range,Nat.min_eq_left hj]
     exact inversePrefix_volume_power orig A hA hp hsize j hj z le_rfl
   have hh := hfold orig z hz hpref
   exact hh

 theorem matrixInverseWords_polynomial_time :
     ∃ C q : ℕ,0< C ∧ ∀ n H (orig : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ),
       RepresentsMatrix orig A → (castMatrix A).PosDef →
       (∀ i j,(A i j).num.natAbs≤2^H ∧ (A i j).den≤2^H) →
       matrixInverseWordsRealizer.time orig≤ C*(volume orig+n+H+4)^q ∧
       volume (matrixInverseWords orig)≤ C*(volume orig+n+H+4)^q := by
   obtain ⟨C,q,hC,hfold⟩ := matrixInverseFold_polynomial_time
   refine ⟨20*C+20,q+1,by positivity,?_⟩
   intro n H orig A hA hp hsize
   have hh := hfold n H orig A hA hp hsize
   let z := volume orig+n+H+4
   have hz : 1≤ z := by dsimp [z]; omega
   have hq : z^q≤ z^(q+1) := Nat.pow_le_pow_right hz (by omega)
   have h1 : 1≤ z^(q+1) := one_le_pow₀ hz
   have htime := hh.1.trans (Nat.mul_le_mul_left C hq)
   have hvol := hh.2.trans (Nat.mul_le_mul_left C hq)
   constructor
   · have he := Realizer.time_comp matrixInverseFoldRealizer (Realizer.snd : Realizer (Prod.snd : MatrixInverseState → SignedMatrix)) orig
     rw [Realizer.time_snd] at he
     have hb : matrixInverseWordsRealizer.time orig=matrixInverseFoldRealizer.time orig+volume (matrixInverseFold orig)+2+10*(volume (matrixInverseFold orig)+1) := he
     rw [hb]
     change _≤(20*C+20)*z^(q+1)
     nlinarith
   · have hv := volume_pair_eta (matrixInverseFold orig)
     have he : matrixInverseWords orig=(matrixInverseFold orig).2 := rfl
     rw [he]
     change volume (matrixInverseFold orig).2≤(20*C+20)*z^(q+1)
     nlinarith

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

 
 
 
 theorem thinDirectionReciprocal_polynomial : PolyBound thinDirectionReciprocalRealizer := polynomial_comp
   (linear_polynomial (linear_pair (linear_constant scalarOne) (linear_comp linear_snd linear_snd))) canonicalDiv_polynomial
 
 
 theorem thinDirectionColumn_polynomial : PolyBound thinDirectionColumnRealizer := polynomial_comp
   (linear_polynomial (linear_pair linear_fst (linear_comp linear_snd linear_fst))) matrixColumn_polynomial
 
 
 theorem normalizedDirectionWords_polynomial : PolyBound normalizedDirectionWordsRealizer := polynomial_comp
   (polynomial_pair thinDirectionColumn_polynomial thinDirectionReciprocal_polynomial) vectorScale_polynomial
 
 
 theorem thinDirectionData_polynomial : PolyBound thinDirectionDataRealizer := polynomial_pair
   (linear_polynomial linear_id) maximumDiagonal_polynomial
 
 
 theorem thinDirectionFinish_polynomial : PolyBound thinDirectionFinishRealizer := polynomial_pair
   normalizedDirectionWords_polynomial (linear_polynomial (linear_comp linear_snd linear_fst))
 
 
 theorem inverseThinDirection_polynomial : PolyBound inverseThinDirectionRealizer := polynomial_comp
   thinDirectionData_polynomial thinDirectionFinish_polynomial
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationModuliCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 theorem commonDenominator_polynomial : PolyBound commonDenominatorRealizer :=
   polynomial_comp (polynomial_mapList (linear_polynomial (linear_comp linear_snd linear_snd))) wordProduct_polynomial
 
 
 theorem precisionSum_polynomial : PolyBound precisionSum := polynomial_comp
   (polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_fst)
     (polynomial_comp (linear_polynomial linear_snd) listLength_polynomial)) BinaryGcd.nat_add_polynomial)
     (linear_polynomial natSucc_linear)) (linear_polynomial natSucc_linear)
 
 theorem precisionExponent_polynomial : PolyBound precisionExponentRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (polynomial_comp (linear_polynomial linear_snd) listLength_polynomial)
     (linear_polynomial natSucc_linear)) precisionSum_polynomial) naturalProduct_polynomial
 
 
 theorem approximationModuli_polynomial : PolyBound approximationModuliRealizer := polynomial_pair
   (polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) commonDenominator_polynomial)
     (polynomial_comp precisionExponent_polynomial powerTwoWord_polynomial)) multiply_polynomial)
   (polynomial_comp (linear_polynomial linear_snd) commonDenominator_polynomial)
 
 
 theorem approximationMatrixWords_polynomial : PolyBound approximationMatrixWordsRealizer :=
   polynomial_comp (polynomial_pair (linear_polynomial linear_snd) approximationModuli_polynomial) approximationWords_polynomial

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

 
 theorem denominatorProduct_pos {n : ℕ} (q : Fin n → RationalCode) : 0< denominatorProduct q :=
   Finset.prod_pos (fun i _ => (q i).positive)
 theorem denominator_dvd_product {n : ℕ} (q : Fin n → RationalCode) (i : Fin n) :
     (q i).denominator∣denominatorProduct q := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
 theorem commonDenominator_codes {n : ℕ} (q : Fin n → RationalCode) :
     value (commonDenominatorWord (List.ofFn (fun i => codeWords (q i))))=denominatorProduct q := by
   simp only [commonDenominatorWord,wordProduct_value,List.map_ofFn,Function.comp_def,
     codeWords,value_natBits,List.prod_ofFn,denominatorProduct]
 theorem approximationModuli_codes {n : ℕ} (q : Fin n → RationalCode) (r : ℕ) :
     value (approximationModuli (r,List.ofFn (fun i => codeWords (q i)))).1=
       denominatorProduct q*2^((n+1)*(r+n+2)) ∧
     value (approximationModuli (r,List.ofFn (fun i => codeWords (q i)))).2=denominatorProduct q := by
   simp only [approximationModuli,multiply_value,powerTwoWord_value,commonDenominator_codes,
     precisionExponent,List.length_ofFn,and_self]
 
 theorem approximationNumerator_correct {n : ℕ} (q : Fin n → RationalCode) (r : ℕ) (i : Fin n) :
     ((q i).value:ℝ)*(denominatorProduct q*2^((n+1)*(r+n+2)):ℕ)=
       (approximationNumerator q r i:ℝ) := by
   have hd : (q i).denominator≠0 := ne_of_gt (q i).positive
   have hm := Nat.div_mul_cancel (denominator_dvd_product q i)
   have hmR : (denominatorProduct q/(q i).denominator:ℕ)*( (q i).denominator:ℝ)=(denominatorProduct q:ℝ) := by exact_mod_cast hm
   simp only [RationalCode.value,Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,approximationNumerator,
     Int.cast_mul,Int.cast_natCast,Int.cast_pow,Int.cast_ofNat,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
   have hdR : ((q i).denominator:ℝ)≠0 := by exact_mod_cast hd
   field_simp
   nlinarith only [congrArg (fun x : ℝ => (q i).numerator*x) hmR]

 theorem approximationMatrixWords_rep {n : ℕ} (q : Fin n → RationalCode) (r : ℕ) :
     ∃ rows : Fin (n+1) → SignedVector,
       approximationMatrixWords (r,List.ofFn (fun i => codeWords (q i)))=List.ofFn rows ∧
       ∀ i,RepresentsVector (rows i)
         (embed (approximationBasis (approximationNumerator q r)
           (denominatorProduct q*2^((n+1)*(r+n+2))) (denominatorProduct q)) i) := by
   let A : Fin n → SignedWords := fun i => codeWords (q i)
   let mods := approximationModuli (r,List.ofFn A)
   have hv := approximationModuli_codes q r
   obtain ⟨rows,hr,hrows⟩ := approximationWords_rep (approximationNumerator q r) mods.1 mods.2 A
     (fun i => by change 0< value (natBits (q i).denominator); rw [value_natBits]; exact (q i).positive)
     (fun i => by rw [signedFractionValue_code]; rw [hv.1]; exact approximationNumerator_correct q r i)
   refine ⟨rows,hr,?_⟩
   intro i
   dsimp only [mods,A] at hrows
   simpa only [hv.1,hv.2,Int.natCast_mul,Int.natCast_pow,Nat.cast_ofNat] using hrows i

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

 
 
 theorem approximationInput_polynomial : PolyBound approximationInputRealizer :=
   polynomial_comp approximationMatrixWords_polynomial serializeMatrix_polynomial
 
 

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

 theorem polynomial_comp_restricted {f : α → β} {g : β → γ} (R : Realizer f) (S : Realizer g)
     (P : α → Prop)
     (hR : ∃ A p : ℕ,0< A ∧ ∀ x,P x → R.time x≤ A*(volume x+1)^p ∧ volume (f x)≤ A*(volume x+1)^p)
     (hS : ∃ D q : ℕ,0< D ∧ ∀ x,P x → S.time (f x)≤ D*(volume (f x)+1)^q ∧ volume (g (f x))≤ D*(volume (f x)+1)^q) :
     ∃ C e : ℕ,0< C ∧ ∀ x,P x →
       (R.comp S).time x≤ C*(volume x+1)^e ∧ volume (g (f x))≤ C*(volume x+1)^e := by
   obtain ⟨A,p,hA,hR⟩ := hR
   obtain ⟨D,q,hD,hS⟩ := hS
   refine ⟨D*(A+1)^q+20*A+20,p+(p+1)*q+2,by positivity,?_⟩
   intro x hx
   let z := volume x+1
   let v := volume (f x)
   have hz : 1≤ z := by dsimp [z]; omega
   have hi := hR x hx
   have hl := hS x hx
   have hbase : v+1≤ v+z := by omega
   have ht := hl.1.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hbase q))
   have hv := hl.2.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hbase q))
   have htime := RuntimeMath.polynomial_pipeline_clock z A p D q (R.time x) v (S.time (f x)) hz hi.1 hi.2 ht
   have hout := RuntimeMath.polynomial_pipeline_clock z A p D q (R.time x) v (volume (g (f x))) hz hi.1 hi.2 hv
   constructor
   · rw [Realizer.time_comp]
     exact htime
   · change volume (g (f x))≤(D*(A+1)^q+20*A+20)*z^(p+(p+1)*q+2)
     omega

 theorem polynomial_restrict {f : α → β} (R : Realizer f) (P : α → Prop) (hR : PolyBound R) :
     ∃ A p : ℕ,0< A ∧ ∀ x,P x → R.time x≤ A*(volume x+1)^p ∧ volume (f x)≤ A*(volume x+1)^p := by
   obtain ⟨A,p,hA,hR⟩ := hR
   exact ⟨A,p,hA,fun x _ => hR x⟩

 theorem polynomial_pair_restricted {f : α → β} {g : α → γ} {R : Realizer f} {S : Realizer g}
    (P : α → Prop)
    (hR : ∃ C q : ℕ,0< C ∧ ∀ x,P x → R.time x≤ C*(volume x+1)^q ∧ volume (f x)≤ C*(volume x+1)^q)
    (hS : ∃ D r : ℕ,0< D ∧ ∀ x,P x → S.time x≤ D*(volume x+1)^r ∧ volume (g x)≤ D*(volume x+1)^r) :
    ∃ C e : ℕ,0< C ∧ ∀ x,P x → (R.pair S).time x≤ C*(volume x+1)^e ∧ volume (f x,g x)≤ C*(volume x+1)^e := by
   obtain ⟨C,q,hC,hR⟩ := hR
   obtain ⟨D,r,hD,hS⟩ := hS
   refine ⟨100*(C+D+1),q+r+1,by positivity,?_⟩
   intro x hx
   let z := volume x+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hp : z≤ z^(q+r+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+r+1)
   have hq : z^q≤ z^(q+r+1) := Nat.pow_le_pow_right hz (by omega)
   have hr : z^r≤ z^(q+r+1) := Nat.pow_le_pow_right hz (by omega)
   have h1 := hR x hx
   have h2 := hS x hx
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

 
 
 theorem approximationIntegerBasis_independent {n : ℕ} (q : Fin n → RationalCode) (r : ℕ) :
     LinearIndependent ℝ (embed (approximationIntegerBasis q r)) := by
   apply embed_independent_of_det_ne_zero
   rw [approximationIntegerBasis,approximationBasis_det]
   have hu : (denominatorProduct q:ℤ)≠0 := by exact_mod_cast ne_of_gt (denominatorProduct_pos q)
   exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hu (pow_ne_zero _ (by norm_num)))) hu
 theorem approximationInput_codes {n : ℕ} (q : Fin n → RationalCode) (r : ℕ) :
     approximationInput (r,List.ofFn (fun i => codeWords (q i)))=integerMatrixInput (approximationIntegerBasis q r) := by
   obtain ⟨rows,hr,hrows⟩ := approximationMatrixWords_rep q r
   rw [approximationInput,Function.comp_apply,hr]
   exact serializeMatrix_rep (approximationIntegerBasis q r) rows hrows

 

 theorem approximationReduced_polynomial_time :
     ∃ C e : ℕ,0< C ∧ ∀ s : ℕ×SignedVector,ValidApproximationInput s →
       approximationReducedWordsRealizer.time s≤ C*(volume s+1)^e ∧
       volume (approximationReducedWords s)≤ C*(volume s+1)^e := by
   have hpre := polynomial_restrict approximationInputRealizer ValidApproximationInput approximationInput_polynomial
   have hlll : ∃ D q : ℕ,0< D ∧ ∀ s,ValidApproximationInput s →
       integerLLLRealizer.time (approximationInput s)≤ D*(volume (approximationInput s)+1)^q ∧
       volume (integerLLL (approximationInput s))≤ D*(volume (approximationInput s)+1)^q := by
     obtain ⟨D,q,hD,hlll⟩ := integerLLL_polynomial_time
     refine ⟨D,q,hD,?_⟩
     rintro ⟨r,A⟩ ⟨n,q,rfl⟩
     rw [approximationInput_codes]
     exact hlll _ _ (approximationIntegerBasis_independent q r)
   have hcore := polynomial_comp_restricted approximationInputRealizer integerLLLRealizer ValidApproximationInput hpre hlll
   have hparse : ∃ D q : ℕ,0< D ∧ ∀ s,ValidApproximationInput s →
       parseIntegerMatrixRealizer.time (integerLLL (approximationInput s))≤ D*(volume (integerLLL (approximationInput s))+1)^q ∧
       volume (parseIntegerMatrix (integerLLL (approximationInput s)))≤ D*(volume (integerLLL (approximationInput s))+1)^q := by
     obtain ⟨D,q,hD,hparse⟩ := parseIntegerMatrix_polynomial
     exact ⟨D,q,hD,fun s _ => hparse _⟩
   have h := polynomial_comp_restricted (approximationInputRealizer.comp integerLLLRealizer)
     parseIntegerMatrixRealizer ValidApproximationInput hcore hparse
   simpa only [approximationReducedWordsRealizer,approximationReducedWords,Function.comp_apply] using h

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationExtractCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 theorem extractBasisLast_polynomial : PolyBound extractBasisLastRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_snd))
     (polynomial_comp (linear_polynomial linear_fst) listLength_polynomial)) (lookupList_polynomial zeroSignedWord)
 
 
 theorem extractApproximationDenominator_polynomial : PolyBound extractApproximationDenominatorRealizer := polynomial_comp
   (polynomial_pair extractBasisLast_polynomial
     (linear_polynomial (linear_comp (linear_comp (linear_comp linear_snd linear_fst) linear_snd) unsignedInteger_linear))) canonicalDiv_polynomial
 
 theorem extractReciprocal_polynomial : PolyBound extractReciprocalRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_constant (unsignedIntegerWord [true])))
     (linear_polynomial (linear_comp (linear_comp (linear_comp linear_snd linear_fst) linear_fst) unsignedInteger_linear))) canonicalDiv_polynomial
 
 theorem extractBasisPrefix_polynomial : PolyBound extractBasisPrefixRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) listLength_polynomial)
     (linear_polynomial (linear_comp linear_snd linear_snd))) takeList_polynomial
 
 
 theorem extractApproximationNumerators_polynomial : PolyBound extractApproximationNumeratorsRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (polynomial_pair (linear_polynomial linear_fst) extractApproximationDenominator_polynomial) vectorScale_polynomial)
     (polynomial_comp (polynomial_pair extractBasisPrefix_polynomial extractReciprocal_polynomial) vectorScale_polynomial)) vectorSub_polynomial
 
 
 theorem extractApproximation_polynomial : PolyBound extractApproximationRealizer :=
   polynomial_pair extractApproximationNumerators_polynomial extractApproximationDenominator_polynomial

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

 theorem approximationExtractionData_polynomial_time :
     ∃ C e : ℕ,0< C ∧ ∀ s : ℕ×SignedVector,ValidApproximationInput s →
       approximationExtractionDataRealizer.time s≤ C*(volume s+1)^e ∧
       volume (approximationExtractionData s)≤ C*(volume s+1)^e := by
   have hred := approximationReduced_polynomial_time
   have hhead : ∃ D q : ℕ,0< D ∧ ∀ s : ℕ×SignedVector,ValidApproximationInput s →
       (headList ([]:SignedVector)).time (approximationReducedWords s)≤ D*(volume (approximationReducedWords s)+1)^q ∧
       volume ((approximationReducedWords s).headD [])≤ D*(volume (approximationReducedWords s)+1)^q := by
     obtain ⟨D,q,hD,hh⟩ := headList_polynomial ([]:SignedVector)
     exact ⟨D,q,hD,fun s _ => hh _⟩
   have hlast := polynomial_comp_restricted approximationReducedWordsRealizer (headList ([]:SignedVector))
     ValidApproximationInput hred hhead
   have hfirst : ∃ C e : ℕ,0< C ∧ ∀ s : ℕ×SignedVector,ValidApproximationInput s →
       approximationFirstReducedRealizer.time s≤ C*(volume s+1)^e ∧
       volume (approximationFirstReduced s)≤ C*(volume s+1)^e := by
     simpa only [approximationFirstReduced,approximationFirstReducedRealizer,Function.comp_apply] using hlast
   have hmod := polynomial_restrict approximationModuliRealizer ValidApproximationInput approximationModuli_polynomial
   have hpair := polynomial_pair_restricted (f:=approximationModuli) (g:=approximationFirstReduced) (R:=approximationModuliRealizer) (S:=approximationFirstReducedRealizer) ValidApproximationInput hmod hfirst
   have hsnd := polynomial_restrict (Realizer.snd : Realizer (Prod.snd : ℕ×SignedVector → SignedVector))
     ValidApproximationInput (linear_polynomial linear_snd)
   have h := polynomial_pair_restricted (R:=(Realizer.snd : Realizer (Prod.snd : ℕ×SignedVector → SignedVector)))
     (S:=approximationModuliRealizer.pair approximationFirstReducedRealizer) ValidApproximationInput hsnd hpair
   simpa only [approximationExtractionDataRealizer,approximationExtractionData,Function.comp_apply] using h

 theorem simultaneousApproximation_polynomial_time :
     ∃ C e : ℕ,0< C ∧ ∀ s : ℕ×SignedVector,ValidApproximationInput s →
       simultaneousApproximationRealizer.time s≤ C*(volume s+1)^e ∧
       volume (simultaneousApproximation s)≤ C*(volume s+1)^e := by
   have hpost : ∃ D q : ℕ,0< D ∧ ∀ s : ℕ×SignedVector,ValidApproximationInput s →
       extractApproximationRealizer.time (approximationExtractionData s)≤ D*(volume (approximationExtractionData s)+1)^q ∧
       volume (extractApproximation (approximationExtractionData s))≤ D*(volume (approximationExtractionData s)+1)^q := by
     obtain ⟨D,q,hD,hh⟩ := extractApproximation_polynomial
     exact ⟨D,q,hD,fun s _ => hh _⟩
   have h := polynomial_comp_restricted approximationExtractionDataRealizer extractApproximationRealizer
     ValidApproximationInput approximationExtractionData_polynomial_time hpost
   simpa only [simultaneousApproximationRealizer,simultaneousApproximation,Function.comp_apply] using h

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

 
 theorem rationalCode_value (q : ℚ) : (rationalCode q).value=q := Rat.num_div_den q
 theorem normalizeVector_codes {n : ℕ} (A : SignedVector) (a : Fin n → ℚ)
     (hA : RepresentsVector A (rationalVector a)) :
     normalizeVector A=List.ofFn (fun i => codeWords (rationalCode (a i))) := by
   obtain ⟨words,rfl,hD,hv⟩ := hA
   simp only [normalizeVector,List.map_ofFn]
   congr 1
   funext i
   have he : signedFractionValue (words i)=a i := Rat.cast_injective (α:=ℝ) (hv i)
   simp only [Function.comp_apply]
   rw [signedReduced_canonical _ (hD i),he]
   rfl

 
 
 theorem canonicalApproximationInput_polynomial : PolyBound canonicalApproximationInputRealizer := polynomial_pair
   (linear_polynomial linear_fst) (polynomial_comp (linear_polynomial linear_snd) normalizeVector_polynomial)
 
 

 

 
 theorem canonicalApproximation_polynomial_time :
     ∃ C e : ℕ,0 < C ∧ ∀ s : ℕ×SignedVector,ValidRationalVector s →
       canonicalApproximationRealizer.time s ≤ C*(volume s+1)^e ∧
       volume (canonicalApproximation s) ≤ C*(volume s+1)^e := by
   have hpre := polynomial_restrict canonicalApproximationInputRealizer ValidRationalVector canonicalApproximationInput_polynomial
   obtain ⟨D,q,hD,hApprox⟩ := simultaneousApproximation_polynomial_time
   have hpost : ∃ D q : ℕ,0 < D ∧ ∀ s : ℕ×SignedVector,ValidRationalVector s →
       simultaneousApproximationRealizer.time (canonicalApproximationInput s) ≤ D*(volume (canonicalApproximationInput s)+1)^q ∧
       volume (simultaneousApproximation (canonicalApproximationInput s)) ≤ D*(volume (canonicalApproximationInput s)+1)^q := by
     refine ⟨D,q,hD,?_⟩
     intro s hs
     obtain ⟨n,a,ha⟩ := hs
     apply hApprox
     refine ⟨n,fun i => rationalCode (a i),?_⟩
     exact normalizeVector_codes s.2 a ha
   exact polynomial_comp_restricted canonicalApproximationInputRealizer simultaneousApproximationRealizer ValidRationalVector hpre hpost

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

 
 
 
 theorem hyperplaneBeta_polynomial : PolyBound hyperplaneBetaRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial (linear_comp linear_fst natSucc_linear)) naturalSignedWord_polynomial)
     (polynomial_comp (linear_polynomial linear_snd) signedDot_polynomial)) canonicalMul_polynomial
 
 
 theorem hyperplaneCoordinates_polynomial : PolyBound hyperplaneCoordinatesRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_fst)) hyperplaneBeta_polynomial) appendCoordinate_polynomial
 
 
 theorem hyperplanePrecision_polynomial : PolyBound hyperplanePrecisionRealizer :=
   linear_polynomial (linear_comp (linear_comp (linear_comp linear_fst natSucc_linear) natSucc_linear) natSucc_linear)
 
 
 theorem hyperplaneApproximationData_polynomial : PolyBound hyperplaneApproximationDataRealizer := polynomial_pair
   hyperplanePrecision_polynomial hyperplaneCoordinates_polynomial
 
 

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

 
 
 theorem dyadicUnitWord_polynomial : PolyBound dyadicUnitWordRealizer := polynomial_pair
   (linear_polynomial (linear_constant false)) (polynomial_pair (linear_polynomial (linear_constant [true])) powerTwoWord_polynomial)
 theorem dyadicUnitWord_den (p : ℕ) : 0< value (dyadicUnitWord p).2.2 := by change 0< value (powerTwoWord p); rw [powerTwoWord_value]; positivity
 theorem dyadicUnitWord_value (p : ℕ) : signedFractionValue (dyadicUnitWord p)=1/(2:ℚ)^p := by
   simp [dyadicUnitWord,signedFractionValue,signedValue,powerTwoWord_value,value]
 
 
 theorem enlargedUnitWord_polynomial : PolyBound enlargedUnitWordRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_constant scalarOne)) dyadicUnitWord_polynomial) canonicalAdd_polynomial
 theorem enlargedUnitWord_correct (p : ℕ) :
     0< value (enlargedUnitWord p).2.2 ∧ signedFractionValue (enlargedUnitWord p)=1+1/(2:ℚ)^p := by
   refine ⟨canonicalAdd_denpos _ _ scalarOne_den (dyadicUnitWord_den p),?_⟩
   rw [enlargedUnitWord,canonicalAdd_value _ _ scalarOne_den (dyadicUnitWord_den p),scalarOne_value,dyadicUnitWord_value]
 
 
 theorem enlargementCoefficient_polynomial : PolyBound enlargementCoefficientRealizer := polynomial_comp
   (polynomial_pair enlargedUnitWord_polynomial enlargedUnitWord_polynomial) canonicalMul_polynomial
 theorem enlargementCoefficient_correct (p : ℕ) :
     0< value (enlargementCoefficient p).2.2 ∧ signedFractionValue (enlargementCoefficient p)=(1+1/(2:ℚ)^p)^2 := by
   refine ⟨canonicalMul_denpos _ _ (enlargedUnitWord_correct p).1 (enlargedUnitWord_correct p).1,?_⟩
   rw [enlargementCoefficient,Function.comp_apply,canonicalMul_value _ _ (enlargedUnitWord_correct p).1 (enlargedUnitWord_correct p).1,
     (enlargedUnitWord_correct p).2]
   ring
 
 
 theorem roundingAllowance_polynomial : PolyBound roundingAllowanceRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) naturalSignedWord_polynomial)
     (polynomial_comp (linear_polynomial linear_snd) dyadicUnitWord_polynomial)) canonicalMul_polynomial
 theorem roundingAllowance_correct (n p : ℕ) :
     0< value (roundingAllowance (n,p)).2.2 ∧ signedFractionValue (roundingAllowance (n,p))=(n:ℚ)/(2:ℚ)^p := by
   refine ⟨canonicalMul_denpos _ _ (naturalSignedWord_den n) (dyadicUnitWord_den p),?_⟩
   rw [roundingAllowance,canonicalMul_value _ _ (naturalSignedWord_den n) (dyadicUnitWord_den p),naturalSignedWord_value,dyadicUnitWord_value]
   ring

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

 
 
 
 theorem cutDirection_polynomial : PolyBound cutDirectionRealizer := polynomial_comp (linear_polynomial linear_snd) matrixVector_polynomial
 
 
 theorem cutQuadratic_polynomial : PolyBound cutQuadraticRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_snd)) cutDirection_polynomial) signedDot_polynomial
 
 
 theorem cutRankOne_polynomial : PolyBound cutRankOneRealizer := polynomial_comp
   (polynomial_pair cutDirection_polynomial cutDirection_polynomial) matrixOuter_polynomial
 
 
 theorem cutRankScalar_polynomial : PolyBound cutRankScalarRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial linear_fst) cutQuadratic_polynomial) shapeCutCoefficient_polynomial
 
 
 theorem cutRankCorrection_polynomial : PolyBound cutRankCorrectionRealizer := polynomial_comp
   (polynomial_pair cutRankOne_polynomial cutRankScalar_polynomial) matrixScale_polynomial
 
 
 theorem cutDifference_polynomial : PolyBound cutDifferenceRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_fst)) cutRankCorrection_polynomial) matrixSub_polynomial
 
 
 theorem cutShapeWords_polynomial : PolyBound cutShapeWordsRealizer := polynomial_comp
   (polynomial_pair cutDifference_polynomial (polynomial_comp (linear_polynomial linear_fst) shapeDimensionCoefficient_polynomial)) matrixScale_polynomial

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

 theorem cutDirection_correct {n : ℕ} (bs : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ)
     (hA : RepresentsMatrix bs A) (v : SignedVector) (a : Fin n → ℚ)
     (ha : RepresentsVector v (rationalVector a)) :
     RepresentsVector (cutDirection (n,(bs,v))) (rationalVector (A *ᵥ a)) :=
   represents_matrix_vector bs A hA v a ha
 theorem cutQuadratic_correct {n : ℕ} (bs : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ)
     (hA : RepresentsMatrix bs A) (v : SignedVector) (a : Fin n → ℚ)
     (ha : RepresentsVector v (rationalVector a)) :
     0< value (cutQuadratic (n,(bs,v))).2.2 ∧
       signedFractionValue (cutQuadratic (n,(bs,v)))=a ⬝ᵥ (A *ᵥ a) :=
   represents_rational_dot v (cutDirection (n,(bs,v))) a (A *ᵥ a) ha (cutDirection_correct bs A hA v a ha)
 theorem cutShapeWords_correct {n : ℕ} (hn : 2≤ n) (bs : SignedMatrix)
     (A : Matrix (Fin n) (Fin n) ℚ) (hA : RepresentsMatrix bs A)
     (v : SignedVector) (a : Fin n → ℚ) (ha : RepresentsVector v (rationalVector a))
     (hq : a ⬝ᵥ (A *ᵥ a)≠0) :
     RepresentsMatrix (cutShapeWords (n,(bs,v))) (GLS.EllipsoidBounds.cutShape n A a) := by
   let s := (n,(bs,v))
   have hd := cutDirection_correct bs A hA v a ha
   have hquad := cutQuadratic_correct bs A hA v a ha
   have hqne : signedFractionValue (cutQuadratic s)≠0 := by rw [hquad.2]; exact hq
   have hbeta := shapeCutCoefficient_correct n (cutQuadratic s) hquad.1 hqne
   have halpha := shapeDimensionCoefficient_correct n hn
   have houter := represents_matrix_outer (cutDirection s) (cutDirection s) (A *ᵥ a) (A *ᵥ a) hd hd
   have hcorr := represents_matrix_scale (cutRankOne s) (Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a)) houter
     (cutRankScalar s) hbeta.1
   have hsub := represents_matrix_sub bs (cutRankCorrection s) A _ hA hcorr
   have hscaled := represents_matrix_scale (cutDifference s) _ hsub (shapeDimensionCoefficient n) halpha.1
   rw [halpha.2] at hscaled
   have hb : signedFractionValue (cutRankScalar s)=2/(((n:ℚ)+1)*(a ⬝ᵥ (A *ᵥ a))) := by simpa only [cutRankScalar,s,hquad.2] using hbeta.2
   rw [hb] at hscaled
   exact hscaled

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

 
 
 theorem diagonalRow_polynomial : PolyBound diagonalRowRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) range_polynomial) (linear_polynomial linear_snd))
     (polynomial_mapEnvironment diagonalWord_polynomial)
 
 
 theorem matrixDiagonal_polynomial : PolyBound matrixDiagonalRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) range_polynomial) (linear_polynomial linear_id))
   (polynomial_mapEnvironment (polynomial_comp (linear_polynomial approximationRowEnvironment_linear) diagonalRow_polynomial))

 theorem diagonalRow_correct {n : ℕ} (s : SignedWords) (hs : 0< value s.2.2) (i : Fin n) :
     RepresentsVector (diagonalRow (n,(i.val,s)))
       (rationalVector (fun j => if j=i then signedFractionValue s else 0)) := by
   refine ⟨fun j => if j=i then s else zeroSignedWord,?_,?_,?_⟩
   · simp only [diagonalRow]
     rw [map_range_ofFn]
     congr 1
     funext j
     simp only [diagonalWord,Fin.ext_iff]
   · intro j
     dsimp only
     by_cases h : j=i
     · simp only [if_pos h]; exact hs
     · simp only [if_neg h]; exact zeroSigned_den
   · intro j
     simp only [rationalVector,WithLp.ofLp_toLp]
     by_cases h : j=i
     · simp only [if_pos h]
     · simp only [if_neg h,zeroSigned_value,Rat.cast_zero]

 theorem matrixDiagonal_correct (n : ℕ) (s : SignedWords) (hs : 0< value s.2.2) :
     RepresentsMatrix (matrixDiagonal (n,s)) (signedFractionValue s • (1:Matrix (Fin n) (Fin n) ℚ)) := by
   refine ⟨fun i => diagonalRow (n,(i.val,s)),?_,?_⟩
   · simp only [matrixDiagonal]
     rw [map_range_ofFn]
   · intro i
     have hh := diagonalRow_correct s hs i
     have he : (fun j => if j=i then signedFractionValue s else 0)=
         (signedFractionValue s • (1:Matrix (Fin n) (Fin n) ℚ)) i := by
       funext j
       simp only [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
       by_cases h : j=i
       · subst j; simp
       · simp [h,Ne.symm h]
     rw [he] at hh
     exact hh

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

 
 
 
 theorem roundingDiagonal_polynomial : PolyBound roundingDiagonalRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_comp linear_fst linear_fst))
     (polynomial_comp (linear_polynomial linear_fst) roundingAllowance_polynomial)) matrixDiagonal_polynomial
 
 
 theorem roundedShapeWords_polynomial : PolyBound roundedShapeWordsRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial (linear_pair linear_snd (linear_comp linear_fst linear_snd))) floorMatrix_polynomial)
     roundingDiagonal_polynomial) matrixAdd_polynomial

 
 
 theorem shapeCutData_linear : Linear shapeCutDataRealizer :=
   linear_pair (linear_comp (linear_comp linear_fst linear_fst) linear_fst) linear_snd
 
 
 theorem shapeRoundData_polynomial : PolyBound shapeRoundDataRealizer := polynomial_pair
   (linear_polynomial (linear_comp linear_fst linear_fst)) (polynomial_comp (linear_polynomial shapeCutData_linear) cutShapeWords_polynomial)
 
 
 theorem roundedStepShapeWords_polynomial : PolyBound roundedStepShapeWordsRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp shapeRoundData_polynomial roundedShapeWords_polynomial)
     (polynomial_comp (linear_polynomial (linear_comp linear_fst linear_snd)) enlargementCoefficient_polynomial)) matrixScale_polynomial

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

 theorem roundedShapeWords_correct {n : ℕ} (bs : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ)
     (hA : RepresentsMatrix bs A) (p : ℕ) :
     RepresentsMatrix (roundedShapeWords ((n,p),bs)) (GLS.EllipsoidRounding.roundedShape A (2^p)) := by
   have hfloor := represents_floor_matrix bs A hA p
   have hdiag := matrixDiagonal_correct n (roundingAllowance (n,p)) (roundingAllowance_correct n p).1
   rw [(roundingAllowance_correct n p).2] at hdiag
   have hadd := represents_matrix_add (floorMatrix (bs,p)) (matrixDiagonal (n,roundingAllowance (n,p))) _ _ hfloor hdiag
   have he : GLS.EllipsoidRounding.roundedShape A (2^p)=
       (Matrix.of (fun i j => GLS.RationalRounding.roundDown (A i j) (2^p)))+((n:ℚ)/(2:ℚ)^p) • (1:Matrix (Fin n) (Fin n) ℚ) := by
     ext i j
     simp only [GLS.EllipsoidRounding.roundedShape,Matrix.add_apply,Matrix.of_apply,Matrix.smul_apply,Nat.cast_pow,Nat.cast_ofNat]
   rw [he]
   exact hadd
 theorem roundedStepShapeWords_correct {n : ℕ} (hn : 2≤ n) (bs : SignedMatrix)
     (A : Matrix (Fin n) (Fin n) ℚ) (hA : RepresentsMatrix bs A)
     (v : SignedVector) (a : Fin n → ℚ) (ha : RepresentsVector v (rationalVector a))
     (hq : a ⬝ᵥ (A *ᵥ a)≠0) (p h : ℕ) :
     RepresentsMatrix (roundedStepShapeWords (((n,p),h),(bs,v)))
       (GLS.EllipsoidCenter.roundedStepShape n A a (2^p) (1/(2:ℚ)^h)) := by
   have hcut := cutShapeWords_correct hn bs A hA v a ha hq
   have hround := roundedShapeWords_correct (cutShapeWords (n,(bs,v))) _ hcut p
   have hscale := represents_matrix_scale (roundedShapeWords ((n,p),cutShapeWords (n,(bs,v)))) _ hround
     (enlargementCoefficient h) (enlargementCoefficient_correct h).1
   rw [(enlargementCoefficient_correct h).2] at hscale
   simpa only [roundedStepShapeWords,shapeRoundData,GLS.EllipsoidCenter.roundedStepShape] using hscale

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SqrtUpperMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 theorem ceil_nat_fraction (a d : ℕ) (hd : 0< d) :
     Nat.ceil ((a:ℚ)/d)=a/d+(if a%d≠0 then 1 else 0) := by
   have h := floor_neg_nat_fraction a d hd
   rw [neg_div,Int.floor_neg] at h
   have hi := Int.neg_inj.mp h
   apply Int.natCast_inj.mp
   rw [Int.natCast_ceil_eq_ceil (by positivity)]
   exact hi

 theorem upperRootInput_denpos (s : FractionWords) (p : ℕ) (hd : 0< value s.2) :
     0< value (upperRootInput (s,p)).2.2 := hd
 theorem upperRootMagnitude_value (s : FractionWords) (p : ℕ) (hd : 0< value s.2) :
     value (upperRootMagnitude (s,p))=Nat.sqrt (Nat.ceil (fractionValue s*((2:ℚ)^p)^2))+1 := by
   simp only [upperRootMagnitude,upperRootSumInput,upperRootInteger,Function.comp_apply]
   rw [sumWords_value,integerRootWord_correct,value_natBits]
   rw [floorMagnitude_value _ (upperRootInput_denpos s p hd)]
   simp only [upperRootInput,zeroPrefix_value,true_and]
   have hc := ceil_nat_fraction (2^(p+p)*value s.1) (value s.2) hd
   have he : fractionValue s*((2:ℚ)^p)^2=((2^(p+p)*value s.1:ℕ):ℚ)/value s.2 := by
     simp only [fractionValue,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add,pow_two]
     ring
   rw [he,hc]
   have hone : value [true]=1 := by decide
   rw [hone]

 theorem sqrtUpperWords_correct (s : FractionWords) (p : ℕ) (hd : 0< value s.2) :
     0< value (sqrtUpperWords (s,p)).2.2 ∧
       signedFractionValue (sqrtUpperWords (s,p))=
         GLS.RationalRounding.sqrtUpper (fractionValue s) (2^p) := by
   constructor
   · change 0< value (powerTwoWord p)
     rw [powerTwoWord_value]
     positivity
   · simp only [signedFractionValue,sqrtUpperWords,signedValue,Bool.false_eq_true,if_false,
       Int.cast_natCast,upperRootMagnitude_value s p hd,powerTwoWord_value,GLS.RationalRounding.sqrtUpper,
       Nat.cast_pow,Nat.cast_ofNat]

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

 theorem fractionValue_abs (s : SignedWords) : fractionValue s.2=|signedFractionValue s| := by
   rcases s with ⟨b,N,D⟩
   cases b <;> simp [fractionValue,signedFractionValue,signedValue,abs_div,
     abs_of_nonneg (Nat.cast_nonneg (value N): (0:ℚ)≤ value N),
     abs_of_nonneg (Nat.cast_nonneg (value D): (0:ℚ)≤ value D)]
 
 
 theorem signedSqrtUpper_polynomial : PolyBound signedSqrtUpperRealizer := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp linear_fst linear_snd) linear_snd)) sqrtUpperWords_polynomial
 theorem signedSqrtUpper_correct (s : SignedWords) (p : ℕ) (hd : 0< value s.2.2)
     (hq : 0≤ signedFractionValue s) :
     0< value (signedSqrtUpper (s,p)).2.2 ∧
       signedFractionValue (signedSqrtUpper (s,p))=GLS.RationalRounding.sqrtUpper (signedFractionValue s) (2^p) := by
   have hh := sqrtUpperWords_correct s.2 p hd
   rw [fractionValue_abs,abs_of_nonneg hq] at hh
   exact hh
 theorem sqrtUpperWords_positive (s : FractionWords) (p : ℕ) : 0< signedFractionValue (sqrtUpperWords (s,p)) := by
   have hnum : 0< value (upperRootMagnitude (s,p)) := by
     simp only [upperRootMagnitude,Function.comp_apply,upperRootSumInput,sumWords_value]
     have h1 : value [true]=1 := by decide
     rw [h1]
     omega
   simp only [sqrtUpperWords,signedFractionValue,signedValue,Bool.false_eq_true,if_false,Int.cast_natCast,powerTwoWord_value]
   positivity
 theorem signedSqrtUpper_positive (s : SignedWords) (p : ℕ) : 0< signedFractionValue (signedSqrtUpper (s,p)) :=
   sqrtUpperWords_positive s.2 p

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

 
 
 
 theorem centerShapeData_linear : Linear centerShapeDataRealizer :=
   linear_pair (linear_comp linear_fst linear_fst)
     (linear_pair (linear_comp linear_snd linear_fst) (linear_comp (linear_comp linear_snd linear_snd) linear_fst))
 
 
 theorem centerRootData_polynomial : PolyBound centerRootDataRealizer := polynomial_pair
   (polynomial_comp (linear_polynomial centerShapeData_linear) cutQuadratic_polynomial) (linear_polynomial (linear_comp linear_fst linear_snd))
 
 
 theorem centerRoot_polynomial : PolyBound centerRootRealizer := polynomial_comp centerRootData_polynomial signedSqrtUpper_polynomial
 
 
 theorem centerScalar_polynomial : PolyBound centerScalarRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_comp linear_fst linear_fst)) centerRoot_polynomial) centerCutCoefficient_polynomial
 
 
 theorem centerDisplacement_polynomial : PolyBound centerDisplacementRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial centerShapeData_linear) cutDirection_polynomial) centerScalar_polynomial) vectorScale_polynomial
 
 
 theorem approximateCenterWords_polynomial : PolyBound approximateCenterWordsRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_comp (linear_comp linear_snd linear_snd) linear_snd)) centerDisplacement_polynomial) vectorSub_polynomial
 
 
 theorem roundedCenterWords_polynomial : PolyBound roundedCenterWordsRealizer := polynomial_comp
   (polynomial_pair approximateCenterWords_polynomial (linear_polynomial (linear_comp linear_fst linear_snd))) floorVector_polynomial

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

 theorem centerRoot_correct {n : ℕ} (bs : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ)
     (hA : RepresentsMatrix bs A) (v c : SignedVector) (a : Fin n → ℚ)
     (ha : RepresentsVector v (rationalVector a)) (hq : 0≤ a ⬝ᵥ (A *ᵥ a)) (p : ℕ) :
     0< value (centerRoot ((n,p),(bs,(v,c)))).2.2 ∧
       signedFractionValue (centerRoot ((n,p),(bs,(v,c))))=
         GLS.RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) (2^p) := by
   have hquad := cutQuadratic_correct bs A hA v a ha
   have hh := signedSqrtUpper_correct (cutQuadratic (n,(bs,v))) p hquad.1 (by rw [hquad.2]; exact hq)
   rw [hquad.2] at hh
   exact hh
 theorem approximateCenterWords_correct {n : ℕ} (bs : SignedMatrix)
     (A : Matrix (Fin n) (Fin n) ℚ) (hA : RepresentsMatrix bs A)
     (v cs : SignedVector) (a c : Fin n → ℚ) (ha : RepresentsVector v (rationalVector a))
     (hc : RepresentsVector cs (rationalVector c)) (hq : 0≤ a ⬝ᵥ (A *ᵥ a)) (p : ℕ) :
     RepresentsVector (approximateCenterWords ((n,p),(bs,(v,cs))))
       (rationalVector (GLS.EllipsoidCenter.approximateCenter n A a c (2^p))) := by
   let s := ((n,p),(bs,(v,cs)))
   have hd := cutDirection_correct bs A hA v a ha
   have hroot := centerRoot_correct bs A hA v cs a ha hq p
   have hpos : 0< signedFractionValue (centerRoot s) := signedSqrtUpper_positive _ _
   have hcoef := centerCutCoefficient_correct n (centerRoot s) hroot.1 (ne_of_gt hpos)
   have hscale := represents_rational_scale (cutDirection (centerShapeData s)) (A *ᵥ a) hd (centerScalar s) hcoef.1
   have hsub := represents_rational_sub cs (centerDisplacement s) c _ hc hscale
   have he : signedFractionValue (centerScalar s)=1/(((n:ℚ)+1)*GLS.RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) (2^p)) := by
     simpa only [centerScalar,s,hroot.2] using hcoef.2
   rw [he] at hsub
   have hcast : (((2:ℕ)^p:ℕ):ℚ)=(2:ℚ)^p := by norm_cast
   simpa only [approximateCenterWords,centerDisplacement,GLS.EllipsoidCenter.approximateCenter,hcast] using hsub
 theorem roundedCenterWords_correct {n : ℕ} (bs : SignedMatrix)
     (A : Matrix (Fin n) (Fin n) ℚ) (hA : RepresentsMatrix bs A)
     (v cs : SignedVector) (a c : Fin n → ℚ) (ha : RepresentsVector v (rationalVector a))
     (hc : RepresentsVector cs (rationalVector c)) (hq : 0≤ a ⬝ᵥ (A *ᵥ a)) (p : ℕ) :
     RepresentsVector (roundedCenterWords ((n,p),(bs,(v,cs))))
       (rationalVector (GLS.EllipsoidCenter.roundedCenter n A a c (2^p))) := by
   have hh := approximateCenterWords_correct bs A hA v cs a c ha hc hq p
   have hf := represents_floor_vector (approximateCenterWords ((n,p),(bs,(v,cs)))) _ hh p
   exact hf

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

 
 
 theorem accuracyExponent_polynomial : PolyBound accuracyExponentRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial (linear_pair (linear_constant (2:ℕ)) linear_id)) naturalProduct_polynomial)
     (linear_polynomial (linear_constant (4:ℕ)))) BinaryGcd.nat_add_polynomial
 
 
 
 theorem gridDouble_polynomial : PolyBound gridDouble := polynomial_comp (linear_polynomial (linear_pair (linear_constant (2:ℕ)) linear_snd)) naturalProduct_polynomial
 theorem gridTriple_polynomial : PolyBound gridTriple := polynomial_comp (linear_polynomial (linear_pair (linear_constant (3:ℕ)) linear_fst)) naturalProduct_polynomial
 
 theorem gridExponent_polynomial : PolyBound gridExponentRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (polynomial_pair gridDouble_polynomial gridTriple_polynomial) BinaryGcd.nat_add_polynomial)
     (linear_polynomial (linear_constant (9:ℕ)))) BinaryGcd.nat_add_polynomial

 
 
 
 theorem ellipsoidShapeData_polynomial : PolyBound ellipsoidShapeDataRealizer := polynomial_pair
   (polynomial_pair (polynomial_pair (linear_polynomial (linear_comp linear_fst linear_fst))
     (polynomial_comp (linear_polynomial linear_fst) gridExponent_polynomial))
     (polynomial_comp (linear_polynomial (linear_comp linear_fst linear_fst)) accuracyExponent_polynomial))
   (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) (linear_comp (linear_comp linear_snd linear_snd) linear_fst)))
 
 
 theorem ellipsoidCenterData_polynomial : PolyBound ellipsoidCenterDataRealizer := polynomial_pair
   (polynomial_pair (linear_polynomial (linear_comp linear_fst linear_fst)) (polynomial_comp (linear_polynomial linear_fst) gridExponent_polynomial))
   (linear_polynomial linear_snd)
 
 
 theorem ellipsoidUpdate_polynomial : PolyBound ellipsoidUpdateRealizer := polynomial_pair
   (polynomial_comp ellipsoidShapeData_polynomial roundedStepShapeWords_polynomial)
   (polynomial_comp ellipsoidCenterData_polynomial roundedCenterWords_polynomial)

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

 theorem ellipsoid_grid_exponent (n k : ℕ) :
     2^(gridExponent (n,k))=GLS.EllipsoidPrecision.gridDenominator (2*k+2) (2*n+4) n := by
   unfold gridExponent GLS.EllipsoidPrecision.gridDenominator
   congr 1
   omega
 theorem ellipsoidUpdate_correct {n : ℕ} (hn : 2≤ n) (k : ℕ)
     (bs : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ) (hA : RepresentsMatrix bs A)
     (vs cs : SignedVector) (a c : Fin n → ℚ) (ha : RepresentsVector vs (rationalVector a))
     (hc : RepresentsVector cs (rationalVector c)) (hq : 0< a ⬝ᵥ (A *ᵥ a)) :
     RepresentsMatrix (ellipsoidUpdate ((n,k),(bs,(vs,cs)))).1
       (GLS.EllipsoidCenter.roundedStepShape n A a
         (GLS.EllipsoidPrecision.gridDenominator (2*k+2) (2*n+4) n) (GLS.EllipsoidIteration.stepAccuracy n)) ∧
       RepresentsVector (ellipsoidUpdate ((n,k),(bs,(vs,cs)))).2
         (rationalVector (GLS.EllipsoidCenter.roundedCenter n A a c
           (GLS.EllipsoidPrecision.gridDenominator (2*k+2) (2*n+4) n))) := by
   have hshape := roundedStepShapeWords_correct hn bs A hA vs a ha (ne_of_gt hq) (gridExponent (n,k)) (accuracyExponent n)
   have hcenter := roundedCenterWords_correct bs A hA vs cs a c ha hc (le_of_lt hq) (gridExponent (n,k))
   rw [ellipsoid_grid_exponent] at hshape hcenter
   refine ⟨?_,hcenter⟩
   simpa only [ellipsoidUpdate,ellipsoidShapeData,GLS.EllipsoidIteration.stepAccuracy,accuracyExponent] using hshape

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

 
 
 theorem normalizeEllipsoidState_polynomial : PolyBound normalizeEllipsoidStateRealizer := polynomial_pair
   (polynomial_comp (linear_polynomial linear_fst) normalizeMatrix_polynomial)
   (polynomial_comp (linear_polynomial linear_snd) normalizeVector_polynomial)
 
 
 theorem canonicalEllipsoidUpdate_polynomial : PolyBound canonicalEllipsoidUpdateRealizer :=
   polynomial_comp ellipsoidUpdate_polynomial normalizeEllipsoidState_polynomial
 theorem canonicalEllipsoidUpdate_correct {n : ℕ} (hn : 2≤ n) (k : ℕ)
     (bs : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ) (hA : RepresentsMatrix bs A)
     (vs cs : SignedVector) (a c : Fin n → ℚ) (ha : RepresentsVector vs (rationalVector a))
     (hc : RepresentsVector cs (rationalVector c)) (hq : 0< a ⬝ᵥ (A *ᵥ a)) :
     RepresentsMatrix (canonicalEllipsoidUpdate ((n,k),(bs,(vs,cs)))).1
       (GLS.EllipsoidCenter.roundedStepShape n A a
         (GLS.EllipsoidPrecision.gridDenominator (2*k+2) (2*n+4) n) (GLS.EllipsoidIteration.stepAccuracy n)) ∧
       RepresentsVector (canonicalEllipsoidUpdate ((n,k),(bs,(vs,cs)))).2
         (rationalVector (GLS.EllipsoidCenter.roundedCenter n A a c
           (GLS.EllipsoidPrecision.gridDenominator (2*k+2) (2*n+4) n))) ∧
       (∀ row∈(canonicalEllipsoidUpdate ((n,k),(bs,(vs,cs)))).1,VectorCanonical row) ∧
       VectorCanonical (canonicalEllipsoidUpdate ((n,k),(bs,(vs,cs)))).2 := by
   have hh := ellipsoidUpdate_correct hn k bs A hA vs cs a c ha hc hq
   have hmatrix := normalizeMatrix_rep hh.1
   have hvector := normalizeVector_rep hh.2
   exact ⟨hmatrix.1,hvector.1,hmatrix.2,hvector.2⟩

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

 
 
 
 
 theorem phaseStepData_polynomial : PolyBound phaseStepDataRealizer := linear_polynomial
   (linear_pair (linear_comp linear_snd linear_fst)
     (linear_pair (linear_comp (linear_comp linear_snd linear_snd) linear_fst)
       (linear_pair linear_fst (linear_comp (linear_comp linear_snd linear_snd) linear_snd))))
 
 
 theorem phaseStepCounter_polynomial : PolyBound phaseStepCounterRealizer := linear_polynomial
   (linear_pair (linear_comp (linear_comp linear_snd linear_fst) linear_fst)
     (linear_comp (linear_comp (linear_comp linear_snd linear_fst) linear_snd) natSucc_linear))
 
 
 theorem ellipsoidPhaseStep_polynomial : PolyBound ellipsoidPhaseStepRealizer := polynomial_pair
   phaseStepCounter_polynomial (polynomial_comp phaseStepData_polynomial canonicalEllipsoidUpdate_polynomial)
 
 
 theorem phaseInitialRaw_polynomial : PolyBound phaseInitialRawRealizer := polynomial_pair
   (polynomial_comp (linear_polynomial (linear_pair linear_id (linear_constant scalarOne))) matrixDiagonal_polynomial)
   (polynomial_comp (linear_polynomial (linear_pair linear_id (linear_constant signedZero))) replicateList_polynomial)
 
 
 theorem phaseInitial_polynomial : PolyBound phaseInitialRealizer := polynomial_pair
   (linear_polynomial (linear_pair linear_id (linear_constant (0:ℕ))))
   (polynomial_comp phaseInitialRaw_polynomial normalizeEllipsoidState_polynomial)
 
 
 
 
 

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

 
 theorem thinExponent_polynomial : PolyBound thinExponentRealizer := by
   unfold thinExponentRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (linear_polynomial (linear_constant (10:ℕ)))
     (polynomial_comp (linear_polynomial (linear_comp natSucc_linear natSucc_linear)) naturalSquare_polynomial)) naturalProduct_polynomial
 
 
 theorem phaseThresholdExponent_polynomial : PolyBound phaseThresholdExponentRealizer := polynomial_comp
   (polynomial_comp (polynomial_pair thinExponent_polynomial (linear_polynomial linear_id)) BinaryGcd.nat_add_polynomial) (linear_polynomial natSucc_linear)
 
 
 
 theorem phaseBudgetInner_polynomial : PolyBound phaseBudgetInnerRealizer := polynomial_comp
   (polynomial_comp (polynomial_pair phaseThresholdExponent_polynomial (linear_polynomial linear_id)) naturalProduct_polynomial) (linear_polynomial natSucc_linear)
 
 theorem phaseBudgetFactor_polynomial : PolyBound phaseBudgetFactorRealizer := polynomial_comp
   (linear_polynomial (linear_pair (linear_constant (4:ℕ)) natSucc_linear)) naturalProduct_polynomial
 
 theorem phaseBudget_polynomial : PolyBound phaseBudgetRealizer := polynomial_comp
   (polynomial_pair phaseBudgetFactor_polynomial phaseBudgetInner_polynomial) naturalProduct_polynomial
 theorem phaseBudget_pos (n : ℕ) : 0 < phaseBudget n := by dsimp [phaseBudget,thresholdSteps]; positivity
 theorem phaseBudget_mono {m n : ℕ} (hmn : m ≤ n) : phaseBudget m ≤ phaseBudget n := by
   dsimp [phaseBudget,thresholdSteps,phaseThresholdExponent,thinExponent]
   gcongr

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

 
 
 theorem wordNonzero_polynomial : PolyBound wordNonzeroRealizer := polynomial_comp
   (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_fst)) trim_polynomial) (linear_polynomial nonempty_linear)
 theorem wordNonzero_correct (s : SignedWords) (hd : 0 < value s.2.2) :
     wordNonzero s=true ↔ signedFractionValue s≠0 := by
   have hdQ : (value s.2.2:ℚ)≠0 := by exact_mod_cast (ne_of_gt hd)
   have hn : signedFractionValue s=0 ↔ value s.2.1=0 := by
     rcases s with ⟨b,N,D⟩
     cases b <;> simp [signedFractionValue,signedValue,div_eq_zero_iff,hdQ]
   have hz := zeroWord_iff s.2.1
   cases hb : (trim s.2.1).isEmpty <;> simp_all [wordNonzero]
 
 
 theorem nonzeroCoordinate_polynomial : PolyBound nonzeroCoordinateRealizer := polynomial_comp
   (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) (lookupList_polynomial signedZero)) wordNonzero_polynomial
 
 
 theorem nonzeroIndices_polynomial : PolyBound nonzeroIndicesRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp listLength_polynomial range_polynomial) (linear_polynomial linear_id))
   (filterEnvironment_polynomial nonzeroCoordinate_polynomial)
 
 
 theorem findNonzero_polynomial : PolyBound findNonzeroRealizer := polynomial_comp
   nonzeroIndices_polynomial (linear_polynomial (linear_pair nonemptyNatList_linear headNat_linear))
 theorem nonzeroIndices_mem {n : ℕ} (ps : SignedVector) (p : Fin n → ℚ)
     (hps : RepresentsVector ps (rationalVector p)) (i : ℕ) :
     i∈nonzeroIndices ps ↔ ∃ j : Fin n,i=j.val ∧ p j≠0 := by
   have hn : ps.length=n := by obtain ⟨words,rfl,hD,hv⟩ := hps; simp
   simp only [nonzeroIndices,List.mem_filter,List.mem_range,hn]
   constructor
   · rintro ⟨hi,h⟩
     have hh := represents_lookup ps (rationalVector p) hps ⟨i,hi⟩ signedZero
     have hv : signedFractionValue ((ps.drop i).headD signedZero)=p ⟨i,hi⟩ := Rat.cast_injective (α:=ℝ) hh.2
     exact ⟨⟨i,hi⟩,rfl,by rw [←hv]; exact (wordNonzero_correct _ hh.1).mp h⟩
   · rintro ⟨j,rfl,hj⟩
     have hh := represents_lookup ps (rationalVector p) hps j signedZero
     have hv : signedFractionValue ((ps.drop j.val).headD signedZero)=p j := Rat.cast_injective (α:=ℝ) hh.2
     exact ⟨j.isLt,(wordNonzero_correct _ hh.1).mpr (by rwa [hv])⟩
 theorem findNonzero_correct {n : ℕ} (ps : SignedVector) (p : Fin n → ℚ)
     (hps : RepresentsVector ps (rationalVector p)) (hp : p≠0) :
     (findNonzero ps).1=true ∧ ∃ j : Fin n,(findNonzero ps).2=j.val ∧ p j≠0 := by
   have hne : nonzeroIndices ps≠[] := by
     intro he
     apply hp
     funext j
     by_contra hj
     have hm := (nonzeroIndices_mem ps p hps j.val).mpr ⟨j,rfl,hj⟩
     rw [he] at hm; cases hm
   have hm : (nonzeroIndices ps).headD 0∈nonzeroIndices ps := by
     cases he : nonzeroIndices ps with
     | nil => exact (hne he).elim
     | cons a xs => simp
   refine ⟨?_,(nonzeroIndices_mem ps p hps _).mp hm⟩
   cases he : nonzeroIndices ps with
   | nil => exact (hne he).elim
   | cons a xs => simp [findNonzero,he]

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

 
 
 theorem eraseIndex_polynomial : PolyBound (eraseIndexRealizer (α:=α)) := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) takeList_polynomial)
     (polynomial_comp (linear_polynomial (linear_pair linear_fst (linear_comp linear_snd RawStack.natSucc_linear))) dropList_polynomial)) appendList_polynomial
 
 

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

 
 
 
 
 theorem eliminationRowPivot_polynomial : PolyBound eliminationRowPivotRealizer := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp linear_fst linear_fst) (linear_comp linear_snd linear_fst))) (lookupList_polynomial signedZero)
 
 
 theorem eliminationNormalPivot_polynomial : PolyBound eliminationNormalPivotRealizer := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp (linear_comp linear_snd linear_snd) linear_fst) (linear_comp linear_snd linear_fst))) (lookupList_polynomial signedZero)
 
 
 theorem eliminationRatio_polynomial : PolyBound eliminationRatioRealizer := polynomial_comp
   (polynomial_pair eliminationRowPivot_polynomial eliminationNormalPivot_polynomial) canonicalDiv_polynomial
 
 
 theorem eliminationRowRest_polynomial : PolyBound eliminationRowRestRealizer := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp linear_fst linear_fst) (linear_comp linear_snd linear_fst))) eraseIndex_polynomial
 
 
 theorem eliminationNormalRest_polynomial : PolyBound eliminationNormalRestRealizer := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp (linear_comp linear_snd linear_snd) linear_fst) (linear_comp linear_snd linear_fst))) eraseIndex_polynomial
 
 
 theorem eliminationRowCoefficients_polynomial : PolyBound eliminationRowCoefficientsRealizer := polynomial_comp
   (polynomial_pair eliminationRowRest_polynomial (polynomial_comp
     (polynomial_pair eliminationNormalRest_polynomial eliminationRatio_polynomial) vectorScale_polynomial)) vectorSub_polynomial
 
 
 theorem eliminationRowOffset_polynomial : PolyBound eliminationRowOffsetRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_comp linear_fst linear_snd))
     (polynomial_comp (polynomial_pair eliminationRatio_polynomial
       (linear_polynomial (linear_comp (linear_comp linear_snd linear_snd) linear_snd))) canonicalMul_polynomial)) canonicalAdd_polynomial
 
 
 theorem eliminationRow_polynomial : PolyBound eliminationRowRealizer := polynomial_pair eliminationRowCoefficients_polynomial eliminationRowOffset_polynomial
 
 
 
 theorem eliminationRows_polynomial : PolyBound eliminationRowsRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) (arrayPairs_polynomial ([]:SignedVector) signedZero))
     (linear_polynomial linear_snd)) (polynomial_mapEnvironment eliminationRow_polynomial)
 
 
 theorem affineEliminate_polynomial : PolyBound affineEliminateRealizer := polynomial_comp eliminationRows_polynomial
   (polynomial_pair (polynomial_mapList (linear_polynomial linear_fst)) (polynomial_mapList (linear_polynomial linear_snd)))

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

 
 theorem represents_rect_matrix_vector {m n : ℕ} (bs : SignedMatrix) (A : Matrix (Fin m) (Fin n) ℚ)
     (hA : RepresentsRectMatrix bs A) (v : SignedVector) (x : Fin n → ℚ)
     (hv : RepresentsVector v (rationalVector x)) :
     RepresentsVector (matrixVector (bs,v)) (rationalVector (A *ᵥ x)) := by
   obtain ⟨rows,rfl,hrows⟩ := hA
   refine ⟨fun i => signedDot (rows i,v),?_,?_,?_⟩
   · simp only [matrixVector,List.map_ofFn]; rfl
   · intro i; exact (represents_rational_dot (rows i) v (A i) x (hrows i) hv).1
   · intro i
     rw [(represents_rational_dot (rows i) v (A i) x (hrows i) hv).2]
     rfl
 

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

 
 theorem rational_rect_matrix_word_volume {m n H : ℕ} (bs : SignedMatrix) (A : Matrix (Fin m) (Fin n) ℚ)
     (hA : RepresentsRectMatrix bs A) (hcan : ∀ row∈bs,VectorCanonical row)
     (hsize : ∀ i j,(A i j).num.natAbs ≤ 2^H ∧ (A i j).den ≤ 2^H) :
     volume bs ≤ m*(n*(14*(H+2)+1)+2)+1 := by
   obtain ⟨rows,rfl,hrows⟩ := hA
   have hrow (i : Fin m) := rational_vector_word_volume (rows i) (A i) (hrows i)
     (hcan _ (List.mem_ofFn.mpr ⟨i,rfl⟩)) (hsize i)
   have hh := volume_list_le (List.ofFn rows) (n*(14*(H+2)+1)+1) (by
     intro row hr; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr; exact hrow i)
   simpa only [List.length_ofFn] using hh
 
 
 theorem canonicalAffineEliminate_polynomial : PolyBound canonicalAffineEliminateRealizer := polynomial_comp
   affineEliminate_polynomial normalizeEllipsoidState_polynomial
 

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

 
 
 theorem phaseRecoveryInput_polynomial : PolyBound phaseRecoveryInputRealizer := linear_polynomial (linear_pair (linear_comp linear_fst linear_fst) linear_snd)
 
 
 
 
 theorem phaseSplitCoefficients_polynomial : PolyBound phaseSplitCoefficientsRealizer := polynomial_pair takeList_polynomial
   (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) (lookupList_polynomial signedZero))
 
 
 
 
 theorem eliminationParameters_polynomial : PolyBound eliminationParametersRealizer := polynomial_pair
   (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) findNonzero_polynomial) (linear_polynomial linear_snd))
   (linear_polynomial linear_id)
 
 
 
 
 

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

 
 
 
 theorem affineEvaluation_polynomial : PolyBound affineEvaluationRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst linear_fst) linear_snd)) matrixVector_polynomial)
     (linear_polynomial (linear_comp linear_fst linear_snd))) vectorAdd_polynomial
 theorem affineEvaluation_correct {m n : ℕ} (rows : SignedMatrix) (offs xs : SignedVector)
     (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (x : Fin n → ℚ)
     (hA : RepresentsRectMatrix rows A) (hb : RepresentsVector offs (rationalVector b))
     (hx : RepresentsVector xs (rationalVector x)) :
     RepresentsVector (affineEvaluation ((rows,offs),xs)) (rationalVector (A *ᵥ x+b)) := by
   exact represents_rational_add _ _ _ _ (represents_rect_matrix_vector rows A hA xs x hx) hb

 
 
 
 theorem affinePullbackCoordinate_polynomial : PolyBound affinePullbackCoordinateRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_fst))
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd linear_snd) linear_fst)) matrixColumn_polynomial)) signedDot_polynomial
 
 
 theorem affinePullback_polynomial : PolyBound affinePullbackRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) range_polynomial) (linear_polynomial linear_snd))
   (polynomial_mapEnvironment affinePullbackCoordinate_polynomial)

 theorem rect_matrixColumn_correct {m n : ℕ} (rows : SignedMatrix) (A : Matrix (Fin m) (Fin n) ℚ)
     (hA : RepresentsRectMatrix rows A) (j : Fin n) :
     RepresentsVector (matrixColumn (rows,j.val)) (rationalVector (fun i => A i j)) := by
   obtain ⟨rs,rfl,hrs⟩ := hA
   refine ⟨fun i => ((rs i).drop j.val).headD signedZero,?_,?_,?_⟩
   · simp only [matrixColumn,List.map_ofFn]; rfl
   · intro i; exact (represents_lookup _ _ (hrs i) j signedZero).1
   · intro i; exact (represents_lookup _ _ (hrs i) j signedZero).2
 theorem affinePullback_correct {m n : ℕ} (rows : SignedMatrix) (as : SignedVector)
     (A : Matrix (Fin m) (Fin n) ℚ) (a : Fin m → ℚ)
     (hA : RepresentsRectMatrix rows A) (ha : RepresentsVector as (rationalVector a)) :
     RepresentsVector (affinePullback (n,(as,rows))) (rationalVector (A.vecMul a)) := by
   have hcol (j : Fin n) := represents_rational_dot as (matrixColumn (rows,j.val)) a (fun i => A i j) ha (rect_matrixColumn_correct rows A hA j)
   refine ⟨fun i => affinePullbackCoordinate (i.val,(as,rows)),?_,fun i => (hcol i).1,?_⟩
   · simp only [affinePullback,map_range_ofFn]
   · intro i
     change (signedFractionValue (signedDot (as,matrixColumn (rows,i.val))):ℝ)=_
     rw [(hcol i).2]; rfl

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

 
 
 theorem clearingModulus_polynomial : PolyBound clearingModulusRealizer := polynomial_comp
   (polynomial_comp (linear_polynomial (linear_pair (linear_constant (0:ℕ)) linear_id)) approximationModuli_polynomial)
   (linear_polynomial linear_fst)
 
 
 theorem clearCanonicalVector_polynomial : PolyBound clearCanonicalVectorRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial linear_id) (polynomial_comp clearingModulus_polynomial (linear_polynomial unsignedInteger_linear))) vectorScale_polynomial
 
 
 theorem clearRationalVector_polynomial : PolyBound clearRationalVectorRealizer := polynomial_comp normalizeVector_polynomial clearCanonicalVector_polynomial

 theorem clearRationalVector_correct {n : ℕ} (xs : SignedVector) (a : Fin n → ℚ)
     (ha : RepresentsVector xs (rationalVector a)) :
     ∃ (p : Fin n → ℤ) (T : ℝ),0 < T ∧
       RepresentsVector (clearRationalVector xs) (WithLp.toLp 2 (fun i => (p i:ℝ))) ∧
       ∀ i,(p i:ℝ)=T*(a i:ℝ) := by
   let α : Fin n → RationalCode := fun i => rationalCode (a i)
   let as : SignedVector := List.ofFn (fun i => codeWords (α i))
   let t := (approximationModuli (0,as)).1
   let p := approximationNumerator α 0
   have hnorm : normalizeVector xs=as := normalizeVector_codes xs a ha
   have hmods := approximationModuli_codes α 0
   have ht : 0 < value t := by
     dsimp only [t,as]
     rw [hmods.1]
     exact Nat.mul_pos (denominatorProduct_pos α) (by positivity)
   have hu : RepresentsVector as (rationalVector a) := by
     rw [←hnorm]
     exact (normalizeVector_rep ha).1
   have hv := represents_rational_scale as a hu (unsignedIntegerWord t) (unsignedInteger_den t)
   have hvalue : ∀ i,(p i:ℝ)=(value t:ℝ)*(a i:ℝ) := by
     intro i
     have hh := approximationNumerator_correct α 0 i
     have he : (value t:ℝ)=(denominatorProduct α*2^((n+1)*(0+n+2)):ℕ) := by
       dsimp [t,as]; rw [hmods.1]
     rw [he]
     dsimp only [p,α] at hh
     rw [rationalCode_value] at hh
     simpa only [mul_comm] using hh.symm
   have he : rationalVector (signedFractionValue (unsignedIntegerWord t) • a)=WithLp.toLp 2 (fun i => (p i:ℝ)) := by
     ext i
     simp only [rationalVector,WithLp.ofLp_toLp,Pi.smul_apply,smul_eq_mul,unsignedInteger_value,Rat.cast_mul,Rat.cast_natCast]
     exact (hvalue i).symm
   rw [he] at hv
   refine ⟨p,(value t:ℝ),by exact_mod_cast ht,?_,hvalue⟩
   simpa only [clearRationalVector,Function.comp_apply,hnorm,clearCanonicalVector,clearingModulus,t] using hv

 theorem integer_vector_norm_lower {n : ℕ} (p : Fin n → ℤ) (hp : p≠0) :
     1 ≤ GLS.Cast.realVector (fun i => (p i:ℚ)) ⬝ᵥ GLS.Cast.realVector (fun i => (p i:ℚ)) := by
   obtain ⟨j,hj⟩ : ∃ j,p j≠0 := by contrapose! hp; ext i; exact hp i
   have hInt : 1 ≤ (p j)^2 := by
     have hh : p j ≤ -1 ∨ 1 ≤ p j := by omega
     rcases hh with hh | hh <;> nlinarith [sq_nonneg (p j)]
   have hReal : (1:ℝ) ≤ (p j:ℝ)^2 := by exact_mod_cast hInt
   have hs : (p j:ℝ)^2 ≤ ∑ i : Fin n,(p i:ℝ)^2 := Finset.single_le_sum (f:=fun i : Fin n => (p i:ℝ)^2) (fun i hi => sq_nonneg _) (Finset.mem_univ j)
   simpa only [GLS.Cast.realVector,_root_.dotProduct,Rat.cast_intCast,pow_two] using hReal.trans hs

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
 
 theorem time_selectiveChoose {f g : α → β} (R : Realizer f) (S : Realizer g) (x : Bool×α) :
     (R.selectiveChoose S).time x=(if x.1 then (snd.comp R).time x else (snd.comp S).time x)+
       30*(volume x+volume (if x.1 then f x.2 else g x.2)+1) := by
   rcases x with ⟨b,x⟩
   cases b <;> change _=_ <;>
     simp only [selectiveChoose,time,Routine.selectiveChoose,enc_pair,enc_false,enc_true,
       Data.head,Data.nonempty,Bool.false_eq_true,ite_false,ite_true]
   · have hh : (snd.comp S).transform (Data.pair Data.nil (enc x))=enc (g x) := (snd.comp S).correct (Bool.false,x)
     rw [hh]; rfl
   · have hh : (snd.comp R).transform (Data.pair (Data.pair Data.nil Data.nil) (enc x))=enc (f x) := (snd.comp R).correct (Bool.true,x)
     rw [hh]; rfl
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

 
 
 
 
 
 theorem oracleQueryScale_polynomial : PolyBound oracleQueryScaleRealizer := polynomial_comp
   (linear_polynomial (linear_comp (linear_comp (linear_comp linear_snd linear_fst) linear_fst) natSucc_linear)) naturalSignedWord_polynomial
 
 theorem oracleCoreQuery_polynomial : PolyBound oracleCoreQueryRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial linear_fst) (polynomial_comp
     (polynomial_pair (linear_polynomial (linear_comp (linear_comp linear_snd linear_snd) linear_snd)) oracleQueryScale_polynomial) vectorScale_polynomial)) affineEvaluation_polynomial
 
 
 theorem oracleInitial_polynomial : PolyBound oracleInitialRealizer := polynomial_pair
   (linear_polynomial (linear_constant Bool.false))
   (polynomial_pair (polynomial_comp phaseInitial_polynomial (linear_polynomial linear_snd)) phaseInitial_polynomial)
 
 
 theorem oracleAtBoundary_polynomial : PolyBound oracleAtBoundaryRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (linear_polynomial (linear_comp (linear_comp linear_snd linear_fst) linear_fst)) phaseBudget_polynomial)
     (linear_polynomial (linear_comp (linear_comp linear_snd linear_fst) linear_snd))) nat_le_polynomial
 
 
 
 
 theorem oraclePhaseAdvance_polynomial : PolyBound oraclePhaseAdvanceRealizer := polynomial_pair
   (linear_polynomial (linear_comp linear_snd linear_fst))
   (polynomial_comp (linear_polynomial (linear_pair linear_fst (linear_comp linear_snd linear_snd))) ellipsoidPhaseStep_polynomial)
 
 
 
 
 
 theorem oracleSmallDimension_linear : Linear oracleSmallDimension := linear_comp (linear_comp (linear_comp linear_snd linear_snd) linear_fst) linear_fst
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 theorem oraclePullbackData_polynomial : PolyBound oraclePullbackDataRealizer := linear_polynomial (linear_pair oracleSmallDimension_linear
   (linear_pair linear_fst (linear_comp (linear_comp linear_snd linear_fst) linear_fst)))
 
 
 theorem oraclePrepareCut_polynomial : PolyBound oraclePrepareCutRealizer := polynomial_pair
   (polynomial_comp (polynomial_comp oraclePullbackData_polynomial affinePullback_polynomial) clearRationalVector_polynomial)
   (linear_polynomial linear_snd)
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RectangularRowsParser
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 theorem readRectangularRows_polynomial : PolyBound readRectangularRowsRealizer := polynomial_comp
   (polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst linear_snd)
     (linear_pair (linear_comp linear_fst linear_fst) (linear_pair linear_snd (linear_constant ([]:SignedMatrix)))))) readMatrix_iterate_polynomial)
   (polynomial_pair (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_snd)) reverse_polynomial_generic)
     (linear_polynomial (linear_comp linear_snd linear_fst)))
 theorem readRectangularRows_codes (n : ℕ) (rows : List (List RationalCode))
     (hlen : ∀ row∈rows,row.length=n) (rest : List Bool) :
     readRectangularRows ((n,rows.length),rows.flatMap (fun row => row.flatMap RationalCode.bits)++rest)=
       (rows.map (List.map codeWords),rest) := by
   dsimp only [readRectangularRows]
   rw [readMatrixStep_codes n rows hlen]
   simp

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
 
 
 theorem readUnboundedNatural_expanded : Expanded readUnboundedNaturalRealizer (fun L => value (readWord L).1) :=
   polynomial_comp_expanded readWord_polynomial (expanded_pair
     (polynomial_comp_expanded (linear_polynomial linear_fst) value_expanded)
     (polynomial_expanded (linear_polynomial linear_snd) (fun s : List Bool×List Bool => value s.1)))
 theorem readUnboundedNatural_encoded (n : ℕ) (rest : List Bool) : readUnboundedNatural (encodeNat n++rest)=(n,rest) := by
   simp only [readUnboundedNatural,readWord_encoded,value_natBits]
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

 
 
 theorem skipOracleBound_polynomial : PolyBound skipOracleBoundRealizer := polynomial_pair
   (linear_polynomial linear_fst) (polynomial_comp (polynomial_comp (linear_polynomial linear_snd) readWord_polynomial) (linear_polynomial linear_snd))
 
 
 
 
 theorem oracleHeader_encoded (n B k : ℕ) (L : List Bool) :
     oracleHeader (encodeNat n++encodeNat B++encodeNat k++L)=(n,(k,L)) := by
   simp only [oracleHeader,Function.comp_apply,List.append_assoc,readUnboundedNatural_encoded,
     skipOracleBound,readWord_encoded,oracleCountHeader]
 
 
 theorem oracleRowsInput_polynomial : PolyBound oracleRowsInputRealizer := linear_polynomial
   (linear_pair (linear_pair (linear_comp linear_fst natSucc_linear) (linear_comp linear_snd linear_fst)) (linear_comp linear_snd linear_snd))
 
 
 theorem oracleNormals_polynomial : PolyBound oracleNormalsRealizer := polynomial_comp
   (polynomial_pair (polynomial_comp (polynomial_comp oracleRowsInput_polynomial readRectangularRows_polynomial) (linear_polynomial linear_fst))
     (linear_polynomial linear_fst))
   (polynomial_mapEnvironment (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) takeList_polynomial))
 
 

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

 
 
 theorem oracleQueryOutput_polynomial : PolyBound oracleQueryOutputRealizer := polynomial_comp
   (polynomial_pair (linear_polynomial (linear_constant Bool.true))
     (polynomial_comp (polynomial_comp (linear_polynomial linear_snd) oracleCoreQuery_polynomial) serializeRow_polynomial))
   (linear_polynomial linear_cons)
 
 
 
 

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

 theorem rationalCode_bits (q : ℚ) : (rationalCode q).bits=encodeRat q := rfl
 
 theorem halfspaceCodeRow_length {n : ℕ} (c : RationalHalfspace n) : (halfspaceCodeRow c).length=n+1 := by simp [halfspaceCodeRow]
 theorem halfspaceCodeRow_bits {n : ℕ} (c : RationalHalfspace n) :
     (halfspaceCodeRow c).flatMap RationalCode.bits=c.bits := by
   dsimp only [halfspaceCodeRow,RationalHalfspace.bits,vectorBits]
   rw [List.flatMap_append,List.flatMap_singleton,rationalCode_bits]
   congr 1
   simp only [List.flatMap_def,List.map_ofFn,Function.comp_def,rationalCode_bits]

 theorem oracleNormals_correct {n : ℕ} (cuts : List (RationalHalfspace n)) :
     oracleNormals (n,(cuts.length,cuts.flatMap RationalHalfspace.bits))=
       cuts.map (fun c => List.ofFn (fun i => codeWords (rationalCode (c.normal i)))) := by
   let rows := cuts.map halfspaceCodeRow
   have hr := readRectangularRows_codes (n+1) rows (by
     intro row hrow
     obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hrow
     exact halfspaceCodeRow_length c) []
   have hlen : rows.length=cuts.length := by simp [rows]
   have hbits : rows.flatMap (fun row => row.flatMap RationalCode.bits)=cuts.flatMap RationalHalfspace.bits := by
     simp only [rows,List.flatMap_map,Function.comp_def,halfspaceCodeRow_bits]
   rw [hlen,hbits,List.append_nil] at hr
   simp only [oracleNormals,oracleRowsInput,hr]
   simp only [rows,List.map_map]
   apply List.map_congr_left
   intro c hc
   simp only [rows,List.map_map,Function.comp_apply,halfspaceCodeRow,List.map_append,List.map_ofFn,List.map_singleton]
   rw [List.take_append_of_le_length (by simp)]
   rw [List.take_of_length_le (by simp)]
   rfl
 theorem parseOracleTranscript_correct (bound : Polynomial ℕ) (n : ℕ) (cuts : List (RationalHalfspace n)) :
     parseOracleTranscript (ellipsoidWord bound n cuts)=
       (n,cuts.map (fun c => List.ofFn (fun i => codeWords (rationalCode (c.normal i))))) := by
   simp only [parseOracleTranscript,Function.comp_apply,ellipsoidWord,oracleHeader_encoded,oracleNormals_correct]

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

 theorem phaseInitial_correct (n : ℕ) :
     (phaseInitial n).1=(n,0) ∧
       RepresentsMatrix (phaseInitial n).2.1 (1:Matrix (Fin n) (Fin n) ℚ) ∧
       RepresentsVector (phaseInitial n).2.2 (rationalVector (0:Fin n → ℚ)) ∧
       (∀ row∈(phaseInitial n).2.1,VectorCanonical row) ∧ VectorCanonical (phaseInitial n).2.2 := by
   have hm := matrixDiagonal_correct n scalarOne scalarOne_den
   rw [scalarOne_value,one_smul] at hm
   have hv : RepresentsVector (List.replicate n signedZero) (rationalVector (0:Fin n → ℚ)) := by
     refine ⟨fun _ => signedZero,?_,fun _ => zero_denpos,?_⟩
     · simp
     · intro i; simp only [zero_value,rationalVector,WithLp.ofLp_toLp,Pi.zero_apply,Rat.cast_zero]
   have hM := normalizeMatrix_rep hm
   have hV := normalizeVector_rep hv
   exact ⟨rfl,hM.1,hV.1,hM.2,hV.2⟩

 
 theorem ellipsoidPrefix_succ (n : ℕ) (vs : ℕ → SignedVector) (k : ℕ) :
     ellipsoidPrefix n vs (k+1)=ellipsoidPhaseStep (vs k,ellipsoidPrefix n vs k) := by
   simp only [ellipsoidPrefix,List.range_succ,List.map_append,List.map_singleton,List.foldl_append,List.foldl_cons,List.foldl_nil]
 theorem ellipsoidPrefix_correct {n : ℕ} (hn : 2 ≤ n) (vs : ℕ → SignedVector)
     (a : ℕ → Fin n → ℚ) (hv : ∀ k,RepresentsVector (vs k) (rationalVector (a k)))
     (ha : ∀ k,1 ≤ realVector (a k) ⬝ᵥ realVector (a k)) (k : ℕ) :
     (ellipsoidPrefix n vs k).1=(n,k) ∧
       RepresentsMatrix (ellipsoidPrefix n vs k).2.1 (shapes n a k) ∧
       RepresentsVector (ellipsoidPrefix n vs k).2.2 (rationalVector (centers n a 0 k)) ∧
       (∀ row∈(ellipsoidPrefix n vs k).2.1,VectorCanonical row) ∧
       VectorCanonical (ellipsoidPrefix n vs k).2.2 := by
   induction k with
   | zero => exact phaseInitial_correct n
   | succ k ih =>
     have hp := (shapes_invariant n hn a ha k).1
     have hne : realVector (a k)≠0 := by
       intro hz
       have hh := ha k
       rw [hz,dotProduct_zero] at hh
       norm_num at hh
     have hqR := hp.dotProduct_mulVec_pos hne
     have hq : 0 < a k ⬝ᵥ ((shapes n a k) *ᵥ a k) := by
       apply (Rat.cast_pos (K:=ℝ)).mp
       simpa only [dotProduct,mulVec,Rat.cast_sum,Rat.cast_mul,star_trivial,realVector,realShape,Matrix.map_apply] using hqR
     have hh := canonicalEllipsoidUpdate_correct hn k _ _ ih.2.1 _ _ _ _ (hv k) ih.2.2.1 hq
     rw [ellipsoidPrefix_succ]
     have he : phaseStepData (vs k,ellipsoidPrefix n vs k)=
         ((n,k),((ellipsoidPrefix n vs k).2.1,(vs k,(ellipsoidPrefix n vs k).2.2))) := by
       dsimp only [phaseStepData]; rw [ih.1]
     have hc : phaseStepCounter (vs k,ellipsoidPrefix n vs k)=(n,k+1) := by
       dsimp only [phaseStepCounter]; rw [ih.1]
     simp only [ellipsoidPhaseStep,he,hc]
     exact ⟨by trivial,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2⟩

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidPrefixCongruence
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence

 theorem ellipsoidPrefix_congr {n k : ℕ} (vs ws : ℕ → SignedVector)
     (h : ∀ i < k,vs i=ws i) : ellipsoidPrefix n vs k=ellipsoidPrefix n ws k := by
   unfold ellipsoidPrefix
   congr 1
   apply List.map_congr_left
   intro i hi
   exact h i (List.mem_range.mp hi)
 theorem shapes_congr_before {n k : ℕ} (a b : ℕ → Fin n → ℚ)
     (h : ∀ i < k,a i=b i) : shapes n a k=shapes n b k := by
   induction k with
   | zero => rfl
   | succ k ih =>
     simp only [shapes,ih (fun i hi => h i (by omega)),h k (by omega)]
 theorem centers_congr_before {n k : ℕ} (a b : ℕ → Fin n → ℚ) (c : Fin n → ℚ)
     (h : ∀ i < k,a i=b i) : centers n a c k=centers n b c k := by
   induction k with
   | zero => rfl
   | succ k ih =>
     have hs : shapes n a k=shapes n b k := shapes_congr_before a b (fun i hi => h i (by omega))
     simp only [centers,ih (fun i hi => h i (by omega)),hs,h k (by omega)]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleCounterMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 
 
 theorem phaseBudget_four (n : ℕ) : 4 ≤ phaseBudget n := by
   dsimp [phaseBudget,GLS.EllipsoidSequence.thresholdSteps]
   have h1 : 1 ≤ n+1 := by omega
   have h2 : 1 ≤ phaseThresholdExponent n*n+1 := by omega
   nlinarith
 theorem counter_good_initial (N : ℕ) : CounterGood N (oracleInitial N).2 := by
   exact ⟨le_rfl,phaseBudget_pos N,by simp [oracleInitial,phaseInitial]⟩
 theorem counter_potential_pos {N : ℕ} (st : OracleCoreState) (hg : CounterGood N st) :
     0 < counterPotential N st := by
   have hk := hg.2.1.trans_le (phaseBudget_mono hg.1)
   have hb : phaseBudget N+3 ≤ (st.2.1.1+1)*(phaseBudget N+3) := Nat.le_mul_of_pos_left _ (by omega)
   dsimp only [counterPotential]
   omega
 theorem dimensionReduction_counter (st : OracleCoreState) :
     (oracleDimensionReduction st).2.1=(st.2.1.1-1,0) := rfl
 theorem phaseAdvance_counter (s : OraclePreparedCut) :
     (oraclePhaseAdvance s).2.1=(s.2.2.1.1,s.2.2.1.2+1) := rfl
 theorem smallAdvance_counter (s : OraclePreparedCut) :
     (oracleSmallAdvance s).2.2.1=(s.2.2.1.1,1) := rfl

 theorem counter_big_progress {N : ℕ} (s : OraclePreparedCut) (hg : CounterGood N s.2)
     (hbig : 1 < s.2.2.1.1) :
     CounterGood N (oracleBigCut s).2 ∧ counterPotential N (oracleBigCut s).2 < counterPotential N s.2 := by
   let n := s.2.2.1.1
   let k := s.2.2.1.2
   have hn : n ≤ N := hg.1
   have hk : k < phaseBudget n := hg.2.1
   have hK := phaseBudget_mono hn
   have hbase : phaseBudget N+3 ≤ (n+1)*(phaseBudget N+3) := Nat.le_mul_of_pos_left _ (by omega)
   change CounterGood N (oracleBoundary (oraclePhaseAdvance s)) ∧ counterPotential N (oracleBoundary (oraclePhaseAdvance s)) < counterPotential N s.2
   unfold oracleBoundary
   split_ifs with h
   · have he := dimensionReduction_counter (oraclePhaseAdvance s)
     rw [phaseAdvance_counter] at he
     have hn' : (oracleDimensionReduction (oraclePhaseAdvance s)).2.1.1=n-1 := by simpa only using congrArg (fun x : ℕ×ℕ => x.1) he
     have hk' : (oracleDimensionReduction (oraclePhaseAdvance s)).2.1.2=0 := by simpa only using congrArg (fun x : ℕ×ℕ => x.2) he
     constructor
     · exact ⟨by rw [hn']; omega,by rw [hn',hk']; exact phaseBudget_pos _,by rw [hk']; omega⟩
     · change (counterPotential N (oracleDimensionReduction (oraclePhaseAdvance s))) < counterPotential N s.2
       dsimp only [counterPotential]
       rw [hn',hk',Nat.sub_zero,show n-1+1=n by omega]
       change n*(phaseBudget N+3) < (n+1)*(phaseBudget N+3)-k
       rw [Nat.add_mul,one_mul]
       omega
   · have he := phaseAdvance_counter s
     have hn' : (oraclePhaseAdvance s).2.1.1=n := by simpa only using congrArg (fun x : ℕ×ℕ => x.1) he
     have hk' : (oraclePhaseAdvance s).2.1.2=k+1 := by simpa only using congrArg (fun x : ℕ×ℕ => x.2) he
     have hlt : k+1 < phaseBudget n := by
       have hh : ¬phaseBudget n ≤ k+1 := by
         simpa only [oracleAtBoundary,hn',hk',decide_eq_true_eq] using h
       omega
     constructor
     · exact ⟨by rw [hn']; exact hn,by rw [hn',hk']; exact hlt,by rw [hn']; omega⟩
     · change counterPotential N (oraclePhaseAdvance s) < counterPotential N s.2
       dsimp only [counterPotential]
       rw [hn',hk']
       change (n+1)*(phaseBudget N+3)-(k+1) < (n+1)*(phaseBudget N+3)-k
       omega

 theorem counter_small_progress {N : ℕ} (s : OraclePreparedCut) (hg : CounterGood N s.2)
     (hsmall : s.2.2.1.1 ≤ 1) :
     (oracleSmallCut s).1=true ∨
       (CounterGood N (oracleSmallCut s).2 ∧ counterPotential N (oracleSmallCut s).2 < counterPotential N s.2) := by
   unfold oracleSmallCut
   split_ifs with h
   · right
     have hk : s.2.2.1.2=0 := by simpa only [oracleSmallFirst,decide_eq_true_eq] using h
     have he := smallAdvance_counter s
     have hn' := by simpa only using congrArg (fun x : ℕ×ℕ => x.1) he
     have hk' := by simpa only using congrArg (fun x : ℕ×ℕ => x.2) he
     constructor
     · refine ⟨?_,?_,?_⟩
       · rw [hn']; exact hg.1
       · rw [hn',hk']; exact lt_of_lt_of_le (by omega) (phaseBudget_four _)
       · rw [hk']; omega
     · dsimp only [counterPotential]
       rw [hn',hk',hk]
       have hbase : 1 < (s.2.2.1.1+1)*(phaseBudget N+3) := by
         have hh : phaseBudget N+3 ≤ (s.2.2.1.1+1)*(phaseBudget N+3) := Nat.le_mul_of_pos_left _ (by omega)
         omega
       omega
   · exact Or.inl rfl

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

 
 

 
 
 theorem phaseGeometry_dimension {n : ℕ} (V : Finset (Fin n → Bool)) (st : EllipsoidPhaseState)
     (h : PhaseGeometry V st) : st.1.1=n := by
   cases h with
   | small hn hs => exact hs.1
   | large hn vs a k hv ha hst hk hcuts =>
     rw [hst]
     exact congrArg Prod.fst (ellipsoidPrefix_correct hn vs a hv ha k).1
 theorem phaseGeometry_counter_bound {n : ℕ} (V : Finset (Fin n → Bool)) (st : EllipsoidPhaseState)
     (h : PhaseGeometry V st) : st.1.2 ≤ phaseBudget n := by
   cases h with
   | small hn hs => exact hs.2.1.trans ((by omega : 1 ≤ 4).trans (phaseBudget_four n))
   | large hn vs a k hv ha hst hk hcuts =>
     rw [hst]
     have hh := congrArg Prod.snd (ellipsoidPrefix_correct hn vs a hv ha k).1
     rw [hh]
     exact hk

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

 theorem oracleCoreQuery_correct {N n : ℕ} (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (c : Fin n → ℚ)
     (hA : RepresentsRectMatrix st.1.1 A) (hb : RepresentsVector st.1.2 (rationalVector b))
     (hc : RepresentsVector st.2.2.2 (rationalVector c)) (hdim : st.2.1.1=n) :
     RepresentsVector (oracleCoreQuery st) (rationalVector (A *ᵥ ((n+1:ℚ) • c)+b)) := by
   have hscale := represents_rational_scale _ _ hc (naturalSignedWord (st.2.1.1+1)) (naturalSignedWord_den _)
   rw [naturalSignedWord_value,hdim] at hscale
   have hval : ((n+1:ℕ):ℚ)=(n+1:ℚ) := by push_cast; rfl
   rw [hval] at hscale
   have hh := affineEvaluation_correct st.1.1 st.1.2 _ A b _ hA hb hscale
   simpa only [oracleCoreQuery,hdim] using hh

 theorem oraclePrepareCut_correct {N n : ℕ} (as : SignedVector) (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin n) ℚ) (a : Fin N → ℚ)
     (hA : RepresentsRectMatrix st.1.1 A) (ha : RepresentsVector as (rationalVector a))
     (hdim : st.2.1.1=n) :
     ∃ (p : Fin n → ℤ) (T : ℝ),0 < T ∧
       RepresentsVector (oraclePrepareCut (as,st)).1 (WithLp.toLp 2 (fun i => (p i:ℝ))) ∧
       (∀ i,(p i:ℝ)=T*((a ᵥ* A) i:ℝ)) ∧ (oraclePrepareCut (as,st)).2=st := by
   have hpull := affinePullback_correct st.1.1 as A a hA ha
   have hdata : oraclePullbackData (as,st)=(n,(as,st.1.1)) := by
     dsimp only [oraclePullbackData]; rw [hdim]
   obtain ⟨p,T,hT,hrep,hp⟩ := clearRationalVector_correct _ _ hpull
   refine ⟨p,T,hT,?_,hp,rfl⟩
   simpa only [oraclePrepareCut,hdata] using hrep

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

 
 
 
 theorem affine_integer_height_coordinates {m n J : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
     (hA : AffineIntegerHeight J A b) :
     (∀ i j,(A i j).num.natAbs ≤ 2^J ∧ (A i j).den ≤ 2^J) ∧
       ∀ i,(b i).num.natAbs ≤ 2^J ∧ (b i).den ≤ 2^J := by
   obtain ⟨D,U,v,hD,hDb,hU,hv⟩ := hA
   constructor
   · intro i j
     rw [(hU i j).2]
     have hh := integer_ratio_num_den_bound (U i j) D hD
     exact ⟨hh.1.trans (hU i j).1,hh.2.trans hDb⟩
   · intro i
     rw [(hv i).2]
     have hh := integer_ratio_num_den_bound (v i) D hD
     exact ⟨hh.1.trans (hv i).1,hh.2.trans hDb⟩

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

 theorem hyperplaneCoordinates_correct {n : ℕ} (us cs : SignedVector) (u c : Fin n → ℚ)
     (hu : RepresentsVector us (rationalVector u)) (hc : RepresentsVector cs (rationalVector c)) :
     RepresentsVector (hyperplaneCoordinates (n,(us,cs)))
       (rationalVector (Fin.snoc u ((n+1:ℚ)*(u ⬝ᵥ c)))) := by
   have hd := represents_rational_dot us cs u c hu hc
   have hbD : 0 < value (hyperplaneBeta (n,(us,cs))).2.2 :=
     canonicalMul_denpos _ _ (naturalSignedWord_den (n+1)) hd.1
   have hb : signedFractionValue (hyperplaneBeta (n,(us,cs)))=(n+1:ℚ)*(u ⬝ᵥ c) := by
     rw [hyperplaneBeta,canonicalMul_value _ _ (naturalSignedWord_den (n+1)) hd.1,
       naturalSignedWord_value,hd.2]
     norm_cast
   have hh := represents_rational_append us u hu _ hbD
   rw [hb] at hh
   exact hh

 

 

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

 theorem diagonalMaxStep_bounds (a b : DiagonalEntry)
     (ha : 0 < value a.2.2.2) (hb : 0 < value b.2.2.2) :
     fractionValue a.2.2 ≤ fractionValue (diagonalMaxStep (a,b)).2.2 ∧
       fractionValue b.2.2 ≤ fractionValue (diagonalMaxStep (a,b)).2.2 := by
   have hc := fractionLE_correct b.2.2 a.2.2 hb ha
   unfold diagonalMaxStep diagonalCompare
   split_ifs with h
   · exact ⟨le_rfl,hc.mp h⟩
   · exact ⟨le_of_not_ge (fun hh => h (hc.mpr hh)),le_rfl⟩

 theorem diagonalFold_member (xs : List DiagonalEntry) (b : DiagonalEntry) :
     xs.foldl (fun b a => diagonalMaxStep (a,b)) b ∈ b::xs := by
   induction xs generalizing b with
   | nil => simp
   | cons a xs ih =>
     simp only [List.foldl_cons]
     have hh := ih (diagonalMaxStep (a,b))
     rcases List.mem_cons.mp hh with he | he
     · rcases diagonalMaxStep_select a b with h | h
       · rw [he,h]; simp
       · rw [he,h]; simp
     · simp only [List.mem_cons]; exact Or.inr (Or.inr he)

 theorem diagonalFold_bounds (xs : List DiagonalEntry) (b : DiagonalEntry)
     (hb : 0 < value b.2.2.2) (hx : ∀ a∈xs,0 < value a.2.2.2) :
     fractionValue b.2.2 ≤ fractionValue (xs.foldl (fun b a => diagonalMaxStep (a,b)) b).2.2 ∧
       ∀ a∈xs,fractionValue a.2.2 ≤ fractionValue (xs.foldl (fun b a => diagonalMaxStep (a,b)) b).2.2 := by
   induction xs generalizing b with
   | nil => exact ⟨le_rfl,by simp⟩
   | cons a xs ih =>
     have ha := hx a (by simp)
     have hs := diagonalMaxStep_bounds a b ha hb
     have hp : 0 < value (diagonalMaxStep (a,b)).2.2.2 := by
       rcases diagonalMaxStep_select a b with h | h <;> rw [h] <;> assumption
     have hh := ih (diagonalMaxStep (a,b)) hp (fun a ha => hx a (by simp [ha]))
     refine ⟨hs.2.trans hh.1,?_⟩
     intro c hc
     rcases List.mem_cons.mp hc with rfl | hc
     · exact hs.1.trans hh.1
     · exact hh.2 c hc

 theorem diagonalWinner_member (xs : List DiagonalEntry) (hne : xs ≠ []) : diagonalWinner xs ∈ xs := by
   have hh := diagonalFold_member xs (xs.headD (0,signedZero))
   rcases List.mem_cons.mp hh with he | he
   · unfold diagonalWinner
     rw [he]
     cases xs with
     | nil => exact (hne rfl).elim
     | cons a xs => simp
   · exact he

 theorem diagonalWinner_bounds (xs : List DiagonalEntry) (hne : xs ≠ [])
     (hx : ∀ a∈xs,0 < value a.2.2.2) :
     ∀ a∈xs,fractionValue a.2.2 ≤ fractionValue (diagonalWinner xs).2.2 := by
   have hm : xs.headD (0,signedZero) ∈ xs := by
     cases xs with
     | nil => exact (hne rfl).elim
     | cons a xs => simp
   exact (diagonalFold_bounds xs _ (hx _ hm) hx).2

 theorem diagonalWordAt_correct {n : ℕ} (bs : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ)
     (hA : RepresentsMatrix bs A) (i : Fin n) :
     0 < value (diagonalWordAt (i.val,bs)).2.2 ∧
       signedFractionValue (diagonalWordAt (i.val,bs))=A i i := by
   obtain ⟨rows,rfl,hrows⟩ := hA
   simp only [diagonalWordAt,array_lookup_ofFn]
   have hh := represents_lookup (rows i) (rationalVector (A i)) (hrows i) i signedZero
   exact ⟨hh.1,Rat.cast_injective (α:=ℝ) hh.2⟩

 theorem diagonalEntries_member {n : ℕ} (bs : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ)
     (hA : RepresentsMatrix bs A) (a : DiagonalEntry) :
     a∈diagonalEntries bs ↔ ∃ i : Fin n,a=(i.val,diagonalWordAt (i.val,bs)) := by
   have hn : bs.length=n := by obtain ⟨rows,rfl,hr⟩ := hA; simp
   simp only [diagonalEntries,hn,List.mem_map,List.mem_range,diagonalEntryAt]
   constructor
   · rintro ⟨i,hi,rfl⟩; exact ⟨⟨i,hi⟩,rfl⟩
   · rintro ⟨i,rfl⟩; exact ⟨i.val,i.isLt,rfl⟩

 theorem maximumDiagonal_correct {n : ℕ} (hn : 0 < n) (bs : SignedMatrix)
     (A : Matrix (Fin n) (Fin n) ℚ) (hA : RepresentsMatrix bs A)
     (hpos : ∀ i,0 < A i i) :
     ∃ k : Fin n,maximumDiagonal bs=(k.val,diagonalWordAt (k.val,bs)) ∧
       (∀ i,A i i ≤ A k k) := by
   have hne : diagonalEntries bs ≠ [] := by
     have hm := (diagonalEntries_member bs A hA (0,diagonalWordAt (0,bs))).mpr
       ⟨⟨0,hn⟩,rfl⟩
     intro he; rw [he] at hm; cases hm
   have hmem := diagonalWinner_member (diagonalEntries bs) hne
   obtain ⟨k,hk⟩ := (diagonalEntries_member bs A hA _).mp hmem
   refine ⟨k,hk,?_⟩
   have hx : ∀ a∈diagonalEntries bs,0 < value a.2.2.2 := by
     intro a ha
     obtain ⟨i,rfl⟩ := (diagonalEntries_member bs A hA a).mp ha
     exact (diagonalWordAt_correct bs A hA i).1
   intro i
   have hm := diagonalWinner_bounds (diagonalEntries bs) hne hx
     (i.val,diagonalWordAt (i.val,bs)) ((diagonalEntries_member bs A hA _).mpr ⟨i,rfl⟩)
   rw [hk] at hm
   simp only [fractionValue_abs,(diagonalWordAt_correct bs A hA i).2,
     (diagonalWordAt_correct bs A hA k).2,abs_of_pos (hpos i),abs_of_pos (hpos k)] at hm
   exact hm

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PositiveMatrixCauchy
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.EllipsoidMath

 theorem symmetric_dot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
     (x y : Fin n → ℝ) : x ⬝ᵥ (A *ᵥ y)=y ⬝ᵥ (A *ᵥ x) := by
   simp only [dotProduct,mulVec,Finset.mul_sum]
   rw [Finset.sum_comm]
   apply Finset.sum_congr rfl
   intro i hi
   apply Finset.sum_congr rfl
   intro j hj
   rw [hA.apply j i]
   ring

 theorem positive_matrix_cauchy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
     (x y : Fin n → ℝ) :
     (x ⬝ᵥ (A *ᵥ y))^2≤(x ⬝ᵥ (A *ᵥ x))*(y ⬝ᵥ (A *ᵥ y)) := by
   by_cases hx : x=0
   · simp [hx]
   have hp : 0< x ⬝ᵥ (A *ᵥ x) := by simpa only [star_trivial] using hA.dotProduct_mulVec_pos hx
   have hsym : A.IsSymm := isHermitian_iff_isSymm.mp hA.isHermitian
   have hcross := symmetric_dot A hsym y x
   let t := (x ⬝ᵥ (A *ᵥ y))/(x ⬝ᵥ (A *ᵥ x))
   have hnonneg := hA.posSemidef.dotProduct_mulVec_nonneg (y-t • x)
   simp only [star_trivial,mulVec_sub,mulVec_smul,sub_dotProduct,dotProduct_sub,
     dotProduct_smul,smul_dotProduct,smul_eq_mul,hcross] at hnonneg
   have he : t*(x ⬝ᵥ (A *ᵥ x))=x ⬝ᵥ (A *ᵥ y) := by dsimp [t]; exact div_mul_cancel₀ _ (ne_of_gt hp)
   have hh := mul_nonneg (le_of_lt hp) hnonneg
   nlinarith only [he,hh]

end EdgeSublinearMWIS.Main.EllipsoidMath
end

-- Solutions.PositiveMatrixEntryBound
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.EllipsoidMath

 theorem positive_matrix_entry_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
     (i j : Fin n) : (A i j)^2≤ A i i*A j j := by
   have h := positive_matrix_cauchy A hA (Pi.single i 1) (Pi.single j 1)
   simpa [dotProduct,mulVec,Pi.single_apply] using h

 theorem positive_matrix_entry_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
     (L : ℝ) (hL : 0≤ L) (hdiag : ∀ i,A i i≤ L) : ∀ i j,|A i j|≤ L := by
   intro i j
   have hs := positive_matrix_entry_sq A hA i j
   have hmul := mul_le_mul (hdiag i) (hdiag j) (le_of_lt (hA.diag_pos (i:=j))) hL
   have hsq : (A i j)^2≤ L^2 := by nlinarith
   exact (sq_le_sq₀ (abs_nonneg _) hL).mp (by simpa only [sq_abs] using hsq)

 

end EdgeSublinearMWIS.Main.EllipsoidMath
end

-- Solutions.EllipsoidThinDirection
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.EllipsoidMath

 
 

 
 theorem normalizedColumn_bounded {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef) (k : Fin n)
     (hmax : ∀ i,B i i≤ B k k) : ∀ i,|normalizedColumn B k i|≤1 := by
   intro i
   rw [normalizedColumn,abs_div,abs_of_pos (hB.diag_pos (i:=k))]
   exact (div_le_one (hB.diag_pos (i:=k))).mpr
     (positive_matrix_entry_bound B hB (B k k) (le_of_lt (hB.diag_pos (i:=k))) hmax i k)

 

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

 theorem normalizedDirectionWords_correct {n : ℕ} (bs : SignedMatrix)
     (B : Matrix (Fin n) (Fin n) ℚ) (hB : RepresentsMatrix bs B) (k : Fin n)
     (hkk : B k k ≠ 0) :
     RepresentsVector (normalizedDirectionWords (bs,(k.val,diagonalWordAt (k.val,bs))))
       (rationalVector (fun i => B i k/B k k)) := by
   let s : ThinDirectionData := (bs,(k.val,diagonalWordAt (k.val,bs)))
   have hdiag := diagonalWordAt_correct bs B hB k
   have hnum := signed_num_positive_of_nonzero _ (by rw [hdiag.2]; exact hkk)
   have hrecD : 0 < value (thinDirectionReciprocal s).2.2 :=
     canonicalDiv_denpos _ _ scalarOne_den hnum
   have hrec : signedFractionValue (thinDirectionReciprocal s)=(B k k)⁻¹ := by
     rw [thinDirectionReciprocal,canonicalDiv_value _ _ scalarOne_den hnum,scalarOne_value,hdiag.2,one_div]
   have hcol := matrixColumn_correct bs B hB k
   have hscale := represents_rational_scale _ _ hcol _ hrecD
   rw [hrec] at hscale
   have he : ((B k k)⁻¹ • (fun i => B i k))=(fun i => B i k/B k k) := by
     funext i; simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
   rw [he] at hscale
   exact hscale

 theorem inverseThinDirection_correct {n : ℕ} (hn : 0 < n) (bs : SignedMatrix)
     (B : Matrix (Fin n) (Fin n) ℚ) (hB : RepresentsMatrix bs B)
     (hp : (castMatrix B).PosDef) :
     ∃ k : Fin n,(inverseThinDirection bs).2=k.val ∧
       RepresentsVector (inverseThinDirection bs).1
         (rationalVector (fun i => B i k/B k k)) ∧
       (∀ i,B i i ≤ B k k) := by
   have hpos : ∀ i,0 < B i i := fun i => (Rat.cast_pos (K:=ℝ)).mp (hp.diag_pos (i:=i))
   obtain ⟨k,hk,hmax⟩ := maximumDiagonal_correct hn bs B hB hpos
   refine ⟨k,?_,?_,hmax⟩
   · simp only [inverseThinDirection,Function.comp_apply,thinDirectionData,thinDirectionFinish,hk]
   · simpa only [inverseThinDirection,Function.comp_apply,thinDirectionData,thinDirectionFinish,hk] using
       normalizedDirectionWords_correct bs B hB k (ne_of_gt (hpos k))

 

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

 theorem counter_prepared_progress {N : ℕ} (s : OraclePreparedCut) (hg : CounterGood N s.2) :
     (oraclePreparedCut s).1=true ∨
       (CounterGood N (oraclePreparedCut s).2 ∧ counterPotential N (oraclePreparedCut s).2 < counterPotential N s.2) := by
   unfold oraclePreparedCut
   split_ifs with h
   · unfold oracleNonzeroCut
     split_ifs with hs
     · exact counter_small_progress s hg (by simpa only [oracleSmall,decide_eq_true_eq] using hs)
     · right
       exact counter_big_progress s hg (by
         have hh : ¬s.2.2.1.1 ≤ 1 := by simpa only [oracleSmall,decide_eq_true_eq] using hs
         omega)
   · exact Or.inl rfl
 theorem counter_cut_progress {N : ℕ} (s : OracleCutInput) (hg : CounterGood N s.2.2) :
     (oracleCut s).1=true ∨
       (CounterGood N (oracleCut s).2 ∧ counterPotential N (oracleCut s).2 < counterPotential N s.2.2) := by
   unfold oracleCut
   split_ifs with h
   · exact Or.inl h
   · exact counter_prepared_progress (oraclePrepareCut (s.1,s.2.2)) hg
 theorem oracleCut_rejected (as : SignedVector) (st : OracleState) (hs : st.1=true) :
     oracleCut (as,st)=st := by simp only [oracleCut,hs,if_true]
 theorem foldCut_rejected (xs : SignedMatrix) (st : OracleState) (hs : st.1=true) :
     xs.foldl (fun st cut => oracleCut (cut,st)) st=st := by
   induction xs with
   | nil => rfl
   | cons a xs ih =>
     rw [List.foldl_cons,oracleCut_rejected a st hs,ih]
 theorem foldCut_counter {N : ℕ} (xs : SignedMatrix) (st : OracleState) (hg : CounterGood N st.2) :
     let out := xs.foldl (fun st cut => oracleCut (cut,st)) st
     out.1=true ∨ (CounterGood N out.2 ∧ counterPotential N out.2+xs.length ≤ counterPotential N st.2) := by
   induction xs generalizing st with
   | nil =>
     right
     exact ⟨hg,by simp⟩
   | cons a xs ih =>
     have hh := counter_cut_progress (a,st) hg
     rcases hh with hr | ⟨hg',hless⟩
     · left
       simpa only [List.foldl_cons,foldCut_rejected xs _ hr] using hr
     · change counterPotential N (oracleCut (a,st)).2 < counterPotential N st.2 at hless
       have hh := ih (oracleCut (a,st)) hg'
       rcases hh with hr | ⟨hgood,hbound⟩
       · exact Or.inl hr
       · right
         exact ⟨hgood,by simp only [List.length_cons,List.foldl_cons]; omega⟩
 theorem oracleExecute_forced_reject (N : ℕ) (xs : SignedMatrix)
     (hlen : (N+1)*(phaseBudget N+3) ≤ xs.length) :
     (oracleExecute (N,xs)).1=true := by
   have hh := foldCut_counter xs (oracleInitial N) (counter_good_initial N)
   rcases hh with hr | ⟨hgood,hbound⟩
   · exact hr
   · have hp := counter_potential_pos _ hgood
     have he : counterPotential N (oracleInitial N).2=(N+1)*(phaseBudget N+3) := rfl
     rw [he] at hbound
     omega

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleQueryBudget
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools

 theorem phaseBudget_upper (n : ℕ) : phaseBudget n ≤ 200*(n+1)^4 := by
   let z := n+1
   have hz : 1 ≤ z := by dsimp [z]; omega
   have hn : n ≤ z := by dsimp [z]; omega
   have hn2 : n+2 ≤ 2*z := by dsimp [z]; omega
   have hp1 : z ≤ z^2 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1 ≤ 2)
   have hp2 : 1 ≤ z^3 := one_le_pow₀ hz
   have hS : thinExponent n ≤ 40*z^2 := by
     have hh := Nat.pow_le_pow_left hn2 2
     dsimp only [thinExponent]
     nlinarith [sq_nonneg z]
   have hE : phaseThresholdExponent n ≤ 41*z^2 := by dsimp [phaseThresholdExponent]; dsimp [z] at *; nlinarith
   have hinner : phaseBudgetInner n ≤ 42*z^3 := by
     have hh := Nat.mul_le_mul hE hn
     dsimp only [phaseBudgetInner]
     have he : 41*z^2*z=41*z^3 := by ring
     rw [he] at hh
     nlinarith
   have hh := Nat.mul_le_mul_left (4*z) hinner
   have he : 4*z*(42*z^3)=168*z^4 := by ring
   rw [he] at hh
   change 4*z*phaseBudgetInner n ≤ 200*z^4
   exact hh.trans (Nat.mul_le_mul_right _ (by omega))
 theorem oracle_counter_budget_upper (n : ℕ) :
     (n+1)*(phaseBudget n+3) ≤ 203*(n+1)^5 := by
   have hk := phaseBudget_upper n
   have h1 : 1 ≤ (n+1)^4 := one_le_pow₀ (by omega)
   have hh := Nat.mul_le_mul_left (n+1) (show phaseBudget n+3 ≤ 203*(n+1)^4 by omega)
   convert hh using 1 <;> ring
 
 theorem oracleQueries_eval (n : ℕ) : oracleQueries.eval (n+1)=203*(n+1)^5 := by simp [oracleQueries]
 theorem oracleExecute_reject_at_budget (n : ℕ) (xs : SignedMatrix)
     (hlen : xs.length=oracleQueries.eval (n+1)) : (oracleExecute (n,xs)).1=true := by
   apply oracleExecute_forced_reject
   rw [hlen,oracleQueries_eval]
   exact oracle_counter_budget_upper n

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

 
 
 
 
 theorem ellipsoidThinDirection_rational {n : ℕ} (hn : 0 < n) (bs : SignedMatrix)
     (A : Matrix (Fin n) (Fin n) ℚ) (hA : RepresentsMatrix bs A) (hp : (castMatrix A).PosDef) :
     ∃ k : Fin n,
       RepresentsVector (ellipsoidThinDirection bs).1
         (rationalVector (fun i => A⁻¹ i k/A⁻¹ k k)) ∧
       (∀ i,|((A⁻¹ i k/A⁻¹ k k:ℚ):ℝ)| ≤ 1) := by
   have hInv := matrixInverseWords_correct bs A hA hp
   have hcast := castMatrix_inv A (castMatrix_unit A hp)
   have hpInv : (castMatrix A⁻¹).PosDef := by rw [hcast]; exact hp.inv
   obtain ⟨k,hk,hrep,hmax⟩ := inverseThinDirection_correct hn _ A⁻¹ hInv.1 hpInv
   have hmaxR : ∀ i,(castMatrix A)⁻¹ i i ≤ (castMatrix A)⁻¹ k k := by
     intro i
     have hh : (castMatrix A⁻¹) i i ≤ (castMatrix A⁻¹) k k := by
       change ((A⁻¹ i i:ℚ):ℝ) ≤ ((A⁻¹ k k:ℚ):ℝ)
       exact_mod_cast hmax i
     rwa [hcast] at hh
   refine ⟨k,hrep,?_⟩
   intro i
   have hh := normalizedColumn_bounded _ hp.inv k hmaxR i
   have he : ((A⁻¹ i k/A⁻¹ k k:ℚ):ℝ)=normalizedColumn ((castMatrix A)⁻¹) k i := by
     rw [Rat.cast_div]
     change (castMatrix A⁻¹) i k/(castMatrix A⁻¹) k k=_
     rw [hcast]; rfl
   rwa [←he] at hh

 

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

 
 theorem affineLift_rational {N n : ℕ} (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ)
     (z : Fin n → ℚ) :
     (fun i => ((A *ᵥ z+b) i:ℝ))=affineLift A b (fun i => (z i:ℝ)) := by
   ext i
   simp [affineLift,Matrix.mulVec,dotProduct]
 

 
 
 
 

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

 theorem ellipsoid_history_append {n : ℕ} (vs : ℕ → SignedVector) (a : ℕ → Fin n → ℚ)
     (hv : ∀ j,RepresentsVector (vs j) (rationalVector (a j)))
     (ha : ∀ j,1 ≤ realVector (a j) ⬝ᵥ realVector (a j)) (k : ℕ)
     (V : Finset (Fin n → Bool))
     (hcuts : ∀ j < k,∀ v∈V,realVector (a j) ⬝ᵥ
       ((fun i => (if v i then 1 else 0)/(n+1:ℝ))-realVector (centers n a 0 j)) ≤ 0)
     (ps : SignedVector) (p : Fin n → ℤ)
     (hp : RepresentsVector ps (rationalVector (fun i => (p i:ℚ)))) (hne : p≠0)
     (hcut : ∀ v∈V,realVector (fun i => (p i:ℚ)) ⬝ᵥ
       ((fun i => (if v i then 1 else 0)/(n+1:ℝ))-realVector (centers n a 0 k)) ≤ 0) :
     ∃ (ws : ℕ → SignedVector) (b : ℕ → Fin n → ℚ),
       (∀ j,RepresentsVector (ws j) (rationalVector (b j))) ∧
       (∀ j,1 ≤ realVector (b j) ⬝ᵥ realVector (b j)) ∧
       ellipsoidPhaseStep (ps,ellipsoidPrefix n vs k)=ellipsoidPrefix n ws (k+1) ∧
       (∀ j < k+1,∀ v∈V,realVector (b j) ⬝ᵥ
         ((fun i => (if v i then 1 else 0)/(n+1:ℝ))-realVector (centers n b 0 j)) ≤ 0) := by
   let ws := Function.update vs k ps
   let b := Function.update a k (fun i => (p i:ℚ))
   have hvs : ∀ j < k,ws j=vs j := by intro j hj; exact Function.update_of_ne (by omega) _ _
   have hab : ∀ j < k,b j=a j := by intro j hj; exact Function.update_of_ne (by omega) _ _
   have hcenter : ∀ j,j ≤ k → centers n b 0 j=centers n a 0 j := by
     intro j hj
     exact centers_congr_before b a 0 (fun i hi => hab i (by omega))
   refine ⟨ws,b,?_,?_,?_,?_⟩
   · intro j
     by_cases hj : j=k
     · subst j; simpa only [ws,b,Function.update_self] using hp
     · simpa only [ws,b,Function.update_of_ne hj] using hv j
   · intro j
     by_cases hj : j=k
     · subst j; simpa only [b,Function.update_self] using integer_vector_norm_lower p hne
     · simpa only [b,Function.update_of_ne hj] using ha j
   · rw [ellipsoidPrefix_succ,ellipsoidPrefix_congr ws vs hvs]
     simp only [ws,Function.update_self]
   · intro j hj v hvV
     by_cases he : j=k
     · subst j
       rw [show b k=(fun i => (p i:ℚ)) from Function.update_self _ _ _,hcenter k le_rfl]
       exact hcut v hvV
     · have hjk : j < k := by omega
       rw [hab j hjk,hcenter j hjk.le]
       exact hcuts j hjk v hvV

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

 theorem coreModel_phase_advance {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig st A b V) (hn : 2 ≤ n) (hk : st.2.1.2 < phaseBudget n)
     (ps : SignedVector) (p : Fin n → ℤ)
     (hp : RepresentsVector ps (rationalVector (fun i => (p i:ℚ)))) (hne : p≠0)
     (hcut : ∀ c : Fin n → ℚ,RepresentsVector st.2.2.2 (rationalVector c) →
       ∀ v∈V,realVector (fun i => (p i:ℚ)) ⬝ᵥ
         ((fun i => (if v i then 1 else 0)/(n+1:ℝ))-realVector c) ≤ 0) :
     CoreModel Orig (oraclePhaseAdvance (ps,st)) A b V := by
   have hphase : PhaseGeometry V (ellipsoidPhaseStep (ps,st.2)) := by
     cases h.phase with
     | small hnsmall hs => omega
     | large hn vs a k hv ha hst hbudget hcuts =>
       have hc := (ellipsoidPrefix_correct hn vs a hv ha k).2.2.1
       rw [←hst] at hc
       have hnewcut := hcut (centers n a 0 k) hc
       obtain ⟨ws,b',hw,hb',happend,hcuts'⟩ := ellipsoid_history_append vs a hv ha k V hcuts ps p hp hne hnewcut
       have hmeta := (ellipsoidPrefix_correct hn vs a hv ha k).1
       rw [←hst] at hmeta
       have hk' : k < phaseBudget n := by simpa only [congrArg Prod.snd hmeta] using hk
       exact PhaseGeometry.large hn ws b' (k+1) hw hb'
         (by rw [hst,happend]) (by omega) hcuts'
   exact ⟨h.order,h.affineRows,h.affineOffsets,h.rowsCanonical,h.offsetsCanonical,h.height,hphase,h.lifts,h.nonempty⟩

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

 theorem affine_central_cut {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
     (b u : Fin m → ℝ) (B q : ℝ) (hq : 0 < q) (c z : Fin n → ℝ)
     (hz : u ⬝ᵥ (A *ᵥ z+b) ≤ B) (hc : B < u ⬝ᵥ (A *ᵥ (q • c)+b)) :
     (u ᵥ* A) ⬝ᵥ (q⁻¹ • z-c) < 0 := by
   have h1 : (u ᵥ* A) ⬝ᵥ z+u ⬝ᵥ b ≤ B := by
     simpa only [dotProduct_add,dotProduct_mulVec] using hz
   have h2 : B < q*((u ᵥ* A) ⬝ᵥ c)+u ⬝ᵥ b := by
     simpa only [dotProduct_add,dotProduct_mulVec,dotProduct_smul,smul_eq_mul] using hc
   have h3 : (u ᵥ* A) ⬝ᵥ z < q*((u ᵥ* A) ⬝ᵥ c) := by linarith
   have hdiv : ((u ᵥ* A) ⬝ᵥ z)/q < (u ᵥ* A) ⬝ᵥ c := (div_lt_iff₀ hq).mpr (by simpa only [mul_comm] using h3)
   rw [dotProduct_sub,dotProduct_smul,smul_eq_mul,mul_comm,←div_eq_mul_inv]
   linarith
 
 

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

 
 theorem halfspace_eval_cast {N : ℕ} (cut : RationalHalfspace N) (y : Fin N → ℚ) :
     (cut.eval y:ℝ)=cut.evalReal (fun i => (y i:ℝ)) := by
   simp [RationalHalfspace.eval,RationalHalfspace.evalReal]
 
 theorem binary_vertex_mem {n : ℕ} (V : Finset (Fin n → Bool)) (v : Fin n → Bool) (hv : v∈V) :
     (fun i => if v i then (1:ℝ) else 0)∈binaryHull V := subset_convexHull ℝ _ ⟨v,hv,fun _ => rfl⟩
 
 theorem affine_query_cast {N n : ℕ} (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ)
     (c : Fin n → ℚ) :
     (fun i => ((A *ᵥ ((n+1:ℚ) • c)+b) i:ℝ))=
       affineLift A b ((n+1:ℝ) • realVector c) := by
   rw [affineLift_rational]
   congr 1
   ext i
   simp [realVector,Pi.smul_apply,smul_eq_mul]

 theorem model_cut_central {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig st A b V) (cut : RationalHalfspace N) (c : Fin n → ℚ)
     (hc : StrictOracleCut Orig cut (A *ᵥ ((n+1:ℚ) • c)+b)) :
     ∀ v∈V,(fun i => ((cut.normal ᵥ* A) i:ℝ)) ⬝ᵥ
       ((fun i => (if v i then 1 else 0)/(n+1:ℝ))-realVector c) < 0 := by
   intro v hv
   let z : Fin n → ℝ := fun i => if v i then 1 else 0
   have hvOrig := h.lifts z (binary_vertex_mem V v hv)
   have hvalid : (fun i => (cut.normal i:ℝ)) ⬝ᵥ affineLift A b z ≤ (cut.bound:ℝ) := hc.2 _ hvOrig
   have hstrict : (cut.bound:ℝ) < (fun i => (cut.normal i:ℝ)) ⬝ᵥ
       affineLift A b ((n+1:ℝ) • realVector c) := by
     have hh : (cut.bound:ℝ) < (cut.eval (A *ᵥ ((n+1:ℚ) • c)+b):ℝ) := by exact_mod_cast hc.1
     rw [halfspace_eval_cast,affine_query_cast] at hh
     exact hh
   have hh := affine_central_cut (A.map (Rat.castHom ℝ)) (fun i => (b i:ℝ))
     (fun i => (cut.normal i:ℝ)) (cut.bound:ℝ) (n+1:ℝ) (by positivity) (realVector c) z hvalid hstrict
   have hnormal : ((fun i => (cut.normal i:ℝ)) ᵥ* A.map (Rat.castHom ℝ))=
       (fun i => ((cut.normal ᵥ* A) i:ℝ)) := by
     ext i
     simp [vecMul,dotProduct]
   have hz : (n+1:ℝ)⁻¹ • z=(fun i => (if v i then 1 else 0)/(n+1:ℝ)) := by
     ext i
     simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,z,mul_comm]
   rwa [hnormal,hz] at hh

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

 theorem represents_rational_unique {n : ℕ} (xs : SignedVector) (a b : Fin n → ℚ)
     (ha : RepresentsVector xs (rationalVector a)) (hb : RepresentsVector xs (rationalVector b)) : a=b := by
   have hh := represents_unique ha hb
   funext i
   apply Rat.cast_injective (α:=ℝ)
   exact congrArg (fun v : Vec n => v i) hh
 theorem model_cleared_central {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig st A b V) (cut : RationalHalfspace N) (c : Fin n → ℚ)
     (hc : StrictOracleCut Orig cut (A *ᵥ ((n+1:ℚ) • c)+b))
     (p : Fin n → ℤ) (T : ℝ) (hT : 0 < T)
     (hp : ∀ i,(p i:ℝ)=T*((cut.normal ᵥ* A) i:ℝ)) :
     ∀ v∈V,realVector (fun i => (p i:ℚ)) ⬝ᵥ
       ((fun i => (if v i then 1 else 0)/(n+1:ℝ))-realVector c) < 0 := by
   have he : realVector (fun i => (p i:ℚ))=T • (fun i => ((cut.normal ᵥ* A) i:ℝ)) := by
     ext i
     simpa only [realVector,Rat.cast_intCast,Pi.smul_apply,smul_eq_mul] using hp i
   intro v hv
   rw [he,smul_dotProduct,smul_eq_mul]
   exact mul_neg_of_pos_of_neg hT (model_cut_central Orig st A b V h cut c hc v hv)
 

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

 theorem phaseGeometry_center {n : ℕ} (V : Finset (Fin n → Bool)) (st : EllipsoidPhaseState)
     (h : PhaseGeometry V st) : ∃ c : Fin n → ℚ,RepresentsVector st.2.2 (rationalVector c) := by
   cases h with
   | small hn hs => exact ⟨_,hs.2.2.2.1⟩
   | large hn vs a k hv ha hst hk hcuts =>
     refine ⟨centers n a 0 k,?_⟩
     rw [hst]
     exact (ellipsoidPrefix_correct hn vs a hv ha k).2.2.1
 
 theorem findNonzero_true_iff {n : ℕ} (ps : SignedVector) (p : Fin n → ℚ)
     (hps : RepresentsVector ps (rationalVector p)) : (findNonzero ps).1=true ↔ p≠0 := by
   constructor
   · intro hflag hp
     have he : nonzeroIndices ps=[] := by
       apply List.eq_nil_iff_forall_not_mem.mpr
       intro i hi
       obtain ⟨j,hj,hpj⟩ := (nonzeroIndices_mem ps p hps i).mp hi
       apply hpj
       rw [hp,Pi.zero_apply]
     simp only [findNonzero,he,List.isEmpty_nil,Bool.not_true] at hflag
     contradiction
   · intro hp
     exact (findNonzero_correct ps p hps hp).1
 theorem integer_rationalVector {n : ℕ} (p : Fin n → ℤ) :
     rationalVector (fun i => (p i:ℚ))=WithLp.toLp 2 (fun i => (p i:ℝ)) := by
   ext i
   simp only [rationalVector,WithLp.ofLp_toLp,Rat.cast_intCast]
 theorem integer_cast_vector_ne_zero {n : ℕ} (p : Fin n → ℤ) :
     (fun i => (p i:ℚ))≠(0:Fin n → ℚ) ↔ p≠0 := by
   constructor
   · intro hq hp
     apply hq
     rw [hp]
     ext i; simp
   · intro hp hq
     apply hp
     ext i
     have hh := congrFun hq i
     change (p i:ℚ)=0 at hh
     exact_mod_cast hh

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

 
 theorem rationalWords_rep {n : ℕ} (a : Fin n → ℚ) : RepresentsVector (rationalWords a) (rationalVector a) := by
   refine ⟨fun i => codeWords (rationalCode (a i)),rfl,?_,?_⟩
   · intro i
     change 0 < value (natBits (a i).den)
     rw [value_natBits]
     exact (a i).den_pos
   · intro i
     rw [signedFractionValue_code,rationalCode_value]
     rfl

 

 

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

 theorem serializeRationalVector_rep {n : ℕ} (xs : SignedVector) (a : Fin n → ℚ)
     (hx : RepresentsVector xs (rationalVector a)) : serializeRow xs=vectorBits a := by
   obtain ⟨words,rfl,hD,hv⟩ := hx
   have hval (i : Fin n) : signedFractionValue (words i)=a i := Rat.cast_injective (α:=ℝ) (hv i)
   simp only [serializeRow,List.flatMap_def,List.map_ofFn,vectorBits]
   congr 1
   congr 1
   funext i
   have hh := rationalBits_correct (words i).1 (words i).2.1 (words i).2.2 (hD i)
   change rationalBits (words i)=encodeRat (signedFractionValue (words i)) at hh
   simpa only [Function.comp_apply,hval i] using hh
 theorem rationalVectorCode_bits {n : ℕ} (a : Fin n → ℚ) :
     (List.ofFn (fun i => rationalCode (a i))).flatMap RationalCode.bits=vectorBits a := by
   simp only [List.flatMap_def,List.map_ofFn,Function.comp_def,rationalCode_bits,vectorBits]
 theorem readMany_vectorBits {n : ℕ} (a : Fin n → ℚ) :
     readMany n (vectorBits a)=(rationalWords a,[]) := by
   have hh := readMany_codes (List.ofFn (fun i => rationalCode (a i))) []
   simpa only [List.length_ofFn,rationalVectorCode_bits,List.append_nil,List.map_ofFn,rationalWords,Function.comp_def] using hh
 theorem vectorBits_injective {n : ℕ} (a b : Fin n → ℚ) (h : vectorBits a=vectorBits b) : a=b := by
   have hh := congrArg (readMany n) h
   rw [readMany_vectorBits,readMany_vectorBits] at hh
   have hwords := List.ofFn_inj.mp (congrArg Prod.fst hh)
   funext i
   have he := congrArg signedFractionValue (congrFun hwords i)
   simpa only [signedFractionValue_code,rationalCode_value] using he
 theorem oracleOutput_query {N n : ℕ} (st : OracleState) (hs : st.1=false)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (c : Fin n → ℚ)
     (hA : RepresentsRectMatrix st.2.1.1 A) (hb : RepresentsVector st.2.1.2 (rationalVector b))
     (hc : RepresentsVector st.2.2.2.2 (rationalVector c)) (hdim : st.2.2.1.1=n) :
     oracleOutput st=true::vectorBits (A *ᵥ ((n+1:ℚ) • c)+b) := by
   have hquery := oracleCoreQuery_correct st.2 A b c hA hb hc hdim
   simp only [oracleOutput,hs,Bool.false_eq_true,if_false,oracleQueryOutput,serializeRationalVector_rep _ _ hquery]
 theorem oracleOutput_rejected (st : OracleState) (hs : st.1=true) : oracleOutput st=[false] := by
   simp only [oracleOutput,hs,if_true]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ProgramOutputUnique
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main

 theorem option_bind_iterate_none {σ : Type} (f : σ → Option σ) (k : ℕ) :
     (fun x : Option σ => x.bind f)^[k] none=none := by
   induction k with
   | zero => rfl
   | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl
 theorem terminal_output_ordered {σ : Type} (f : σ → Option σ) (a b c : σ) (n m : ℕ)
     (hnm : n ≤ m) (hb : f b=none)
     (h1 : (fun x : Option σ => x.bind f)^[n] (some a)=some b)
     (h2 : (fun x : Option σ => x.bind f)^[m] (some a)=some c) : b=c := by
   obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hnm
   rw [Nat.add_comm,Function.iterate_add_apply,h1] at h2
   cases d with
   | zero => exact Option.some.inj h2
   | succ d =>
     have he : (fun x : Option σ => x.bind f)^[d+1] (some b)=none := by
       rw [Function.iterate_succ_apply]
       simp only [Option.bind_some,hb]
       exact option_bind_iterate_none f d
     rw [he] at h2
     cases h2
 theorem terminal_output_unique {σ : Type} (f : σ → Option σ) (a b c : σ) (n m : ℕ)
     (hb : f b=none) (hc : f c=none)
     (h1 : (fun x : Option σ => x.bind f)^[n] (some a)=some b)
     (h2 : (fun x : Option σ => x.bind f)^[m] (some a)=some c) : b=c := by
   rcases Nat.le_total n m with h | h
   · exact terminal_output_ordered f a b c n m h hb h1 h2
   · exact (terminal_output_ordered f a c b m n h hc h2 h1).symm
 theorem runs_output_unique (P : Program) (input out1 out2 : List Bool) {s t : ℕ}
     (h1 : Runs P input out1 s) (h2 : Runs P input out2 t) : out1=out2 := by
   obtain ⟨r1⟩ := h1
   obtain ⟨r2⟩ := h2
   have hh := terminal_output_unique P.machine.tm.step
     (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm))
     (Turing.haltList P.machine.tm (out1.map P.machine.outputAlphabet.symm))
     (Turing.haltList P.machine.tm (out2.map P.machine.outputAlphabet.symm)) r1.steps r2.steps
     (by rfl) (by rfl) r1.evals_in_steps r2.evals_in_steps
   have he := congrArg (fun c => c.stk P.machine.tm.k₁) hh
   simp only [Turing.haltList,dif_pos rfl] at he
   exact (List.map_injective_iff.mpr P.machine.outputAlphabet.symm.injective) he
 theorem evaluates_output_unique (P : Program) (input out1 out2 : List Bool)
     (h1 : Evaluates P input out1) (h2 : Evaluates P input out2) : out1=out2 := by
   obtain ⟨s,hs⟩ := h1
   obtain ⟨t,ht⟩ := h2
   exact runs_output_unique P input out1 out2 hs ht

end EdgeSublinearMWIS.Main
end

-- Solutions.OracleTranscriptState
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 
 
 
 theorem binaryOracle_transcript (bound : Polynomial ℕ) (N : ℕ) (cuts : List (RationalHalfspace N)) :
     binaryOracle (ellipsoidWord bound N cuts)=oracleOutput (oracleTranscriptState cuts) := by
   simp only [binaryOracle,Function.comp_apply,parseOracleTranscript_correct,oracleTranscriptState,rationalWords]
 theorem transcript_counter_live {N : ℕ} (cuts : List (RationalHalfspace N))
     (h : (oracleTranscriptState cuts).1=false) : CounterGood N (oracleTranscriptState cuts).2 := by
   have hh := foldCut_counter (cuts.map (fun cut => rationalWords cut.normal)) (oracleInitial N) (counter_good_initial N)
   rcases hh with hr | ⟨hg,hb⟩
   · change (oracleTranscriptState cuts).1=true at hr
     rw [h] at hr
     contradiction
   · exact hg

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

 
 theorem dialogue_query_is_native {N n : ℕ} (E : Program) (hE : ImplementsBinaryOracle E)
     (bound : Polynomial ℕ) (Orig : Finset (Fin N → Bool))
     (qs : List (Fin N → ℚ)) (cuts : List (RationalHalfspace N))
     (hadm : AdmissibleDialogue E bound N Orig qs cuts) (i : ℕ) (hi : i < cuts.length)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig (oracleTranscriptState (cuts.take i)).2 A b V)
     (hs : (oracleTranscriptState (cuts.take i)).1=false) (c0 : Fin n → ℚ)
     (hc0 : RepresentsVector (oracleTranscriptState (cuts.take i)).2.2.2.2 (rationalVector c0)) :
     StrictOracleCut Orig cuts[i] (A *ᵥ ((n+1:ℚ) • c0)+b) := by
   obtain ⟨y,hy,hEval,hviol,hvalid,hbits⟩ := hadm.2 i hi
   have hd := phaseGeometry_dimension V _ h.phase
   have hactual := hE (ellipsoidWord bound N (cuts.take i))
   rw [binaryOracle_transcript,oracleOutput_query _ hs A b c0 h.affineRows h.affineOffsets hc0 hd] at hactual
   have hout := evaluates_output_unique E _ _ _ hactual hEval
   have hvec := List.cons.inj hout
   have he := vectorBits_injective _ _ hvec.2
   exact ⟨by rwa [he],hvalid⟩

 
 

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

 theorem signedFractionValue_height (s : SignedWords) (hd : 0 < value s.2.2) :
     (signedFractionValue s).num.natAbs ≤ 2^volume s ∧ (signedFractionValue s).den ≤ 2^volume s := by
   have hD : (value s.2.2:ℤ)≠0 := by exact_mod_cast ne_of_gt hd
   have hh := GLS.DeterminantBounds.integer_ratio_num_den_bound (signedValue s.1 s.2.1) (value s.2.2:ℤ) hD
   have he : (signedValue s.1 s.2.1).natAbs=value s.2.1 := by
     cases hb : s.1 <;> simp [signedValue,hb]
   have hw := signedWidth_volume s
   have hNlen : s.2.1.length ≤ volume s := by dsimp [fractionWidth] at hw; omega
   have hDlen : s.2.2.length ≤ volume s := by dsimp [fractionWidth] at hw; omega
   have hN := (value_lt s.2.1).le.trans (Nat.pow_le_pow_right (by omega) hNlen)
   have hDD := (value_lt s.2.2).le.trans (Nat.pow_le_pow_right (by omega) hDlen)
   have hnum : (signedFractionValue s).num.natAbs ≤ value s.2.1 := by
     simpa only [signedFractionValue,Int.cast_natCast,he] using hh.1
   have hden : (signedFractionValue s).den ≤ value s.2.2 := by
     simpa only [signedFractionValue,Int.cast_natCast,Int.natAbs_natCast] using hh.2
   exact ⟨hnum.trans hN,hden.trans hDD⟩
 theorem represented_vector_height {n : ℕ} (xs : SignedVector) (a : Fin n → ℚ)
     (h : RepresentsVector xs (rationalVector a)) :
     ∀ i,(a i).num.natAbs ≤ 2^volume xs ∧ (a i).den ≤ 2^volume xs := by
   obtain ⟨words,rfl,hD,hv⟩ := h
   intro i
   have he : signedFractionValue (words i)=a i := Rat.cast_injective (α:=ℝ) (hv i)
   have hh := signedFractionValue_height (words i) (hD i)
   rw [he] at hh
   have hvol : volume (words i) ≤ volume (List.ofFn words) := volume_mem_le (List.mem_ofFn.mpr ⟨i,rfl⟩)
   have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ (2:ℕ)) hvol
   exact ⟨hh.1.trans hpow,hh.2.trans hpow⟩
 theorem represented_matrix_height {n : ℕ} (bs : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ)
     (h : RepresentsMatrix bs A) :
     ∀ i j,(A i j).num.natAbs ≤ 2^volume bs ∧ (A i j).den ≤ 2^volume bs := by
   obtain ⟨rows,rfl,hrows⟩ := h
   intro i j
   have hh := represented_vector_height (rows i) (A i) (hrows i) j
   have hvol : volume (rows i) ≤ volume (List.ofFn rows) := volume_mem_le (List.mem_ofFn.mpr ⟨i,rfl⟩)
   have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ (2:ℕ)) hvol
   exact ⟨hh.1.trans hpow,hh.2.trans hpow⟩

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

 
 theorem matrixInverseWords_valid_polynomial :
     ∃ C q : ℕ,0 < C ∧ ∀ bs : SignedMatrix,ValidPositiveMatrix bs →
       matrixInverseWordsRealizer.time bs ≤ C*(volume bs+1)^q ∧
       volume (matrixInverseWords bs) ≤ C*(volume bs+1)^q := by
   obtain ⟨C,q,hC,hclock⟩ := matrixInverseWords_polynomial_time
   refine ⟨C*4^q,q,by positivity,?_⟩
   intro bs h
   obtain ⟨n,A,hA,hp⟩ := h
   have hs := represented_matrix_height bs A hA
   have hn : bs.length=n := by obtain ⟨rows,rfl,hr⟩ := hA; simp
   have hlen := length_volume bs
   rw [hn] at hlen
   have hbase : volume bs+n+volume bs+4 ≤ 4*(volume bs+1) := by omega
   have hh := hclock n (volume bs) bs A hA hp hs
   have ht := hh.1.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
   have hv := hh.2.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
   simpa only [mul_pow,Nat.mul_assoc] using And.intro ht hv

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

 
 theorem hyperplaneApproximation_polynomial_time :
     ∃ C e : ℕ,0 < C ∧ ∀ s : HyperplaneApproximationInput,ValidHyperplaneInput s →
       hyperplaneApproximationRealizer.time s ≤ C*(volume s+1)^e ∧
       volume (hyperplaneApproximation s) ≤ C*(volume s+1)^e := by
   have hpre := polynomial_restrict hyperplaneApproximationDataRealizer ValidHyperplaneInput hyperplaneApproximationData_polynomial
   obtain ⟨D,q,hD,hApprox⟩ := canonicalApproximation_polynomial_time
   have hpost : ∃ D q : ℕ,0 < D ∧ ∀ s : HyperplaneApproximationInput,ValidHyperplaneInput s →
       canonicalApproximationRealizer.time (hyperplaneApproximationData s) ≤ D*(volume (hyperplaneApproximationData s)+1)^q ∧
       volume (canonicalApproximation (hyperplaneApproximationData s)) ≤ D*(volume (hyperplaneApproximationData s)+1)^q := by
     refine ⟨D,q,hD,?_⟩
     intro s hs
     obtain ⟨u,c,hu,hc⟩ := hs
     apply hApprox
     exact ⟨s.1+1,Fin.snoc u ((s.1+1:ℚ)*(u ⬝ᵥ c)),hyperplaneCoordinates_correct s.2.1 s.2.2 u c hu hc⟩
   exact polynomial_comp_restricted hyperplaneApproximationDataRealizer canonicalApproximationRealizer ValidHyperplaneInput hpre hpost

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

 
 theorem restricted_comp {f : α → β} {g : β → γ} (R : Realizer f) (S : Realizer g)
     (P : α → Prop) (Q : β → Prop) (hR : RestrictedPoly R P) (hS : RestrictedPoly S Q)
     (hf : ∀ x,P x → Q (f x)) : RestrictedPoly (R.comp S) P := by
   obtain ⟨D,q,hD,hS⟩ := hS
   exact polynomial_comp_restricted R S P hR ⟨D,q,hD,fun x hx => hS (f x) (hf x hx)⟩
 theorem restricted_comp_global {f : α → β} {g : β → γ} (R : Realizer f) (S : Realizer g)
     (P : α → Prop) (hR : RestrictedPoly R P) (hS : PolyBound S) : RestrictedPoly (R.comp S) P := by
   obtain ⟨D,q,hD,hS⟩ := hS
   exact polynomial_comp_restricted R S P hR ⟨D,q,hD,fun x _ => hS (f x)⟩
 theorem restricted_pre_global {f : α → β} {g : β → γ} (R : Realizer f) (S : Realizer g)
     (P : α → Prop) (Q : β → Prop) (hR : PolyBound R) (hS : RestrictedPoly S Q)
     (hf : ∀ x,P x → Q (f x)) : RestrictedPoly (R.comp S) P :=
   restricted_comp R S P Q (polynomial_restrict R P hR) hS hf
 

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

 theorem ellipsoidThinDirection_valid_clock : RestrictedPoly ellipsoidThinDirectionRealizer ValidPositiveMatrix :=
   restricted_comp_global matrixInverseWordsRealizer inverseThinDirectionRealizer ValidPositiveMatrix
     matrixInverseWords_valid_polynomial inverseThinDirection_polynomial
 
 theorem ellipsoidRecoveryDirection_clock : RestrictedPoly ellipsoidRecoveryDirectionRealizer ValidRecoveryInput := by
   let shape : Realizer (fun s : EllipsoidRecoveryInput => s.2.1) := Realizer.snd.comp Realizer.fst
   have hshape : PolyBound shape := linear_polynomial (linear_comp linear_snd linear_fst)
   have hpre := restricted_pre_global shape ellipsoidThinDirectionRealizer ValidRecoveryInput ValidPositiveMatrix hshape
     ellipsoidThinDirection_valid_clock (by
       intro s hs
       obtain ⟨hn,A,c,hA,hc,hp⟩ := hs
       exact ⟨s.1,A,hA,hp⟩)
   have hlast := restricted_comp_global (shape.comp ellipsoidThinDirectionRealizer) Realizer.fst ValidRecoveryInput hpre (linear_polynomial linear_fst)
   exact hlast
 theorem ellipsoidRecoveryData_clock : RestrictedPoly ellipsoidRecoveryDataRealizer ValidRecoveryInput := by
   have hcenter := polynomial_restrict (Realizer.snd.comp Realizer.snd : Realizer (fun s : EllipsoidRecoveryInput => s.2.2))
     ValidRecoveryInput (linear_polynomial (linear_comp linear_snd linear_snd))
   have hpair := polynomial_pair_restricted (R:=ellipsoidRecoveryDirectionRealizer) (S:=Realizer.snd.comp Realizer.snd)
     ValidRecoveryInput ellipsoidRecoveryDirection_clock hcenter
   have hdim := polynomial_restrict (Realizer.fst : Realizer (fun s : EllipsoidRecoveryInput => s.1))
     ValidRecoveryInput (linear_polynomial linear_fst)
   exact polynomial_pair_restricted (R:=Realizer.fst) (S:=ellipsoidRecoveryDirectionRealizer.pair (Realizer.snd.comp Realizer.snd))
     ValidRecoveryInput hdim hpair
 theorem ellipsoidRecovery_valid_clock : RestrictedPoly ellipsoidRecoveryRealizer ValidRecoveryInput := by
   have hValid : ∀ s,ValidRecoveryInput s → ValidHyperplaneInput (ellipsoidRecoveryData s) := by
     intro s hs
     obtain ⟨hn,A,c,hA,hc,hp⟩ := hs
     obtain ⟨k,hu,hU⟩ := ellipsoidThinDirection_rational hn s.2.1 A hA hp
     exact ⟨(fun i => A⁻¹ i k/A⁻¹ k k),c,hu,hc⟩
   exact restricted_comp ellipsoidRecoveryDataRealizer hyperplaneApproximationRealizer
     ValidRecoveryInput ValidHyperplaneInput ellipsoidRecoveryData_clock hyperplaneApproximation_polynomial_time hValid

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

 
 
 theorem phaseRecoveredCoefficients_clock : RestrictedPoly phaseRecoveredCoefficientsRealizer ValidReductionPhase := by
   have hpre := restricted_pre_global phaseRecoveryInputRealizer ellipsoidRecoveryRealizer ValidReductionPhase ValidRecoveryInput
     phaseRecoveryInput_polynomial ellipsoidRecovery_valid_clock (fun s hs => hs)
   exact restricted_comp_global (phaseRecoveryInputRealizer.comp ellipsoidRecoveryRealizer) Realizer.fst
     ValidReductionPhase hpre (linear_polynomial linear_fst)
 theorem phaseNormalAndOffset_clock : RestrictedPoly phaseNormalAndOffsetRealizer ValidReductionPhase := by
   have hdim := polynomial_restrict (Realizer.fst.comp Realizer.fst : Realizer (fun st : EllipsoidPhaseState => st.1.1))
     ValidReductionPhase (linear_polynomial (linear_comp linear_fst linear_fst))
   have hpair := polynomial_pair_restricted (R:=Realizer.fst.comp Realizer.fst) (S:=phaseRecoveredCoefficientsRealizer)
     ValidReductionPhase hdim phaseRecoveredCoefficients_clock
   exact restricted_comp_global ((Realizer.fst.comp Realizer.fst).pair phaseRecoveredCoefficientsRealizer) phaseSplitCoefficientsRealizer
     ValidReductionPhase hpair phaseSplitCoefficients_polynomial
 theorem phaseEliminationParameters_clock : RestrictedPoly phaseEliminationParametersRealizer ValidReductionPhase :=
   restricted_comp_global phaseNormalAndOffsetRealizer eliminationParametersRealizer ValidReductionPhase
     phaseNormalAndOffset_clock eliminationParameters_polynomial
 theorem oracleDimensionReduction_clock : RestrictedPoly oracleDimensionReductionRealizer ValidReductionCore := by
   have hparams := restricted_pre_global Realizer.snd phaseEliminationParametersRealizer ValidReductionCore ValidReductionPhase
     (linear_polynomial linear_snd) phaseEliminationParameters_clock (fun s hs => hs)
   have haff := polynomial_restrict (Realizer.fst : Realizer (fun st : OracleCoreState => st.1))
     ValidReductionCore (linear_polynomial linear_fst)
   have hpair := polynomial_pair_restricted (R:=Realizer.fst) (S:=Realizer.snd.comp phaseEliminationParametersRealizer)
     ValidReductionCore haff hparams
   have hleft := restricted_comp_global (Realizer.fst.pair (Realizer.snd.comp phaseEliminationParametersRealizer))
     canonicalAffineEliminateRealizer ValidReductionCore hpair canonicalAffineEliminate_polynomial
   have hright : PolyBound ((((Realizer.snd.comp Realizer.fst).comp Realizer.fst).comp Realizer.pred).comp phaseInitialRealizer :
       Realizer (fun st : OracleCoreState => phaseInitial (st.2.1.1-1))) := polynomial_comp
     (linear_polynomial (linear_comp (linear_comp (linear_comp linear_snd linear_fst) linear_fst) natPred_linear)) phaseInitial_polynomial
   have hright' := polynomial_restrict _ ValidReductionCore hright
   exact polynomial_pair_restricted (R:=(Realizer.fst.pair (Realizer.snd.comp phaseEliminationParametersRealizer)).comp canonicalAffineEliminateRealizer)
     (S:=(((Realizer.snd.comp Realizer.fst).comp Realizer.fst).comp Realizer.pred).comp phaseInitialRealizer)
     ValidReductionCore hleft hright'

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

 theorem restricted_selectiveChoose {f g : α → β} (R : Realizer f) (S : Realizer g)
     (P : Bool×α → Prop)
     (hR : RestrictedPoly (Realizer.snd.comp R) (fun x => P x ∧ x.1=true))
     (hS : RestrictedPoly (Realizer.snd.comp S) (fun x => P x ∧ x.1=false)) :
     RestrictedPoly (R.selectiveChoose S) P := by
   obtain ⟨C,q,hC,hR⟩ := hR
   obtain ⟨D,r,hD,hS⟩ := hS
   refine ⟨100*(C+D+1),q+r+1,by positivity,?_⟩
   intro x hx
   let z := volume x+1
   let e := q+r+1
   have hz : 1 ≤ z := by dsimp [z]; omega
   have hq : z^q ≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hr : z^r ≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hze : z ≤ z^e := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by dsimp [e]; omega : 1 ≤ e)
   have hchosen :
       (if x.1 then (Realizer.snd.comp R).time x else (Realizer.snd.comp S).time x) ≤ (C+D)*z^e ∧
       volume (if x.1 then f x.2 else g x.2) ≤ (C+D)*z^e := by
     cases hb : x.1 with
     | false =>
       have hh := hS x ⟨hx,hb⟩
       have ht := hh.1.trans (Nat.mul_le_mul_left D hr)
       have hv := hh.2.trans (Nat.mul_le_mul_left D hr)
       simp only [Function.comp_apply] at hv
       simp only [hb,Bool.false_eq_true,if_false]
       constructor <;> nlinarith
     | true =>
       have hh := hR x ⟨hx,hb⟩
       have ht := hh.1.trans (Nat.mul_le_mul_left C hq)
       have hv := hh.2.trans (Nat.mul_le_mul_left C hq)
       simp only [Function.comp_apply] at hv
       simp only [hb,if_true]
       constructor <;> nlinarith
   constructor
   · rw [Realizer.time_selectiveChoose]
     change _ ≤ 100*(C+D+1)*z^e
     have hv : volume x+1 ≤ z^e := hze
     nlinarith only [hchosen.1,hchosen.2,hv]
   · change volume (if x.1 then f x.2 else g x.2) ≤ 100*(C+D+1)*z^e
     exact hchosen.2.trans (Nat.mul_le_mul_right _ (by omega))

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.SelectiveChoosePolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.ThreeMachine.StackCompiler.Realizer
variable {α β : Type} [Coding α] [Coding β]
 theorem selectiveChoose_time_le {f g : α → β} (R : Realizer f) (S : Realizer g) (x : Bool×α) :
     (R.selectiveChoose S).time x ≤ (R.choose S).time x := by
   rw [time_selectiveChoose,time_choose]
   rcases x with ⟨b,x⟩
   cases b <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
end OAI.ThreeMachine.StackCompiler.Realizer
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]
 theorem polynomial_selectiveChoose {f g : α → β} {R : Realizer f} {S : Realizer g}
     (hR : PolyBound R) (hS : PolyBound S) : PolyBound (R.selectiveChoose S) := by
   obtain ⟨C,q,hC,hChoose⟩ := polynomial_choose hR hS
   refine ⟨C,q,hC,?_⟩
   intro x
   exact ⟨(Realizer.selectiveChoose_time_le R S x).trans (hChoose x).1,(hChoose x).2⟩

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

 
 theorem oracleBoundary_clock : RestrictedPoly oracleBoundaryRealizer BoundarySafe := by
   let P : Bool×OracleCoreState → Prop := fun x => x.1=true → ValidReductionCore x.2
   have hleft := restricted_pre_global Realizer.snd oracleDimensionReductionRealizer (fun x => P x ∧ x.1=true) ValidReductionCore
     (linear_polynomial linear_snd) oracleDimensionReduction_clock (fun x hx => hx.1 hx.2)
   have hright := polynomial_restrict (Realizer.snd.comp (Realizer.id : Realizer (id : OracleCoreState → OracleCoreState)))
     (fun x : Bool×OracleCoreState => P x ∧ x.1=false) (linear_polynomial (linear_comp linear_snd linear_id))
   have hchoose := restricted_selectiveChoose oracleDimensionReductionRealizer Realizer.id P hleft hright
   exact restricted_pre_global (oracleAtBoundaryRealizer.pair Realizer.id) (oracleDimensionReductionRealizer.selectiveChoose Realizer.id)
     BoundarySafe P (polynomial_pair oracleAtBoundary_polynomial (linear_polynomial linear_id)) hchoose (fun s hs => hs)
 
 theorem oracleBigCut_clock : RestrictedPoly oracleBigCutRealizer BigCutSafe := by
   have hfalse := polynomial_restrict (Realizer.constant Bool.false : Realizer (fun _ : OracleCoreState => Bool.false))
     BoundarySafe (linear_polynomial (linear_constant Bool.false))
   have hpost := polynomial_pair_restricted (R:=Realizer.constant Bool.false) (S:=oracleBoundaryRealizer) BoundarySafe hfalse oracleBoundary_clock
   exact restricted_pre_global oraclePhaseAdvanceRealizer ((Realizer.constant Bool.false).pair oracleBoundaryRealizer)
     BigCutSafe BoundarySafe oraclePhaseAdvance_polynomial hpost (fun s hs => hs)
 theorem oracleSmallAdvance_polynomial : PolyBound oracleSmallAdvanceRealizer := polynomial_pair
   (linear_polynomial (linear_constant Bool.false))
   (polynomial_pair (linear_polynomial (linear_comp linear_snd linear_fst))
     (polynomial_pair (linear_polynomial (linear_pair oracleSmallDimension_linear (linear_constant (1:ℕ))))
       (polynomial_pair (linear_polynomial (linear_comp (linear_comp (linear_comp linear_snd linear_snd) linear_snd) linear_fst))
         (polynomial_comp (linear_polynomial (linear_pair oracleSmallDimension_linear (linear_constant scalarHalf))) replicateList_polynomial))))
 theorem oracleReject_polynomial : PolyBound oracleRejectRealizer := linear_polynomial (linear_pair (linear_constant Bool.true) linear_snd)
 theorem oracleSmallFirst_polynomial : PolyBound oracleSmallFirstRealizer := polynomial_comp
   (linear_polynomial (linear_pair (linear_comp (linear_comp (linear_comp linear_snd linear_snd) linear_fst) linear_snd)
     (linear_constant (0:ℕ)))) eqNat_polynomial
 theorem oracleSmallCut_polynomial : PolyBound oracleSmallCutRealizer := polynomial_comp
   (polynomial_pair oracleSmallFirst_polynomial (linear_polynomial linear_id))
   (polynomial_selectiveChoose oracleSmallAdvance_polynomial oracleReject_polynomial)
 theorem oracleSmall_polynomial : PolyBound oracleSmallRealizer := polynomial_comp
   (linear_polynomial (linear_pair oracleSmallDimension_linear (linear_constant (1:ℕ)))) nat_le_polynomial
 theorem oraclePreparedNonzero_polynomial : PolyBound oraclePreparedNonzeroRealizer := polynomial_comp
   (polynomial_comp (linear_polynomial linear_fst) findNonzero_polynomial) (linear_polynomial linear_fst)
 
 theorem oracleNonzeroCut_clock : RestrictedPoly oracleNonzeroCutRealizer NonzeroCutSafe := by
   let P : Bool×OraclePreparedCut → Prop := fun x => x.1=false → BigCutSafe x.2
   have hleft := polynomial_restrict (Realizer.snd.comp oracleSmallCutRealizer)
     (fun x : Bool×OraclePreparedCut => P x ∧ x.1=true)
     (polynomial_comp (linear_polynomial linear_snd) oracleSmallCut_polynomial)
   have hright := restricted_pre_global Realizer.snd oracleBigCutRealizer (fun x => P x ∧ x.1=false) BigCutSafe
     (linear_polynomial linear_snd) oracleBigCut_clock (fun x hx => hx.1 hx.2)
   have hchoose := restricted_selectiveChoose oracleSmallCutRealizer oracleBigCutRealizer P hleft hright
   exact restricted_pre_global (oracleSmallRealizer.pair Realizer.id) (oracleSmallCutRealizer.selectiveChoose oracleBigCutRealizer)
     NonzeroCutSafe P (polynomial_pair oracleSmall_polynomial (linear_polynomial linear_id)) hchoose (fun s hs => hs)
 
 theorem oraclePreparedCut_clock : RestrictedPoly oraclePreparedCutRealizer PreparedSafe := by
   let P : Bool×OraclePreparedCut → Prop := fun x => x.1=true → NonzeroCutSafe x.2
   have hleft := restricted_pre_global Realizer.snd oracleNonzeroCutRealizer (fun x => P x ∧ x.1=true) NonzeroCutSafe
     (linear_polynomial linear_snd) oracleNonzeroCut_clock (fun x hx => hx.1 hx.2)
   have hright := polynomial_restrict (Realizer.snd.comp oracleRejectRealizer)
     (fun x : Bool×OraclePreparedCut => P x ∧ x.1=false)
     (polynomial_comp (linear_polynomial linear_snd) oracleReject_polynomial)
   have hchoose := restricted_selectiveChoose oracleNonzeroCutRealizer oracleRejectRealizer P hleft hright
   exact restricted_pre_global (oraclePreparedNonzeroRealizer.pair Realizer.id) (oracleNonzeroCutRealizer.selectiveChoose oracleRejectRealizer)
     PreparedSafe P (polynomial_pair oraclePreparedNonzero_polynomial (linear_polynomial linear_id)) hchoose (fun s hs => hs)
 
 theorem oracleActiveCut_clock : RestrictedPoly oracleActiveCutRealizer ActiveCutSafe := by
   have hpre : PolyBound ((Realizer.fst.pair (Realizer.snd.comp Realizer.snd)).comp oraclePrepareCutRealizer :
       Realizer (fun s : OracleCutInput => oraclePrepareCut (s.1,s.2.2))) := polynomial_comp
     (linear_polynomial (linear_pair linear_fst (linear_comp linear_snd linear_snd))) oraclePrepareCut_polynomial
   exact restricted_pre_global ((Realizer.fst.pair (Realizer.snd.comp Realizer.snd)).comp oraclePrepareCutRealizer) oraclePreparedCutRealizer
     ActiveCutSafe PreparedSafe hpre oraclePreparedCut_clock (fun s hs => hs)
 
 theorem oracleCut_clock : RestrictedPoly oracleCutRealizer OracleCutSafe := by
   let P : Bool×OracleCutInput → Prop := fun x => x.1=false → ActiveCutSafe x.2
   have hleft := polynomial_restrict (Realizer.snd.comp (Realizer.snd : Realizer (fun s : OracleCutInput => s.2)))
     (fun x : Bool×OracleCutInput => P x ∧ x.1=true) (linear_polynomial (linear_comp linear_snd linear_snd))
   have hright := restricted_pre_global Realizer.snd oracleActiveCutRealizer (fun x => P x ∧ x.1=false) ActiveCutSafe
     (linear_polynomial linear_snd) oracleActiveCut_clock (fun x hx => hx.1 hx.2)
   have hchoose := restricted_selectiveChoose Realizer.snd oracleActiveCutRealizer P hleft hright
   exact restricted_pre_global ((Realizer.snd.comp Realizer.fst).pair Realizer.id) (Realizer.snd.selectiveChoose oracleActiveCutRealizer)
     OracleCutSafe P (linear_polynomial (linear_pair (linear_comp linear_snd linear_fst) linear_id)) hchoose (fun s hs => hs)

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

 theorem phaseGeometry_recovery_valid {n : ℕ} (V : Finset (Fin n → Bool)) (st : EllipsoidPhaseState)
     (h : PhaseGeometry V st) (hn : 2 ≤ n) : ValidReductionPhase st := by
   cases h with
   | small hnsmall hs => omega
   | large hn vs a k hv ha hst hk hcuts =>
     have hs := ellipsoidPrefix_correct hn vs a hv ha k
     have hdata : phaseRecoveryInput st=(n,(ellipsoidPrefix n vs k).2) := by
       dsimp only [phaseRecoveryInput]
       rw [hst,hs.1]
     change ValidRecoveryInput (phaseRecoveryInput st)
     rw [hdata]
     refine ⟨by omega,shapes n a k,centers n a 0 k,hs.2.1,hs.2.2.1,?_⟩
     exact (shapes_invariant n hn a ha k).1
 theorem model_bigCut_safe {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig st A b V) (hn : 2 ≤ n) (hk : st.2.1.2 < phaseBudget n)
     (ps : SignedVector) (p : Fin n → ℤ)
     (hp : RepresentsVector ps (rationalVector (fun i => (p i:ℚ)))) (hne : p≠0)
     (hcut : ∀ c : Fin n → ℚ,RepresentsVector st.2.2.2 (rationalVector c) →
       ∀ v∈V,realVector (fun i => (p i:ℚ)) ⬝ᵥ
         ((fun i => (if v i then 1 else 0)/(n+1:ℝ))-realVector c) ≤ 0) : BigCutSafe (ps,st) := by
   have hm := coreModel_phase_advance Orig st A b V h hn hk ps p hp hne hcut
   intro hboundary
   exact phaseGeometry_recovery_valid V _ hm.phase hn
 theorem model_prepared_safe {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig st A b V) (hg : CounterGood N st)
     (cut : RationalHalfspace N) (c0 : Fin n → ℚ)
     (hc0 : RepresentsVector st.2.2.2 (rationalVector c0))
     (hc : StrictOracleCut Orig cut (A *ᵥ ((n+1:ℚ) • c0)+b))
     (ps : SignedVector) (p : Fin n → ℤ)
     (hp : RepresentsVector ps (rationalVector (fun i => (p i:ℚ))))
     (T : ℝ) (hT : 0 < T) (hscale : ∀ i,(p i:ℝ)=T*((cut.normal ᵥ* A) i:ℝ)) : PreparedSafe (ps,st) := by
   intro hflag hsmall
   have hdim := phaseGeometry_dimension V st.2 h.phase
   have hn : 2 ≤ n := by
     have hh : ¬n ≤ 1 := by simpa only [oracleSmall,hdim,decide_eq_false_iff_not] using hsmall
     omega
   have hpQ := (findNonzero_true_iff ps _ hp).mp hflag
   have hpInt := (integer_cast_vector_ne_zero p).mp hpQ
   have hk : st.2.1.2 < phaseBudget n := by simpa only [hdim] using hg.2.1
   apply model_bigCut_safe Orig st A b V h hn hk ps p hp hpInt
   intro c hcrep v hv
   have he := represents_rational_unique _ _ _ hcrep hc0
   rw [he]
   exact (model_cleared_central Orig st A b V h cut c0 hc p T hT hscale v hv).le
 theorem model_active_safe {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig st.2 A b V) (hg : CounterGood N st.2)
     (cut : RationalHalfspace N) (as : SignedVector)
     (has : RepresentsVector as (rationalVector cut.normal)) (c0 : Fin n → ℚ)
     (hc0 : RepresentsVector st.2.2.2.2 (rationalVector c0))
     (hc : StrictOracleCut Orig cut (A *ᵥ ((n+1:ℚ) • c0)+b)) : ActiveCutSafe (as,st) := by
   have hdim := phaseGeometry_dimension V st.2.2 h.phase
   obtain ⟨p,T,hT,hprep,hscale,hcore⟩ := oraclePrepareCut_correct as st.2 A cut.normal h.affineRows has hdim
   let ps := (oraclePrepareCut (as,st.2)).1
   have hp : RepresentsVector ps (rationalVector (fun i => (p i:ℚ))) := by rw [integer_rationalVector]; exact hprep
   have hs := model_prepared_safe Orig st.2 A b V h hg cut c0 hc0 hc ps p hp T hT hscale
   have he : oraclePrepareCut (as,st.2)=(ps,st.2) := Prod.ext rfl hcore
   change PreparedSafe (oraclePrepareCut (as,st.2))
   rwa [he]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleHeightBounds
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools GLS.EllipsoidStateSize

 
 theorem recoveryHeight_upper (N : ℕ) : recoveryHeight N ≤ 300*(N+1)^4 := by
   let z := N+1
   have hz : 1 ≤ z := by dsimp [z]; omega
   have hp2 : z^2 ≤ z^4 := Nat.pow_le_pow_right hz (by omega)
   have hp1 : z ≤ z^4 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1 ≤ 4)
   have hExp : approximationExponent N ≤ 12*z^2 := by
     have h1 : N+2 ≤ 2*z := by dsimp [z]; omega
     have h2 : (N+3)+(N+1)+2 ≤ 6*z := by dsimp [z]; omega
     have hh := Nat.mul_le_mul h1 h2
     dsimp only [approximationExponent]
     nlinarith only [hh]
   have hK := phaseBudget_upper N
   change phaseBudget N ≤ 200*z^4 at hK
   have hlin : 2*N+4 ≤ 4*z := by dsimp [z]; omega
   change approximationExponent N+phaseBudget N+2*N+4 ≤ 300*z^4
   nlinarith only [hExp,hK,hlin,hp1,hp2]
 theorem affineHeight_upper (N n : ℕ) : affineHeight N n ≤ 400*(N+1)^5 := by
   let z := N+1
   have hz : 1 ≤ z := by dsimp [z]; omega
   have hJ := recoveryHeight_upper N
   have h1 : 1 ≤ z^4 := one_le_pow₀ hz
   have hbase : recoveryHeight N+1 ≤ 301*z^4 := by dsimp [z] at *; omega
   have hn : N-n ≤ z := by dsimp [z]; omega
   have hh := Nat.mul_le_mul hn hbase
   have he : z*(301*z^4)=301*z^5 := by ring
   rw [he] at hh
   exact hh.trans (Nat.mul_le_mul_right _ (by omega))
 theorem stateHeight_uniform {N n k : ℕ} (hn : n ≤ N) (hk : k ≤ phaseBudget n) :
     stateHeight n k ≤ phaseHeight N := by
   let z := N+1
   have hz : 1 ≤ z := by dsimp [z]; omega
   have hpow1 : z ≤ z^4 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1 ≤ 4)
   have hpow0 : 1 ≤ z^4 := one_le_pow₀ hz
   have hK := hk.trans (phaseBudget_mono hn)
   have hK' := phaseBudget_upper N
   have hnz : n ≤ z := by dsimp [z]; omega
   dsimp only [stateHeight,phaseHeight]
   change 10*(k+n+4) ≤ 2050*z^4
   change phaseBudget N ≤ 200*z^4 at hK'
   nlinarith

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

 theorem phaseHeight_pow_four (N : ℕ) : 4 ≤ 2^phaseHeight N := by
   have h1 : 1 ≤ (N+1)^4 := one_le_pow₀ (by omega)
   have hh : 2 ≤ phaseHeight N := by dsimp [phaseHeight]; omega
   simpa only [show (2:ℕ)^2=4 by rfl] using Nat.pow_le_pow_right (by omega : 1 ≤ (2:ℕ)) hh
 theorem small_center_height (k : ℕ) (hk : k ≤ 1) :
     ((k:ℚ)/2).num.natAbs ≤ 4 ∧ ((k:ℚ)/2).den ≤ 4 := by
   interval_cases k <;> norm_num
 theorem phaseGeometry_size_certificate {N n : ℕ} (hn : n ≤ N) (V : Finset (Fin n → Bool)) (st : EllipsoidPhaseState)
     (h : PhaseGeometry V st) :
     ∃ (A : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ),
       RepresentsMatrix st.2.1 A ∧ RepresentsVector st.2.2 (rationalVector c) ∧
       (∀ row∈st.2.1,VectorCanonical row) ∧ VectorCanonical st.2.2 ∧
       (∀ i j,(A i j).num.natAbs ≤ 2^phaseHeight N ∧ (A i j).den ≤ 2^phaseHeight N) ∧
       (∀ i,(c i).num.natAbs ≤ 2^phaseHeight N ∧ (c i).den ≤ 2^phaseHeight N) := by
   cases h with
   | small hnsmall hs =>
     refine ⟨1,(fun _ => (st.1.2:ℚ)/2),hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2,?_,?_⟩
     · intro i j
       have hpow := phaseHeight_pow_four N
       simp only [Matrix.one_apply]
       split_ifs <;> norm_num only [Rat.num_one,Rat.den_one,Rat.num_zero,Rat.den_zero,Int.natAbs_one,Int.natAbs_zero] <;> constructor <;> omega
     · intro i
       have hh := small_center_height st.1.2 hs.2.1
       exact ⟨hh.1.trans (phaseHeight_pow_four N),hh.2.trans (phaseHeight_pow_four N)⟩
   | large hnlarge vs a k hv ha hst hbudget hcuts =>
     have hs := ellipsoidPrefix_correct hnlarge vs a hv ha k
     rw [←hst] at hs
     have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ (2:ℕ)) (stateHeight_uniform hn hbudget)
     refine ⟨shapes n a k,centers n a 0 k,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2,?_,?_⟩
     · intro i j
       have hh := shapes_height n hnlarge a ha k i j
       exact ⟨hh.1.trans hpow,hh.2.trans hpow⟩
     · intro i
       have hh := centers_height n hnlarge a ha k i
       exact ⟨hh.1.trans hpow,hh.2.trans hpow⟩

 theorem phaseGeometry_volume {N n : ℕ} (hn : n ≤ N) (V : Finset (Fin n → Bool)) (st : EllipsoidPhaseState)
     (h : PhaseGeometry V st) :
     OAI.ThreeMachine.StackCompiler.volume st ≤ 100000*(N+1)^6 := by
   open OAI.ThreeMachine.StackCompiler in
   obtain ⟨A,c,hA,hc,hcan,hccan,hsize,hcsize⟩ := phaseGeometry_size_certificate hn V st h
   have hM := rational_matrix_word_volume st.2.1 A hA hcan hsize
   have hV := rational_vector_word_volume st.2.2 c hc hccan hcsize
   have hdim := phaseGeometry_dimension V st h
   have hcounter := phaseGeometry_counter_bound V st h
   have hK := hcounter.trans (phaseBudget_mono hn)
   have hKmax := phaseBudget_upper N
   let z := N+1
   have hz : 1 ≤ z := by dsimp [z]; omega
   have hnz : n ≤ z := by dsimp [z]; omega
   have hL : 14*(phaseHeight N+2)+1 ≤ 30000*z^4 := by
     have h1 : 1 ≤ z^4 := one_le_pow₀ hz
     dsimp [phaseHeight,z]
     dsimp [z] at h1
     omega
   have hn2 : n*n ≤ z^2 := by nlinarith [Nat.mul_le_mul hnz hnz]
   have hMM := Nat.mul_le_mul hn2 hL
   have hVV := Nat.mul_le_mul hnz hL
   have he6 : z^2*(30000*z^4)=30000*z^6 := by ring
   have he5 : z*(30000*z^4)=30000*z^5 := by ring
   rw [he6] at hMM
   rw [he5] at hVV
   have h1 : 1 ≤ z^6 := one_le_pow₀ hz
   have hp1 : z ≤ z^6 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1 ≤ 6)
   have hp4 : z^4 ≤ z^6 := Nat.pow_le_pow_right hz (by omega)
   have hp5 : z^5 ≤ z^6 := Nat.pow_le_pow_right hz (by omega)
   have hmeta := RealizerBounds.volume_pair_eta st
   have hmeta2 := RealizerBounds.volume_pair_eta st.2
   have hmeta1 := RealizerBounds.volume_pair_eta st.1
   simp only [OAI.ThreeMachine.StackCompiler.volume_nat] at hmeta1
   rw [hdim] at hmeta1
   change phaseBudget N ≤ 200*z^4 at hKmax
   change _ ≤ 100000*z^6
   nlinarith

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

 theorem coreModel_volume {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig st A b V) : volume st ≤ 200000*(N+1)^8 := by
   have hcoords := affine_integer_height_coordinates A b h.height
   have hM := rational_rect_matrix_word_volume st.1.1 A h.affineRows h.rowsCanonical hcoords.1
   have hV := rational_vector_word_volume st.1.2 b h.affineOffsets h.offsetsCanonical hcoords.2
   have hP := phaseGeometry_volume h.order V st.2 h.phase
   let z := N+1
   have hz : 1 ≤ z := by dsimp [z]; omega
   have hNz : N ≤ z := by dsimp [z]; omega
   have hnz : n ≤ z := h.order.trans hNz
   have hJ := affineHeight_upper N n
   have h1 : 1 ≤ z^5 := one_le_pow₀ hz
   have hL : 14*(affineHeight N n+2)+1 ≤ 6000*z^5 := by
     change affineHeight N n ≤ 400*z^5 at hJ
     omega
   have hNN : N*n ≤ z^2 := by nlinarith [Nat.mul_le_mul hNz hnz]
   have hMM := Nat.mul_le_mul hNN hL
   have hVV := Nat.mul_le_mul hNz hL
   have he7 : z^2*(6000*z^5)=6000*z^7 := by ring
   have he6 : z*(6000*z^5)=6000*z^6 := by ring
   rw [he7] at hMM
   rw [he6] at hVV
   have hp1 : z ≤ z^8 := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1 ≤ 8)
   have hp6 : z^6 ≤ z^8 := Nat.pow_le_pow_right hz (by omega)
   have hp7 : z^7 ≤ z^8 := Nat.pow_le_pow_right hz (by omega)
   have hp0 : 1 ≤ z^8 := one_le_pow₀ hz
   have hc := volume_pair_eta st
   have ha := volume_pair_eta st.1
   change volume st.2 ≤ 100000*z^6 at hP
   change volume st ≤ 200000*z^8
   nlinarith
 theorem coreGeometry_volume {N : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleCoreState)
     (h : CoreGeometry N Orig st) : volume st ≤ 200000*(N+1)^8 := by
   obtain ⟨n,A,b,V,h⟩ := h
   exact coreModel_volume Orig st A b V h
 theorem oracleState_volume {N : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleState)
     (h : CoreGeometry N Orig st.2) : volume st ≤ 300000*(N+1)^8 := by
   have hh := coreGeometry_volume Orig st.2 h
   have hb := volume_bool st.1
   have hp := volume_pair_eta st
   have h1 : 1 ≤ (N+1)^8 := one_le_pow₀ (by omega)
   omega

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleDialogueClockValidity
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem dialogue_cut_safe {N : ℕ} (E : Program) (hE : ImplementsBinaryOracle E)
     (bound : Polynomial ℕ) (Orig : Finset (Fin N → Bool))
     (qs : List (Fin N → ℚ)) (cuts : List (RationalHalfspace N))
     (hadm : AdmissibleDialogue E bound N Orig qs cuts) (i : ℕ) (hi : i < cuts.length) :
     OracleCutSafe (rationalWords cuts[i].normal,oracleTranscriptState (cuts.take i)) := by
   intro hs
   have hh := (admissible_prefix_sound E hE bound Orig qs cuts hadm i hi.le).1
   obtain ⟨n,A,b,V,hmodel⟩ := hh
   obtain ⟨c0,hc0⟩ := phaseGeometry_center V _ hmodel.phase
   have hvalid := dialogue_query_is_native E hE bound Orig qs cuts hadm i hi A b V hmodel hs c0 hc0
   have hg := transcript_counter_live (cuts.take i) hs
   exact model_active_safe Orig _ A b V hmodel hg cuts[i] _ (rationalWords_rep cuts[i].normal) c0 hc0 hvalid
 theorem transcript_prefix_volume {N : ℕ} (E : Program) (hE : ImplementsBinaryOracle E)
     (bound : Polynomial ℕ) (Orig : Finset (Fin N → Bool))
     (qs : List (Fin N → ℚ)) (cuts : List (RationalHalfspace N))
     (hadm : AdmissibleDialogue E bound N Orig qs cuts) (i : ℕ) (hi : i ≤ cuts.length) :
     volume (oracleTranscriptState (cuts.take i)) ≤ 300000*(N+1)^8 := by
   exact oracleState_volume Orig _ (admissible_prefix_sound E hE bound Orig qs cuts hadm i hi).1
 

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

 theorem restricted_fold_clock {f : α×β → β} {R : Realizer f}
     (P : α×β → Prop) (hR : RestrictedPoly R P) (E r : ℕ) :
     ∃ D e : ℕ, 0< D ∧ ∀ (xs : List α) (b : β) (z : ℕ),
       volume (xs,b)+1≤ z →
       (∀ j,j≤ xs.length → volume ((xs.take j).foldl (fun b a => f (a,b)) b)≤ E*z^r) →
       (∀ j (hj : j < xs.length),P (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)) →
       R.fold.time (xs,b)≤ D*z^e ∧ volume (xs.foldl (fun b a => f (a,b)) b)≤ D*z^e := by
   obtain ⟨C,q,hC,hR⟩ := hR
   let F := C*(E+3)^q
   let u := (r+1)*q
   let e := u+r+2
   refine ⟨F+100*E+200,e,by dsimp [F]; positivity,?_⟩
   intro xs b z hinput hv hvalid
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
     have hh := ((hR _ (hvalid j hj)).1).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
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

-- Solutions.RestrictedComposedFoldClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 theorem restricted_composed_fold_clock {pre : α → List β×γ} {step : β×γ → γ}
     {R : Realizer pre} {S : Realizer step} (P : β×γ → Prop) (hR : PolyBound R) (hS : RestrictedPoly S P) (E r : ℕ) :
     ∃ D e : ℕ,0< D ∧ ∀ (a : α) (z : ℕ),volume a+1≤ z →
       (∀ j,j≤(pre a).1.length → volume (((pre a).1.take j).foldl (fun b x => step (x,b)) (pre a).2)≤ E*z^r) →
       (∀ j (hj : j < (pre a).1.length),P ((pre a).1[j],((pre a).1.take j).foldl (fun b x => step (x,b)) (pre a).2)) →
       (R.comp S.fold).time a≤ D*z^e ∧
       volume ((pre a).1.foldl (fun b x => step (x,b)) (pre a).2)≤ D*z^e := by
   obtain ⟨C,p,hC,hR⟩ := hR
   obtain ⟨F,q,hF,hfold⟩ := restricted_fold_clock P hS E r
   let K := F*(C+1)^q
   let e := (p+1)*(q+1)+1
   refine ⟨K+20*C+20,e,by dsimp [K]; positivity,?_⟩
   intro a z hin hv hvalid
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
   have hf := hfold (pre a).1 (pre a).2 W hinput hv' hvalid
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

-- Solutions.OracleExecutionClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem oracleExecute_valid_clock : RestrictedPoly oracleExecuteRealizer ValidExecutionInput := by
   let pre : Realizer (fun s : ℕ×SignedMatrix => (s.2,oracleInitial s.1)) := Realizer.snd.pair (Realizer.fst.comp oracleInitialRealizer)
   have hpre : PolyBound pre := polynomial_pair (linear_polynomial linear_snd)
     (polynomial_comp (linear_polynomial linear_fst) oracleInitial_polynomial)
   obtain ⟨C,q,hC,hfold⟩ := restricted_composed_fold_clock OracleCutSafe hpre oracleCut_clock 300000 8
   refine ⟨C,q,hC,?_⟩
   intro input hi
   obtain ⟨E,bound,Orig,qs,cuts,hE,hadm,hinput⟩ := hi
   let N := input.1
   let z := volume input+1
   have hNz : N+1 ≤ z := by
     have hh := volume_pair_eta input
     simp only [volume_nat] at hh
     dsimp only [N,z]
     omega
   have hpref : ∀ j,j ≤ input.2.length →
       volume ((input.2.take j).foldl (fun st cut => oracleCut (cut,st)) (oracleInitial input.1)) ≤ 300000*z^8 := by
     intro j hj
     change j ≤ input.2.length at hj
     rw [hinput,List.length_map] at hj
     have hh := transcript_prefix_volume E hE bound Orig qs cuts hadm j hj
     have he : ((input.2.take j).foldl (fun st cut => oracleCut (cut,st)) (oracleInitial input.1))=
         oracleTranscriptState (cuts.take j) := by
       rw [hinput,←List.map_take]
       rfl
     change volume ((input.2.take j).foldl (fun st cut => oracleCut (cut,st)) (oracleInitial input.1)) ≤ _
     rw [he]
     exact hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hNz 8))
   have hvalid : ∀ j (hj : j < input.2.length),OracleCutSafe
       (input.2[j],(input.2.take j).foldl (fun st cut => oracleCut (cut,st)) (oracleInitial input.1)) := by
     intro j hj
     change j < input.2.length at hj
     have hjc : j < cuts.length := by simpa only [hinput,List.length_map] using hj
     have hs := dialogue_cut_safe E hE bound Orig qs cuts hadm j hjc
     change OracleCutSafe (input.2[j],(input.2.take j).foldl (fun st cut => oracleCut (cut,st)) (oracleInitial input.1))
     have hElem : input.2[j]=rationalWords cuts[j].normal := by simp only [hinput,List.getElem_map]
     have hFold : (input.2.take j).foldl (fun st cut => oracleCut (cut,st)) (oracleInitial input.1)=oracleTranscriptState (cuts.take j) := by
       rw [hinput,←List.map_take]
       rfl
     rw [hElem,hFold]
     exact hs
   exact hfold input z le_rfl hpref hvalid

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

 
 theorem oracleCountHeader_expanded : Expanded oracleCountHeaderRealizer
     (fun s : ℕ×List Bool => value (readWord s.2).1) := by
   have hsnd := polynomial_comp_expanded
     (linear_polynomial (linear_snd : Linear (Realizer.snd : Realizer (fun s : ℕ×List Bool => s.2)))) readUnboundedNatural_expanded
   have hfst := polynomial_expanded (linear_polynomial (linear_fst : Linear (Realizer.fst : Realizer (fun s : ℕ×List Bool => s.1))))
     (fun s : ℕ×List Bool => value (readWord s.2).1)
   exact expanded_pair hfst hsnd
 theorem oracleHeader_expanded : Expanded oracleHeaderRealizer oracleHeaderMagnitude := by
   have hpre := expanded_comp readUnboundedNatural_expanded skipOracleBound_polynomial
   have h := expanded_comp_expanded hpre oracleCountHeader_expanded
   have he : oracleHeaderMagnitude=(fun L => value (readWord L).1+value (readWord (readWord (readWord L).2).2).1) := by
     funext L
     rfl
   rw [he]
   exact h
 theorem parseOracleTranscript_expanded : Expanded parseOracleTranscriptRealizer oracleHeaderMagnitude := by
   exact expanded_comp oracleHeader_expanded (polynomial_pair (linear_polynomial linear_fst) oracleNormals_polynomial)
 theorem oracleHeaderMagnitude_encoded (bound : Polynomial ℕ) (N : ℕ) (cuts : List (RationalHalfspace N)) :
     oracleHeaderMagnitude (ellipsoidWord bound N cuts)=N+cuts.length := by
   simp only [oracleHeaderMagnitude,ellipsoidWord,oracleHeader_encoded]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleOutputBounds
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem oracleOutput_polynomial : PolyBound oracleOutputRealizer := polynomial_comp
   (linear_polynomial (linear_pair linear_fst linear_id))
   (polynomial_selectiveChoose (linear_polynomial (linear_constant [Bool.false])) oracleQueryOutput_polynomial)
 theorem oracleOutput_uniform_bound :
     ∃ C q : ℕ,0 < C ∧ ∀ (N : ℕ) (Orig : Finset (Fin N → Bool)) (st : OracleState),
       CoreGeometry N Orig st.2 →
       oracleOutputRealizer.time st ≤ C*(N+1)^q ∧ volume (oracleOutput st) ≤ C*(N+1)^q := by
   obtain ⟨C,q,hC,hR⟩ := oracleOutput_polynomial
   refine ⟨C*300001^q,8*q,by positivity,?_⟩
   intro N Orig st h
   have hs := oracleState_volume Orig st h
   have h1 : 1 ≤ (N+1)^8 := one_le_pow₀ (by omega)
   have hbase : volume st+1 ≤ 300001*(N+1)^8 := by omega
   have hh := hR st
   have ht := hh.1.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
   have hv := hh.2.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
   simpa only [mul_pow,←pow_mul,Nat.mul_assoc] using And.intro ht hv

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

 
 theorem restricted_expanded_comp {f : α → β} {g : β → γ} (R : Realizer f) (S : Realizer g)
     (N : α → ℕ) (P : α → Prop) (Q : β → Prop)
     (hR : RestrictedExpanded R N P) (hS : RestrictedPoly S Q) (hf : ∀ x,P x → Q (f x)) :
     RestrictedExpanded (R.comp S) N P := by
   obtain ⟨C,q,hC,hR⟩ := hR
   obtain ⟨D,r,hD,hS⟩ := hS
   refine ⟨D*(C+1)^r+20*C+20,q+(q+1)*r+2,by positivity,?_⟩
   intro x hx
   let z := volume x+N x+1
   have hz : 1 ≤ z := by dsimp [z]; omega
   have hi := hR x hx
   have hl := hS (f x) (hf x hx)
   have hb : volume (f x)+1 ≤ volume (f x)+z := by omega
   have ht := hl.1.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hb r))
   have hv := hl.2.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hb r))
   have htime := RuntimeMath.polynomial_pipeline_clock z C q D r (R.time x) (volume (f x)) (S.time (f x)) hz hi.1 hi.2 ht
   have hout := RuntimeMath.polynomial_pipeline_clock z C q D r (R.time x) (volume (f x)) (volume (g (f x))) hz hi.1 hi.2 hv
   constructor
   · rw [Realizer.time_comp]
     exact htime
   · change volume (g (f x)) ≤ (D*(C+1)^r+20*C+20)*z^(q+(q+1)*r+2)
     omega

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

 
 theorem binaryOracle_expanded_clock : RestrictedExpanded binaryOracleRealizer oracleHeaderMagnitude ValidOracleWord := by
   obtain ⟨C,q,hC,hParser⟩ := parseOracleTranscript_expanded
   have hParse : RestrictedExpanded parseOracleTranscriptRealizer oracleHeaderMagnitude ValidOracleWord :=
     ⟨C,q,hC,fun x _ => hParser x⟩
   have hExec := restricted_expanded_comp parseOracleTranscriptRealizer oracleExecuteRealizer oracleHeaderMagnitude
     ValidOracleWord ValidExecutionInput hParse oracleExecute_valid_clock (fun x hx => hx)
   have hOut := polynomial_restrict oracleOutputRealizer (fun _ => True) oracleOutput_polynomial
   exact restricted_expanded_comp (parseOracleTranscriptRealizer.comp oracleExecuteRealizer) oracleOutputRealizer oracleHeaderMagnitude
     ValidOracleWord (fun _ => True) hExec hOut (fun _ _ => trivial)
 theorem binaryOracle_dialogue_clock :
     ∃ C q : ℕ,0 < C ∧ ∀ (E : Program),ImplementsBinaryOracle E →
       ∀ (bound : Polynomial ℕ) (N : ℕ) (Orig : Finset (Fin N → Bool))
         (qs : List (Fin N → ℚ)) (cuts : List (RationalHalfspace N)),
         AdmissibleDialogue E bound N Orig qs cuts →
         let L := ellipsoidWord bound N cuts
         binaryOracleRealizer.time L ≤ C*(volume L+N+cuts.length+1)^q ∧
         volume (binaryOracle L) ≤ C*(volume L+N+cuts.length+1)^q := by
   obtain ⟨C,q,hC,hclock⟩ := binaryOracle_expanded_clock
   refine ⟨C,q,hC,?_⟩
   intro E hE bound N Orig qs cuts hadm
   have hValid : ValidOracleWord (ellipsoidWord bound N cuts) := by
     change ValidExecutionInput (parseOracleTranscript (ellipsoidWord bound N cuts))
     rw [parseOracleTranscript_correct]
     exact ⟨E,bound,Orig,qs,cuts,hE,hadm,rfl⟩
   have hh := hclock _ hValid
   rw [oracleHeaderMagnitude_encoded] at hh
   simpa only [Nat.add_assoc] using hh

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleWorkPolynomials
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 theorem flatMap_length_le {α β : Type} (xs : List α) (f : α → List β) (B : ℕ)
     (h : ∀ a∈xs,(f a).length ≤ B) : (xs.flatMap f).length ≤ xs.length*B := by
   induction xs with
   | nil => simp
   | cons a xs ih =>
     have ha := h a (by simp)
     have htail := ih (fun b hb => h b (by simp [hb]))
     simp only [List.flatMap_cons,List.length_append,List.length_cons]
     nlinarith
 theorem admissible_cut_size {N : ℕ} (E : Program) (bound : Polynomial ℕ) (Orig : Finset (Fin N → Bool))
     (qs : List (Fin N → ℚ)) (cuts : List (RationalHalfspace N))
     (h : AdmissibleDialogue E bound N Orig qs cuts) :
     ∀ cut∈cuts,cut.bits.length ≤ bound.eval (N+1) := by
   intro cut hc
   obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hc
   obtain ⟨y,hy,hEval,hviol,hvalid,hbits⟩ := h.2 i hi
   exact hbits
 theorem ellipsoidWord_length_bound {N : ℕ} (E : Program) (bound : Polynomial ℕ) (Orig : Finset (Fin N → Bool))
     (qs : List (Fin N → ℚ)) (cuts : List (RationalHalfspace N))
     (h : AdmissibleDialogue E bound N Orig qs cuts) :
     (ellipsoidWord bound N cuts).length ≤ 2*N+2*bound.eval (N+1)+2*cuts.length+3+cuts.length*bound.eval (N+1) := by
   have hN := EncodingBounds.encodeNat_length N
   have hB := EncodingBounds.encodeNat_length (bound.eval (N+1))
   have hK := EncodingBounds.encodeNat_length cuts.length
   have hL := flatMap_length_le cuts RationalHalfspace.bits (bound.eval (N+1)) (admissible_cut_size E bound Orig qs cuts h)
   simp only [ellipsoidWord,List.length_append]
   omega
 theorem oracle_measure_bound {N : ℕ} (E : Program) (bound : Polynomial ℕ) (Orig : Finset (Fin N → Bool))
     (qs : List (Fin N → ℚ)) (cuts : List (RationalHalfspace N))
     (h : AdmissibleDialogue E bound N Orig qs cuts) (hK : cuts.length ≤ oracleQueries.eval (N+1)) :
     volume (ellipsoidWord bound N cuts)+N+cuts.length+1 ≤ (oracleWorkBase bound).eval (N+1) := by
   have hLen := ellipsoidWord_length_bound E bound Orig qs cuts h
   have hVol := BinaryAdder.volume_bits (ellipsoidWord bound N cuts)
   let B := bound.eval (N+1)
   let K := oracleQueries.eval (N+1)
   let z := N+1+B+K+1
   have hprod : cuts.length*B ≤ K*B := Nat.mul_le_mul_right B hK
   have hNs : N ≤ z := by dsimp [z]; omega
   have hBs : B ≤ z := by dsimp [z]; omega
   have hKs : K ≤ z := by dsimp [z]; omega
   have h1 : 1 ≤ z := by dsimp [z]; omega
   have hprod' : K*B ≤ z^2 := by nlinarith [Nat.mul_le_mul hKs hBs]
   have hzz : z ≤ z^2 := by nlinarith
   have hmeasure : volume (ellipsoidWord bound N cuts)+N+cuts.length+1 ≤ 50*z^2 := by
     dsimp [B,K] at hprod
     change cuts.length ≤ K at hK
     change (ellipsoidWord bound N cuts).length ≤ 2*N+2*B+2*cuts.length+3+cuts.length*B at hLen
     nlinarith
   simpa only [oracleWorkBase,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
     Polynomial.eval_add,Polynomial.eval_X,z,B,K] using hmeasure

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleFiniteProgram
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main
open RawStack

 theorem binary_oracle_finite_program :
     ∃ (E : Program) (K : ℕ),0 < K ∧ ∀ input : List Bool,
       Runs E input (binaryOracle input)
         (K*(binaryOracleRealizer.time input+input.length+(binaryOracle input).length+1)) := by
   exact realizer_native_program binaryOracle binaryOracleRealizer

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

 theorem exact_binary_oracle_local (bound : Polynomial ℕ) (hDesc : BinaryHullDescriptions bound) :
     ∃ (E : Program) (queries work coordinates : Polynomial ℕ),ExactEllipsoid E bound queries work coordinates := by
   obtain ⟨E,K,hK,hE⟩ := binary_oracle_finite_program
   have hImpl : ImplementsBinaryOracle E := fun input => ⟨_,hE input⟩
   obtain ⟨C,q,hC,hClock⟩ := binaryOracle_dialogue_clock
   obtain ⟨D,r,hD,hOut⟩ := oracleOutput_uniform_bound
   let work : Polynomial ℕ := Polynomial.C (K*(2*C+2))*(oracleWorkBase bound)^(q+1)
   let coordinates : Polynomial ℕ := Polynomial.C D*Polynomial.X^r
   refine ⟨E,oracleQueries,work,coordinates,hDesc,?_⟩
   intro N Orig qs cuts hadm hCount
   let L := ellipsoidWord bound N cuts
   let z := volume L+N+cuts.length+1
   let t := K*(binaryOracleRealizer.time L+L.length+(binaryOracle L).length+1)
   have hRun : Runs E L (binaryOracle L) t := hE L
   have hClock' := hClock E hImpl bound N Orig qs cuts hadm
   change binaryOracleRealizer.time L ≤ C*z^q ∧ volume (binaryOracle L) ≤ C*z^q at hClock'
   have hz : 1 ≤ z := by dsimp [z]; omega
   have hq : z^q ≤ z^(q+1) := Nat.pow_le_pow_right hz (by omega)
   have h1 : z ≤ z^(q+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1 ≤ q+1)
   have hIn : L.length+1 ≤ 2*z := by
     have hh := bits_length_volume L
     dsimp only [z]
     omega
   have hOutLen : (binaryOracle L).length ≤ C*z^q := (bits_length_volume _).trans hClock'.2
   have ht : t ≤ work.eval (N+1) := by
     have hsum : binaryOracleRealizer.time L+L.length+(binaryOracle L).length+1 ≤ (2*C+2)*z^(q+1) := by
       have htime := hClock'.1.trans (Nat.mul_le_mul_left C hq)
       have hout := hOutLen.trans (Nat.mul_le_mul_left C hq)
       have hin := hIn.trans (Nat.mul_le_mul_left 2 h1)
       nlinarith only [htime,hout,hin]
     have hb := oracle_measure_bound E bound Orig qs cuts hadm hCount
     change z ≤ (oracleWorkBase bound).eval (N+1) at hb
     calc
       t ≤ K*((2*C+2)*z^(q+1)) := Nat.mul_le_mul_left K hsum
       _ = K*(2*C+2)*z^(q+1) := by ring
       _ ≤ K*(2*C+2)*((oracleWorkBase bound).eval (N+1))^(q+1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _)
       _ = work.eval (N+1) := by simp only [work,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow]
   have hprefix := admissible_prefix_sound E hImpl bound Orig qs cuts hadm cuts.length le_rfl
   simp only [List.take_length] at hprefix
   obtain ⟨hgeom,hsound⟩ := hprefix
   let st := oracleTranscriptState cuts
   refine ⟨t,ht,?_⟩
   cases hs : st.1 with
   | true =>
     left
     have ho : binaryOracle L=[false] := by
       rw [binaryOracle_transcript]
       exact oracleOutput_rejected st hs
     rw [ho] at hRun
     exact ⟨hRun,hsound hs⟩
   | false =>
     right
     obtain ⟨n,A,b,V,hmodel⟩ := hgeom
     obtain ⟨c,hc⟩ := phaseGeometry_center V st.2.2 hmodel.phase
     have hd := phaseGeometry_dimension V st.2.2 hmodel.phase
     have ho := oracleOutput_query st hs A b c hmodel.affineRows hmodel.affineOffsets hc hd
     let y := A *ᵥ ((n+1:ℚ) • c)+b
     have hword : binaryOracle L=true::vectorBits y := by
       rw [binaryOracle_transcript]
       exact ho
     rw [hword] at hRun
     refine ⟨y,hRun,?_,?_⟩
     · have hbounds := (hOut N Orig st ⟨n,A,b,V,hmodel⟩).2
       rw [ho] at hbounds
       change volume (true::vectorBits y) ≤ D*(N+1)^r at hbounds
       have hh := bits_length_volume (true::vectorBits y)
       simp only [List.length_cons] at hh
       have hcsize : (vectorBits y).length ≤ D*(N+1)^r := by omega
       simpa only [coordinates,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X] using hcsize
     · intro hlen
       have hr := oracleExecute_reject_at_budget N (cuts.map (fun cut => rationalWords cut.normal))
         (by simpa only [List.length_map] using hlen)
       change st.1=true at hr
       rw [hs] at hr
       exact False.elim (Bool.false_ne_true hr)

end EdgeSublinearMWIS.Main
end

-- Solutions.Sol_exact_binary_oracle
noncomputable section

theorem solution (bound : Polynomial ℕ) (hbound : EdgeSublinearMWIS.Main.BinaryHullDescriptions bound) :
    ∃ (E : EdgeSublinearMWIS.Main.Program) (queries work coordinates : Polynomial ℕ),
      EdgeSublinearMWIS.Main.ExactEllipsoid E bound queries work coordinates := by
  exact EdgeSublinearMWIS.Main.exact_binary_oracle_local bound hbound
end
