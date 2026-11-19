-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.binary_oracle_prefix_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:06:29.88142+00:00
-- url     : https://prove2.me/submissions/4aa1c60b-167d-4fb4-a356-3f8ff18de9a4

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

 
 

 

 

 

 

 

 

 

 

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.BinaryTrim
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 

 

 

 theorem value_lt (L : List Bool) : value L<2^L.length := by
   induction L with
   | nil => simp [value]
   | cons b L ih => cases b <;> simp [value,pow_succ] <;> omega

 

 

 

 

 


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

 

 

 

 

 

 

 

 
 
 



 

 

 

 

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.AdderStepBound
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 

 

 
 
 
 
 
 
 

 

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.WordLengthBound
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler

 

 

 

 

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.AdderRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 

 

 

 

 

 

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

 

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.BinaryTrimRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.TrimRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 

 

 

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

 

 

 

 

 

 

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.BinaryArithmeticPolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 

 

 

 
 
 
 

 

 

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

 
 

 

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.BinarySubtractRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.BinarySubtract
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 

 

 

end EdgeSublinearMWIS.Main.BinarySubtract
end

-- Solutions.SubtractPolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.BinarySubtract
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 

 

 

end EdgeSublinearMWIS.Main.BinarySubtract
end

-- Solutions.BinaryDivisionRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds



 
 
 
 
 
 
 
 
 
 
 
 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FoldPrefixBound
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

 

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.BitFoldEnvelope
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {β : Type} [Coding β]

 

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
 
 
 

 
 

 
 
 
 
 

 
 
 
 

 
 
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedSumCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

 
 
 
 
 
 
 
 
 
 
 
 
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
 
 
 
 theorem canonicalAdd_denpos (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.2) :
     0< value (canonicalAdd (a,b)).2.2 := signedReduced_denpos _ (signedFractionAdd_denpos a b ha hb)
 theorem canonicalAdd_value (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.2) :
     signedFractionValue (canonicalAdd (a,b))=signedFractionValue a+signedFractionValue b := by
   rw [canonicalAdd,signedReduced_value _ (signedFractionAdd_denpos a b ha hb),signedFractionAdd_value a b ha hb]
 
 
 
 theorem canonicalMul_denpos (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.2) :
     0< value (canonicalMul (a,b)).2.2 := signedReduced_denpos _ (signedFractionMul_denpos a b ha hb)
 theorem canonicalMul_value (a b : SignedWords) (ha : 0< value a.2.2) (hb : 0< value b.2.2) :
     signedFractionValue (canonicalMul (a,b))=signedFractionValue a*signedFractionValue b := by
   rw [canonicalMul,signedReduced_value _ (signedFractionMul_denpos a b ha hb),signedFractionMul_value]
 
 
 
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

 

 

 

 

 

 

 

 

 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedVectorCode
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

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

 
 
 
 
 
 
 
 
 
 
 
 
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryWordProduct
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
 
 
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

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedFloorDyadic
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 
 
 
 
 
 
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

 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 theorem diagonalMaxStep_select (a b : DiagonalEntry) : diagonalMaxStep (a,b)=a ∨ diagonalMaxStep (a,b)=b := by
   unfold diagonalMaxStep
   split_ifs <;> simp
 
 
 
 
 
 
 

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

 
 theorem threeQuarter_den : 0< value threeQuarter.2.2 := by decide
 theorem threeQuarter_value : signedFractionValue threeQuarter=(3/4:ℚ) := by
   norm_num [threeQuarter,signedFractionValue,signedValue,value]
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 

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

theorem potential_ge_one {n : ℕ} (b : Matrix (Fin n) (Fin n) ℤ)
    (hb : LinearIndependent ℝ (embed b)) : 1≤ potD (embed b) := by
  apply Finset.one_le_prod
  intro i hi
  exact gram_ge_one b hb i (by have h:=Finset.mem_Ioo.mp hi; omega)

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

theorem descent_counter {T : ℕ} (p : ℕ → ℝ) (c : ℕ → ℕ)
    (hc0 : c 0=0)
    (step : ∀ t< T,
      (c (t+1)=c t ∧ p (t+1)≤ p t) ∨
      (c (t+1)=c t+1 ∧ p (t+1)≤ (3/4:ℝ)*p t)) :
    ∀ t≤ T, p t ≤ (3/4:ℝ)^(c t)*p 0 := by
  intro t ht
  induction t with
  | zero => simp [hc0]
  | succ t ih =>
    have hi := ih (by omega)
    rcases step t (by omega) with h|h
    · rw [h.1]
      exact h.2.trans hi
    · rw [h.1,pow_succ]
      have hm := mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤3/4)
      nlinarith [h.2]

theorem descent_steps_bound {T H : ℕ} (p : ℕ → ℝ) (c : ℕ → ℕ)
    (hc0 : c 0=0) (hlo : 1≤ p T) (hhi : p 0≤(2:ℝ)^H)
    (step : ∀ t< T,
      (c (t+1)=c t ∧ p (t+1)≤ p t) ∨
      (c (t+1)=c t+1 ∧ p (t+1)≤ (3/4:ℝ)*p t)) :
    c T < 4*(H+1) := by
  have hd := descent_counter p c hc0 step T le_rfl
  by_contra h
  have hc : 4*(H+1)≤ c T := by omega
  have hpow : (3/4:ℝ)^(c T)≤(3/4:ℝ)^(4*(H+1)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hc
  have hquarter : (3/4:ℝ)^4≤(1/2:ℝ) := by norm_num
  have hpow2 : (3/4:ℝ)^(4*(H+1))≤(1/2:ℝ)^(H+1) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hquarter _
  have hb : p T≤(1/2:ℝ)^(H+1)*(2:ℝ)^H := by
    calc
      _ ≤ (3/4:ℝ)^(c T)*p 0 := hd
      _ ≤ (3/4:ℝ)^(c T)*(2:ℝ)^H := mul_le_mul_of_nonneg_left hhi (by positivity)
      _ ≤ (1/2:ℝ)^(H+1)*(2:ℝ)^H := mul_le_mul_of_nonneg_right (hpow.trans hpow2) (by positivity)
  have he : (1/2:ℝ)^(H+1)*(2:ℝ)^H=1/2 := by
    rw [pow_succ]
    calc
      _ = (1/2:ℝ)*((1/2:ℝ)^H*2^H) := by ring
      _ = 1/2 := by rw [← mul_pow]; norm_num
  rw [he] at hb
  linarith

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

 theorem represents_castSucc_take {n : ℕ} (A : SignedVector) (x : Vec (n+1)) (h : RepresentsVector A x) :
     RepresentsVector (A.take n) (WithLp.toLp 2 (fun i : Fin n => x i.castSucc)) := by
   obtain ⟨a,rfl,ha,hv⟩ := h
   refine ⟨fun i => a i.castSucc,?_,fun i => ha i.castSucc,fun i => hv i.castSucc⟩
   rw [List.ofFn_succ']
   simp only [List.concat_eq_append]
   have he : n=(List.ofFn (fun i : Fin n => a i.castSucc)).length := by simp
   rw (occs := .pos [1]) [he]
   exact List.take_left

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



 theorem fullTrace_basis {n : ℕ} {b c : Fin n → Vec n} {t : ℕ}
     (h : FullTrace b t c) (hb : LinearIndependent ℝ b) :
     LinearIndependent ℝ c ∧ latticeOf c=latticeOf b := by
   induction h with
   | zero => exact ⟨hb,rfl⟩
   | succ prior step ih =>
     have hc := fullSwap_properties ih.1 step
     exact ⟨hc.1,hc.2.1.trans ih.2⟩

 theorem fullTrace_integral {n : ℕ} {b c : Fin n → Vec n} {t : ℕ}
     (h : FullTrace b t c) (hb : IntegralRows b) : IntegralRows c := by
   induction h with
   | zero => exact hb
   | succ prior step ih => exact fullSwap_integral ih step

 theorem fullTrace_potential {n : ℕ} {b c : Fin n → Vec n} {t : ℕ}
     (h : FullTrace b t c) (hb : LinearIndependent ℝ b) :
     potD c≤(3/4:ℝ)^t*potD b := by
   induction h with
   | zero => simp
   | @succ t c d prior step ih =>
     have hc := fullSwap_properties (fullTrace_basis prior hb).1 step
     calc
       potD d≤(3/4:ℝ)*potD c := hc.2.2.1.le
       _≤(3/4:ℝ)*((3/4:ℝ)^t*potD b) := mul_le_mul_of_nonneg_left ih (by norm_num)
       _=(3/4:ℝ)^(t+1)*potD b := by rw [pow_succ]; ring

 theorem fullTrace_length {n H t : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hb : LinearIndependent ℝ (embed B)) {c : Fin n → Vec n}
     (h : FullTrace (embed B) t c) (hpot : potD (embed B)≤(2:ℝ)^H) :
     t<4*(H+1) := by
   obtain ⟨C,hC⟩ := fullTrace_integral h ⟨B,rfl⟩
   have hcli := (fullTrace_basis h hb).1
   have hlo : 1≤ potD c := by rw [hC] at hcli ⊢; exact potential_ge_one C hcli
   have hhi := fullTrace_potential h hb
   have hl : 1≤(3/4:ℝ)^t*(2:ℝ)^H := hlo.trans (hhi.trans (mul_le_mul_of_nonneg_left hpot (by positivity)))
   let p : ℕ → ℝ := fun j => (3/4:ℝ)^j*(2:ℝ)^H
   exact RuntimeMath.descent_steps_bound p id rfl hl (by simp [p]) (by
     intro j hj
     right
     refine ⟨rfl,?_⟩
     dsimp [p]
     rw [pow_succ]
     apply le_of_eq
     ring)

 

 

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

 theorem fullTrace_integral_length {n H t : ℕ} {b c : Fin n → Vec n}
     (hb : LinearIndependent ℝ b) (hint : IntegralRows b) (hpot : potD b≤(2:ℝ)^H)
     (h : FullTrace b t c) : t<4*(H+1) := by
   obtain ⟨B,rfl⟩ := hint
   exact fullTrace_length B hb h hpot

end EdgeSublinearMWIS.Main.LLLBounds
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 theorem reductionGood_iterate {n H : ℕ} {b : Fin n → Vec n} {s : ReductionState}
     (h : ReductionGood b H 0 s) : ∀ t,ReductionGood b H t (reductionBody^[t] s) := by
   intro t
   induction t with
   | zero => exact h
   | succ t ih => rw [Function.iterate_succ_apply']; exact reductionGood_step ih

 theorem reductionLoop_correct {n H : ℕ} (b : Fin n → Vec n)
     (hb : BasisInvariant b H b) (hpot : potD b≤(2:ℝ)^H)
     (A : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (b i))
     (hcan : ∀ i,VectorCanonical (A i)) :
     ∃ (c : Fin n → Vec n) (A' : Fin n → SignedVector),
       reductionLoop (4*(H+1),List.ofFn A)=(true,List.ofFn A') ∧
       IsBasisFor c (latticeOf b) ∧ IsReduced c ∧ IntegralRows c ∧
       (∀ i,RepresentsVector (A' i) (c i)) ∧ (∀ i,VectorCanonical (A' i)) := by
   have hg := reductionGood_iterate (reductionGood_initial b hb A hA hcan) (4*(H+1))
   let s := reductionLoop (4*(H+1),List.ofFn A)
   change ReductionGood b H (4*(H+1)) s at hg
   obtain ⟨c,A',hword,hA',hcan',hc,hred,htrace⟩ := hg
   have hflag : s.1=true := by
     cases hs : s.1 with
     | true => rfl
     | false =>
       have hbad := fullTrace_integral_length hb.linear hb.integral hpot (htrace hs)
       exact (Nat.lt_irrefl _ hbad).elim
   refine ⟨c,A',Prod.ext hflag hword,⟨hc.linear,hc.lattice⟩,hred hflag,hc.integral,hA',hcan'⟩

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

 

 theorem reductionGram_step {n : ℕ} (original : Fin n → Vec n) (s : ReductionState)
     (h : ReductionGram original s) : ReductionGram original (reductionBody s) := by
   obtain ⟨b,A,hword,hA,hcan,hb,hgram⟩ := h
   by_cases hflag : s.1=true
   · simpa only [reductionBody,hflag,if_true] using
       (show ReductionGram original s from ⟨b,A,hword,hA,hcan,hb,hgram⟩)
   · have hact : reductionBody s=basisRound (List.ofFn A) := by simp [reductionBody,hflag,reductionActive,hword]
     rw [hact]
     rcases basisRound_correct b hb A hA hcan with hdone|hcont
     · obtain ⟨c,C,hout,hpass,hred,hC,hcc⟩ := hdone
       refine ⟨c,C,?_,hC,hcc,(pass_basis hpass hb).1,?_⟩
       · rw [hout]
       · rw [pass_gram hpass hb n le_rfl,hgram]
     · obtain ⟨c,C,hout,hswap,hC,hcc⟩ := hcont
       refine ⟨c,C,?_,hC,hcc,(fullSwap_properties hb hswap).1,?_⟩
       · rw [hout]
       · rw [(fullSwap_properties hb hswap).2.2.2,hgram]

 theorem reductionGram_iterate {n : ℕ} (b : Fin n → Vec n) (hb : LinearIndependent ℝ b)
     (A : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (b i))
     (hcan : ∀ i,VectorCanonical (A i)) (N : ℕ) :
     ReductionGram b (reductionLoop (N,List.ofFn A)) := by
   change ReductionGram b (reductionBody^[N] (false,List.ofFn A))
   induction N with
   | zero => exact ⟨b,A,rfl,hA,hcan,hb,rfl⟩
   | succ N ih => rw [Function.iterate_succ_apply']; exact reductionGram_step b _ ih

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

 theorem represented_basis_unique {n : ℕ} {A C : Fin n → SignedVector}
     {b c : Fin n → LLLFactor.RedBasis.Vec n} (hword : List.ofFn A=List.ofFn C)
     (hA : ∀ i,RepresentsVector (A i) (b i)) (hC : ∀ i,RepresentsVector (C i) (c i)) : b=c := by
   have hac := List.ofFn_inj.mp hword
   subst C
   funext i
   exact represents_unique (hA i) (hC i)

 theorem reductionLoop_correct_gram {n H : ℕ} (b : Fin n → LLLFactor.RedBasis.Vec n)
     (hb : LLLBounds.BasisInvariant b H b) (hpot : LLLFactor.Reduction.potD b≤(2:ℝ)^H)
     (A : Fin n → SignedVector) (hA : ∀ i,RepresentsVector (A i) (b i))
     (hcan : ∀ i,VectorCanonical (A i)) :
     ∃ (c : Fin n → LLLFactor.RedBasis.Vec n) (A' : Fin n → SignedVector),
       reductionLoop (4*(H+1),List.ofFn A)=(true,List.ofFn A') ∧
       LLLFactor.RedBasis.IsBasisFor c (LLLFactor.RedBasis.latticeOf b) ∧
       LLLFactor.RedBasis.IsReduced c ∧ LLLBounds.IntegralRows c ∧
       (∀ i,RepresentsVector (A' i) (c i)) ∧ (∀ i,VectorCanonical (A' i)) ∧
       LLLFactor.Reduction.gram c n=LLLFactor.Reduction.gram b n := by
   obtain ⟨c,A',hout,hbasis,hred,hint,hA',hcan'⟩ := reductionLoop_correct b hb hpot A hA hcan
   obtain ⟨d,D,hword,hD,hdcan,hd,hgram⟩ := reductionGram_iterate b hb.linear A hA hcan (4*(H+1))
   rw [hout] at hword
   have heq : c=d := represented_basis_unique hword hA' hD
   exact ⟨c,A',hout,hbasis,hred,hint,hA',hcan',heq.symm ▸ hgram⟩

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLReducedGramBound
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 theorem reduced_gs_adjacent {n : ℕ} {b : Fin n → Vec n} (hb : LinearIndependent ℝ b)
     (hred : IsReduced b) (i : ℕ) (hi : i+1< n) :
     ‖gs b ⟨i,by omega⟩‖^2≤2*‖gs b ⟨i+1,hi⟩‖^2 := by
   have hl := hred.2 i hi
   have hm := hred.1 ⟨i+1,hi⟩ ⟨i,by omega⟩ (by simp)
   rw [gs_lovasz_square b ⟨i,by omega⟩ ⟨i+1,hi⟩ (by intro he; have hh:=congrArg Fin.val he; simp at hh)] at hl
   have hm2 : mu b ⟨i+1,hi⟩ ⟨i,by omega⟩^2≤(1/4:ℝ) := by
     have hh := abs_le.mp hm
     nlinarith
   nlinarith [sq_nonneg ‖gs b ⟨i,by omega⟩‖,
     mul_le_mul_of_nonneg_right hm2 (sq_nonneg ‖gs b ⟨i,by omega⟩‖)]

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLFirstVectorBound
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 theorem reduced_gs_chain {n : ℕ} (hn : 0< n) (b : Fin n → Vec n)
     (hb : LinearIndependent ℝ b) (hred : IsReduced b) (i : ℕ) (hi : i< n) :
     ‖gs b ⟨0,hn⟩‖^2≤(2:ℝ)^i*‖gs b ⟨i,hi⟩‖^2 := by
   induction i with
   | zero => simp
   | succ i ih =>
     have hp := ih (by omega)
     have hs := reduced_gs_adjacent hb hred i hi
     have hm := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ)≤2^i)
     calc
       _≤(2:ℝ)^i*‖gs b ⟨i,by omega⟩‖^2 := hp
       _≤(2:ℝ)^i*(2*‖gs b ⟨i+1,hi⟩‖^2) := hm
       _=(2:ℝ)^(i+1)*‖gs b ⟨i+1,hi⟩‖^2 := by rw [pow_succ]; ring

 theorem first_norm_gs {n : ℕ} (hn : 0< n) (b : Fin n → Vec n) :
     ‖b ⟨0,hn⟩‖^2=‖gs b ⟨0,hn⟩‖^2 := by
   rw [norm_sq_decompose]
   have he : Finset.Iio (⟨0,hn⟩ : Fin n)=∅ := by
     ext j
     simp only [Finset.mem_Iio,Finset.notMem_empty,iff_false]
     change ¬j.val<0
     omega
   rw [he,Finset.sum_empty,add_zero]

 theorem reduced_first_gram_bound {n : ℕ} (hn : 0< n) (b : Fin n → Vec n)
     (hb : LinearIndependent ℝ b) (hred : IsReduced b) :
     (‖b ⟨0,hn⟩‖^2)^n≤(2:ℝ)^(n*n)*gram b n := by
   have hlocal (i : Fin n) : ‖gs b ⟨0,hn⟩‖^2≤(2:ℝ)^n*‖gs b i‖^2 := by
     exact (reduced_gs_chain hn b hb hred i.val i.isLt).trans
       (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt i.isLt)) (sq_nonneg _))
   have hp := Finset.prod_le_prod (s:=Finset.univ) (fun i _ => sq_nonneg ‖gs b ⟨0,hn⟩‖)
     (fun i _ => hlocal i)
   have hg := ((gram_eq_prod_gs b hb).1 n le_rfl).1
   have hge : gram b n=∏ i : Fin n,‖gs b i‖^2 := by simpa only [Fin.castLE_refl,Function.comp_apply] using hg
   rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Finset.prod_mul_distrib,
     Finset.prod_const,Finset.card_univ,Fintype.card_fin,←hge,←first_norm_gs hn b] at hp
   simpa only [←pow_mul] using hp

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

 theorem integerLLL_correct_gram {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
     (hb : LinearIndependent ℝ (embed B)) :
     ∃ C : Matrix (Fin n) (Fin n) ℤ,
       integerLLL (integerMatrixInput B)=integerMatrixInput C ∧
       IsBasisFor (embed C) (latticeOf (embed B)) ∧ IsReduced (embed C) ∧
       gram (embed C) n=gram (embed B) n := by
   have hi := integer_input_invariant B hb
   obtain ⟨c,A,hloop,hbasis,hred,⟨C,hC⟩,hA,hcan,hgram⟩ :=
     reductionLoop_correct_gram (embed B) hi.1 hi.2 (integerWords B)
       (integerWords_rep B) (integerWords_canonical B)
   rw [hC] at hbasis hred hA hgram
   refine ⟨C,?_,hbasis,hred,hgram⟩
   rw [integerLLL,Function.comp_apply,Function.comp_apply]
   simp only [prepareReduction,parseIntegerMatrix_correct,reductionCount,hloop,finishReduction,Function.comp_apply]
   exact serializeMatrix_rep C A hA

 

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

 theorem gram_full_det {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
     gram (embed B) n=(B.det:ℝ)^2 := by
   have h : (fun i j : Fin n => inner ℝ (embed B i) (embed B j))=
       (B.map (Int.castRingHom ℝ))*(B.map (Int.castRingHom ℝ)).transpose := by
     ext i j
     simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.map_apply]
     rw [inner_embed]
     simp only [Int.cast_sum,Int.cast_mul]
     rfl
   simp only [gram,dif_pos le_rfl,Fin.castLE_refl]
   rw [h]
   change ((B.map (Int.castRingHom ℝ))*(B.map (Int.castRingHom ℝ)).transpose).det=_
   rw [Matrix.det_mul,Matrix.det_transpose]
   have hc : (B.map (Int.castRingHom ℝ)).det=(B.det:ℝ) := (Int.cast_det B).symm
   rw [hc]
   ring

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

 theorem approximationReduced_correct {n : ℕ} (q : Fin n → RationalCode) (r : ℕ) :
     ∃ C : Matrix (Fin (n+1)) (Fin (n+1)) ℤ,
       approximationReducedWords (r,List.ofFn (fun i => codeWords (q i)))=List.ofFn (integerWords C) ∧
       IsBasisFor (embed C) (latticeOf (embed (approximationIntegerBasis q r))) ∧ IsReduced (embed C) ∧
       LLLFactor.Reduction.gram (embed C) (n+1)=LLLFactor.Reduction.gram (embed (approximationIntegerBasis q r)) (n+1) := by
   obtain ⟨C,hC,hbasis,hred,hgram⟩ := integerLLL_correct_gram (approximationIntegerBasis q r)
     (approximationIntegerBasis_independent q r)
   refine ⟨C,?_,hbasis,hred,hgram⟩
   simp only [approximationReducedWords,Function.comp_apply,approximationInput_codes,hC,parseIntegerMatrix_correct]

 

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

 theorem extraction_denominator_correct {n : ℕ} (A X : SignedVector) (v : Vec n) (x : Vec (n+1))
     (hA : RepresentsVector A v) (hX : RepresentsVector X x) (T U : List Bool) (hU : 0< value U) :
     0< value (extractApproximationDenominator (A,((T,U),X))).2.2 ∧
       (signedFractionValue (extractApproximationDenominator (A,((T,U),X))):ℝ)=
         x (Fin.last n)/(value U:ℝ) := by
   have hlen := represents_length hA
   have hx := represents_lookup X x hX (Fin.last n) zeroSignedWord
   let s := (X.drop n).headD zeroSignedWord
   have hs : 0< value s.2.2 := hx.1
   have hval : (signedFractionValue s:ℝ)=x (Fin.last n) := hx.2
   have hu : 0< value (unsignedIntegerWord U).2.1 := hU
   have hd := canonicalDiv_denpos s (unsignedIntegerWord U) hs hu
   have hv := canonicalDiv_value s (unsignedIntegerWord U) hs hu
   have he : extractApproximationDenominator (A,((T,U),X))=canonicalDiv (s,unsignedIntegerWord U) := by
     simp only [extractApproximationDenominator,extractBasisLast,hlen,s]
   rw [he]
   refine ⟨hd,?_⟩
   rw [hv,Rat.cast_div,hval,unsignedInteger_value,Rat.cast_natCast]

 theorem extraction_numerators_correct {n : ℕ} (A X : SignedVector) (v : Vec n) (x : Vec (n+1))
     (hA : RepresentsVector A v) (hX : RepresentsVector X x) (T U : List Bool)
     (hT : 0< value T) (hU : 0< value U) :
     RepresentsVector (extractApproximationNumerators (A,((T,U),X)))
       ((x (Fin.last n)/(value U:ℝ)) • v-
         ((value T:ℝ)⁻¹) • WithLp.toLp 2 (fun i : Fin n => x i.castSucc)) := by
   have hq := extraction_denominator_correct A X v x hA hX T U hU
   have hrecipD := canonicalDiv_denpos (unsignedIntegerWord [true]) (unsignedIntegerWord T)
     (unsignedInteger_den [true]) (show 0< value (unsignedIntegerWord T).2.1 from hT)
   have hrecipV := canonicalDiv_value (unsignedIntegerWord [true]) (unsignedIntegerWord T)
     (unsignedInteger_den [true]) (show 0< value (unsignedIntegerWord T).2.1 from hT)
   have hrecip : (signedFractionValue (canonicalDiv (unsignedIntegerWord [true],unsignedIntegerWord T)):ℝ)=
       (value T:ℝ)⁻¹ := by
     rw [hrecipV,Rat.cast_div,unsignedInteger_value,unsignedInteger_value,Rat.cast_natCast,Rat.cast_natCast]
     simp [value]
   have hp := represents_castSucc_take X x hX
   have hleft := represents_scale hA _ hq.1
   have hright := represents_scale hp _ hrecipD
   rw [hq.2] at hleft
   rw [hrecip] at hright
   have hh := represents_sub hleft hright
   simpa only [extractApproximationNumerators,represents_length hA] using hh

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

 theorem extraction_integer_solution {n : ℕ} (A X : SignedVector) (v : Vec n) (x : Vec (n+1))
     (hA : RepresentsVector A v) (hX : RepresentsVector X x) (T U : List Bool)
     (hT : 0< value T) (hU : 0< value U) (a p : Fin n → ℤ) (q : ℤ)
     (ha : ∀ i,v i*(value T:ℝ)=(a i:ℝ))
     (hcoord : ∀ i,x i.castSucc=(value T:ℝ)*(p i:ℝ)+(a i:ℝ)*q)
     (hlast : x (Fin.last n)=(value U:ℝ)*q) :
     RepresentsVector (extractApproximation (A,((T,U),X))).1
       (WithLp.toLp 2 (fun i => -(p i:ℝ))) ∧
       0< value (extractApproximation (A,((T,U),X))).2.2.2 ∧
       (signedFractionValue (extractApproximation (A,((T,U),X))).2:ℝ)=(q:ℝ) := by
   have hq := extraction_denominator_correct A X v x hA hX T U hU
   have hU0 : (value U:ℝ)≠0 := by exact_mod_cast ne_of_gt hU
   have hT0 : (value T:ℝ)≠0 := by exact_mod_cast ne_of_gt hT
   have hqval : (signedFractionValue (extractApproximationDenominator (A,((T,U),X))):ℝ)=(q:ℝ) := by
     rw [hq.2,hlast]
     field_simp
   have hp := extraction_numerators_correct A X v x hA hX T U hT hU
   have hval : (x (Fin.last n)/(value U:ℝ)) • v-(value T:ℝ)⁻¹ •
       WithLp.toLp 2 (fun i : Fin n => x i.castSucc)=WithLp.toLp 2 (fun i => -(p i:ℝ)) := by
     ext i
     simp only [PiLp.sub_apply,PiLp.smul_apply,WithLp.ofLp_toLp,smul_eq_mul]
     rw [hlast]
     have he : (value U:ℝ)*(q:ℝ)/(value U:ℝ)=(q:ℝ) := by field_simp
     rw [he,hcoord,inv_mul_eq_div]
     field_simp
     nlinarith only [congrArg (fun z : ℝ => (q:ℝ)*z) (ha i)]
   exact ⟨hval ▸ hp,hq.1,hqval⟩

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

 theorem approximation_lattice_coordinates {n : ℕ} (a : Fin n → ℤ) (T U : ℤ)
     (x : Vec (n+1)) (hx : x∈latticeOf (embed (approximationBasis a T U))) :
     ∃ (p : Fin n → ℤ) (q : ℤ),
       (∀ i,(x i.castSucc:ℝ)=(T:ℝ)*p i+(a i:ℝ)*q) ∧
       (x (Fin.last n):ℝ)=(U:ℝ)*q := by
   obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
   refine ⟨fun i => c i.castSucc,c (Fin.last n),?_,?_⟩
   · intro j
     have he := congrArg (fun v : Vec (n+1) => v j.castSucc) hc
     rw [Fin.sum_univ_castSucc] at he
     simp only [PiLp.add_apply,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,embed,WithLp.ofLp_toLp,
       zsmul_eq_mul,smul_eq_mul,approximationBasis_cast,approximationBasis_last] at he
     have hs : (∑ i : Fin n,(c i.castSucc:ℝ)*(if i.castSucc=j.castSucc then T else 0 : ℤ))=
         (c j.castSucc:ℝ)*T := by
       simp [Fin.castSucc_inj,Finset.sum_ite_eq']
     rw [hs] at he
     nlinarith only [he]
   · have he := congrArg (fun v : Vec (n+1) => v (Fin.last n)) hc
     rw [Fin.sum_univ_castSucc] at he
     simp only [PiLp.add_apply,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,embed,WithLp.ofLp_toLp,
       zsmul_eq_mul,smul_eq_mul,approximationBasis_cast,approximationBasis_last_last] at he
     have hs : (∑ i : Fin n,(c i.castSucc:ℝ)*(if i.castSucc=Fin.last n then T else 0 : ℤ))=0 := by
       apply Finset.sum_eq_zero
       intro i hi
       simp only [Fin.castSucc_ne_last,if_false,Int.cast_zero,mul_zero]
     rw [hs,zero_add] at he
     nlinarith only [he]

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

 theorem coordinate_abs_le_norm {n : ℕ} (x : Vec n) (i : Fin n) : |x i|≤‖x‖ := by
   have h := PiLp.norm_apply_le x i
   simpa only [Real.norm_eq_abs] using h

 theorem approximation_coordinates_nonzero {n : ℕ} (a : Fin n → ℤ) (T U : ℤ)
     (hT : 0< T) (x : Vec (n+1)) (hx : x≠0)
     (p : Fin n → ℤ) (q : ℤ)
     (hcoord : ∀ i,x i.castSucc=(T:ℝ)*p i+(a i:ℝ)*q)
     (hlast : x (Fin.last n)=(U:ℝ)*q) (hnorm : ‖x‖<(T:ℝ)) : q≠0 := by
   intro hq
   subst q
   have hp : ∀ i,p i=0 := by
     intro i
     have hsmall := (coordinate_abs_le_norm x i.castSucc).trans_lt hnorm
     rw [hcoord,Int.cast_zero,mul_zero,add_zero,abs_mul,abs_of_pos (show (0:ℝ)<(T:ℝ) by exact_mod_cast hT)] at hsmall
     have hpbound : |(p i:ℝ)|<1 := by nlinarith [show (0:ℝ)< T by exact_mod_cast hT]
     have hpint : |p i|<1 := by exact_mod_cast hpbound
     have hpabs := abs_lt.mp hpint
     omega
   apply hx
   ext i
   refine Fin.lastCases ?_ (fun j => ?_) i
   · simp [hlast]
   · simp [hcoord,hp]

 

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

 theorem approximation_reduced_norm {n : ℕ} (a : Fin n → ℤ) (T U : ℤ)
     (hT : 0< T) (hU : 0< U) (p : ℕ)
     (hscale : T=U*(2:ℤ)^((n+1)*(p+n+2)))
     (C : Matrix (Fin (n+1)) (Fin (n+1)) ℤ)
     (hb : LinearIndependent ℝ (embed C)) (hred : IsReduced (embed C))
     (hg : gram (embed C) (n+1)=gram (embed (approximationBasis a T U)) (n+1)) :
     ‖embed C ⟨0,by omega⟩‖≤(T:ℝ)/(2:ℝ)^(p+1) := by
   have hs := reduced_first_gram_bound (by omega : 0< n+1) (embed C) hb hred
   rw [hg,gram_full_det,approximationBasis_det] at hs
   let N := n+1
   let k := N*(p+n+2)
   have hTR : (T:ℝ)=(U:ℝ)*(2:ℝ)^k := by exact_mod_cast hscale
   have hT0 : (0:ℝ)< T := by exact_mod_cast hT
   have hU0 : (0:ℝ)< U := by exact_mod_cast hU
   have he : 2*k=(N*N+2*(p+1)*N)+(N*N) := by dsimp [k,N]; ring
   have hpow : (2:ℝ)^(N*N+2*(p+1)*N)≤(2:ℝ)^(2*k) :=
     pow_le_pow_right₀ (by norm_num) (by omega)
   have hineq : (‖embed C ⟨0,by omega⟩‖^2)^N*((2:ℝ)^(p+1))^(2*N)≤(T:ℝ)^(2*N) := by
     have hs' : (‖embed C ⟨0,by omega⟩‖^2)^N≤(2:ℝ)^(N*N)*((T:ℝ)^n*U)^2 := by
       simpa only [Int.cast_mul,Int.cast_pow] using hs
     have hmul := mul_le_mul_of_nonneg_right hs' (by positivity : 0≤((2:ℝ)^(p+1))^(2*N))
     have htw : (T:ℝ)^2=(U:ℝ)^2*(2:ℝ)^(2*k) := by rw [hTR]; ring
     have hscale2 : (2:ℝ)^(N*N)*((T:ℝ)^n*U)^2*((2:ℝ)^(p+1))^(2*N)≤(T:ℝ)^(2*N) := by
       have hsmall := mul_le_mul_of_nonneg_left hpow (by positivity : 0≤(T:ℝ)^(2*n)*(U:ℝ)^2)
       have hbig : (T:ℝ)^(2*N)=(T:ℝ)^(2*n)*(U:ℝ)^2*(2:ℝ)^(2*k) := by
         calc
           _=(T:ℝ)^(2*n)*(T:ℝ)^2 := by rw [←pow_add]; congr 1
           _=_ := by rw [htw]; ring
       rw [hbig]
       calc
         _=(T:ℝ)^(2*n)*(U:ℝ)^2*(2:ℝ)^(N*N+2*(p+1)*N) := by
           have hp : ((2:ℝ)^(p+1))^(2*N)=(2:ℝ)^(2*(p+1)*N) := by rw [←pow_mul]; congr 1; ring
           have ht : ((T:ℝ)^n)^2=(T:ℝ)^(2*n) := by rw [←pow_mul]; congr 1; omega
           rw [mul_pow,ht,hp,pow_add]
           ring
         _≤ _ := hsmall
     exact hmul.trans hscale2
   have hroot : (‖embed C ⟨0,by omega⟩‖*(2:ℝ)^(p+1))^(2*N)≤(T:ℝ)^(2*N) := by
     simpa only [mul_pow,pow_mul] using hineq
   have hbase : ‖embed C ⟨0,by omega⟩‖*(2:ℝ)^(p+1)≤(T:ℝ) :=
     (pow_le_pow_iff_left₀ (by positivity) (le_of_lt hT0) (by dsimp [N]; omega : 2*N≠0)).mp hroot
   exact (le_div_iff₀ (by positivity)).mpr hbase

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

 theorem headD_ofFn_succ {α : Type} {n : ℕ} (A : Fin (n+1) → α) (default : α) :
     (List.ofFn A).headD default=A ⟨0,by omega⟩ := by
   rw [List.ofFn_succ]
   rfl

 theorem simultaneousApproximation_correct {n : ℕ} (α : Fin n → RationalCode) (r : ℕ) :
     ∃ (p : Fin n → ℤ) (q : ℤ),q≠0 ∧
       RepresentsVector (simultaneousApproximation (r,List.ofFn (fun i => codeWords (α i)))).1
         (WithLp.toLp 2 (fun i => (p i:ℝ))) ∧
       0< value (simultaneousApproximation (r,List.ofFn (fun i => codeWords (α i)))).2.2.2 ∧
       (signedFractionValue (simultaneousApproximation (r,List.ofFn (fun i => codeWords (α i)))).2:ℝ)=(q:ℝ) ∧
       (∀ i,|(q:ℝ)*((α i).value:ℝ)-(p i:ℝ)|≤(2:ℝ)⁻¹^(r+1)) ∧
       |(q:ℝ)|≤(2:ℝ)^((n+1)*(r+n+2)) := by
   let A : SignedVector := List.ofFn (fun i => codeWords (α i))
   let v : Vec n := WithLp.toLp 2 (fun i => ((α i).value:ℝ))
   let mods := approximationModuli (r,A)
   let T : ℤ := (denominatorProduct α:ℤ)*2^((n+1)*(r+n+2))
   let U : ℤ := denominatorProduct α
   let a : Fin n → ℤ := approximationNumerator α r
   have hv := approximationModuli_codes α r
   have hmT : (value mods.1:ℤ)=T := by dsimp [mods,A,T]; rw [hv.1]; norm_cast
   have hmU : (value mods.2:ℤ)=U := by dsimp [mods,A,U]; rw [hv.2]
   have hU : 0< U := by dsimp [U]; exact_mod_cast denominatorProduct_pos α
   have hT : 0< T := by dsimp [T]; positivity
   have hUT : 0< value mods.2 := by exact_mod_cast (hmU ▸ hU)
   have hTT : 0< value mods.1 := by exact_mod_cast (hmT ▸ hT)
   have hA : RepresentsVector A v := by
     refine ⟨fun i => codeWords (α i),rfl,?_,?_⟩
     · intro i; change 0< value (natBits (α i).denominator); rw [value_natBits]; exact (α i).positive
     · intro i; rw [signedFractionValue_code]
   obtain ⟨C,hC,hbasis,hred,hgram⟩ := approximationReduced_correct α r
   have hB : approximationIntegerBasis α r=approximationBasis a T U := rfl
   rw [hB] at hbasis hgram
   let x := embed C ⟨0,by omega⟩
   have hx : x≠0 := hbasis.1.ne_zero _
   have hxL : x∈latticeOf (embed (approximationBasis a T U)) := by
     rw [←hbasis.2]
     exact Submodule.subset_span ⟨⟨0,by omega⟩,rfl⟩
   obtain ⟨p,q,hcoord,hlast⟩ := approximation_lattice_coordinates a T U x hxL
   have hn := approximation_reduced_norm a T U hT hU r rfl C hbasis.1 hred hgram
   change ‖x‖≤(T:ℝ)/(2:ℝ)^(r+1) at hn
   have hTR : (0:ℝ)< T := by exact_mod_cast hT
   have hUR : (0:ℝ)< U := by exact_mod_cast hU
   have hstrict : ‖x‖<(T:ℝ) := hn.trans_lt (div_lt_self hTR (one_lt_pow₀ (by norm_num) (by omega)))
   have hq := approximation_coordinates_nonzero a T U hT x hx p q hcoord hlast hstrict
   let X := integerWords C ⟨0,by omega⟩
   have hX : RepresentsVector X x := integerWords_rep C _
   have ha : ∀ i,v i*(value mods.1:ℝ)=(a i:ℝ) := by
     intro i
     have he : (value mods.1:ℝ)=(denominatorProduct α*2^((n+1)*(r+n+2)):ℕ) := by rw [hv.1]
     rw [he]
     exact approximationNumerator_correct α r i
   have hmTR : (value mods.1:ℝ)=(T:ℝ) := by exact_mod_cast hmT
   have hmUR : (value mods.2:ℝ)=(U:ℝ) := by exact_mod_cast hmU
   have hextract := extraction_integer_solution A X v x hA hX mods.1 mods.2 hTT hUT a p q ha
     (by simpa only [hmTR] using hcoord) (by simpa only [hmUR] using hlast)
   have hfirst : approximationFirstReduced (r,A)=X := by
     have he := congrArg (fun bs : List SignedVector => bs.headD []) hC
     simpa only [approximationFirstReduced,Function.comp_apply,headD_ofFn_succ,A,X] using he
   have hdata : approximationExtractionData (r,A)=(A,(mods,X)) := by
     unfold approximationExtractionData
     rw [hfirst]
   have hout : simultaneousApproximation (r,A)=extractApproximation (A,(mods,X)) := by
     rw [simultaneousApproximation,Function.comp_apply,hdata]
   refine ⟨fun i => -p i,q,hq,?_,?_,?_,?_,?_⟩
   · have hh := hextract.1
     rw [←hout] at hh
     simpa only [A,Int.cast_neg] using hh
   · have hh := hextract.2.1
     rw [←hout] at hh
     simpa only [A] using hh
   · have hh := hextract.2.2
     rw [←hout] at hh
     simpa only [A] using hh
   · intro i
     have hc : x i.castSucc=(T:ℝ)*(p i:ℝ)+(v i*(T:ℝ))*(q:ℝ) := by
       rw [hmTR] at ha
       rw [ha]
       exact hcoord i
     have he : (q:ℝ)*((α i).value:ℝ)-( -(p i:ℝ))=x i.castSucc/T := by
       rw [hc]
       change (q:ℝ)*v i-(-(p i:ℝ))=_
       field_simp
       ring
     have hcoordBound := coordinate_abs_le_norm x i.castSucc
     rw [Int.cast_neg,he,abs_div,abs_of_pos hTR]
     have h := (div_le_div_of_nonneg_right hcoordBound (le_of_lt hTR)).trans
       (div_le_div_of_nonneg_right hn (le_of_lt hTR))
     have hb : ((T:ℝ)/(2:ℝ)^(r+1))/(T:ℝ)=(2:ℝ)⁻¹^(r+1) := by rw [inv_pow]; field_simp
     simpa only [hb] using h
   · have hlastle := (coordinate_abs_le_norm x (Fin.last n)).trans (le_of_lt hstrict)
     rw [hlast,abs_mul,abs_of_pos hUR] at hlastle
     have he : (T:ℝ)=(U:ℝ)*(2:ℝ)^((n+1)*(r+n+2)) := by dsimp [T,U]; push_cast; rfl
     rw [he] at hlastle
     nlinarith only [hlastle,hUR]

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

 
 
 
 
 

 theorem canonicalApproximation_correct {n : ℕ} (A : SignedVector) (a : Fin n → ℚ)
     (hA : RepresentsVector A (rationalVector a)) (r : ℕ) :
     ∃ (p : Fin n → ℤ) (q : ℤ),q≠0 ∧
       RepresentsVector (canonicalApproximation (r,A)).1 (WithLp.toLp 2 (fun i => (p i:ℝ))) ∧
       0 < value (canonicalApproximation (r,A)).2.2.2 ∧
       (signedFractionValue (canonicalApproximation (r,A)).2:ℝ)=(q:ℝ) ∧
       (∀ i,|(q:ℝ)*(a i:ℝ)-(p i:ℝ)| ≤ (2:ℝ)⁻¹^(r+1)) ∧
       |(q:ℝ)| ≤ (2:ℝ)^((n+1)*(r+n+2)) := by
   have hh := simultaneousApproximation_correct (fun i => rationalCode (a i)) r
   simpa only [canonicalApproximation,Function.comp_apply,canonicalApproximationInput,
     normalizeVector_codes A a hA,rationalCode_value] using hh

 
 

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

 
 
 theorem hyperplane_precision_small (n : ℕ) :
     (n+1:ℝ)*(2:ℝ)⁻¹^(n+4)+
       (2:ℝ)^(approximationExponent n)*((n+1:ℝ)/((2:ℝ)^thinExponent n)) < 1 := by
   have hn : (n+1:ℝ) ≤ (2:ℝ)^(n+1) := by exact_mod_cast (Nat.le_of_lt (n+1).lt_two_pow_self)
   have hfirst : (n+1:ℝ)*4 ≤ (2:ℝ)^(n+4) := by
     have h := mul_le_mul_of_nonneg_right hn (by norm_num : (0:ℝ) ≤ 4)
     have he : (2:ℝ)^(n+1)*4=(2:ℝ)^(n+3) := by
       calc
         _ = (2:ℝ)^(n+1)*(2:ℝ)^2 := by norm_num
         _ = _ := by rw [←pow_add]
     rw [he] at h
     exact h.trans (pow_le_pow_right₀ (by norm_num) (by omega))
   have hsecond : (2:ℝ)^(approximationExponent n)*(n+1:ℝ)*4 ≤ (2:ℝ)^thinExponent n := by
     have h := mul_le_mul_of_nonneg_left hn (by positivity : (0:ℝ) ≤ (2:ℝ)^approximationExponent n)
     have hh := mul_le_mul_of_nonneg_right h (by norm_num : (0:ℝ) ≤ 4)
     have he : (2:ℝ)^(approximationExponent n)*(2:ℝ)^(n+1)*4=(2:ℝ)^(approximationExponent n+(n+1)+2) := by
       calc
         _ = (2:ℝ)^(approximationExponent n)*(2:ℝ)^(n+1)*(2:ℝ)^2 := by norm_num
         _ = _ := by rw [←pow_add,←pow_add]
     rw [he] at hh
     apply hh.trans
     apply pow_le_pow_right₀ (by norm_num)
     dsimp [thinExponent,approximationExponent]
     nlinarith
   have hp1 : 0 < (2:ℝ)^(n+4) := by positivity
   have hp2 : 0 < (2:ℝ)^thinExponent n := by positivity
   have hb1 : (n+1:ℝ)/(2:ℝ)^(n+4) ≤ 1/4 := by
     apply (div_le_iff₀ hp1).mpr
     linarith
   have hb2 : (2:ℝ)^(approximationExponent n)*((n+1:ℝ)/(2:ℝ)^thinExponent n) ≤ 1/4 := by
     rw [←mul_div_assoc]
     apply (div_le_iff₀ hp2).mpr
     linarith
   rw [inv_pow,←div_eq_mul_inv]
   linarith

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

 
 
 
 theorem dyadicUnitWord_den (p : ℕ) : 0< value (dyadicUnitWord p).2.2 := by change 0< value (powerTwoWord p); rw [powerTwoWord_value]; positivity
 theorem dyadicUnitWord_value (p : ℕ) : signedFractionValue (dyadicUnitWord p)=1/(2:ℚ)^p := by
   simp [dyadicUnitWord,signedFractionValue,signedValue,powerTwoWord_value,value]
 
 
 
 theorem enlargedUnitWord_correct (p : ℕ) :
     0< value (enlargedUnitWord p).2.2 ∧ signedFractionValue (enlargedUnitWord p)=1+1/(2:ℚ)^p := by
   refine ⟨canonicalAdd_denpos _ _ scalarOne_den (dyadicUnitWord_den p),?_⟩
   rw [enlargedUnitWord,canonicalAdd_value _ _ scalarOne_den (dyadicUnitWord_den p),scalarOne_value,dyadicUnitWord_value]
 
 
 
 theorem enlargementCoefficient_correct (p : ℕ) :
     0< value (enlargementCoefficient p).2.2 ∧ signedFractionValue (enlargementCoefficient p)=(1+1/(2:ℚ)^p)^2 := by
   refine ⟨canonicalMul_denpos _ _ (enlargedUnitWord_correct p).1 (enlargedUnitWord_correct p).1,?_⟩
   rw [enlargementCoefficient,Function.comp_apply,canonicalMul_value _ _ (enlargedUnitWord_correct p).1 (enlargedUnitWord_correct p).1,
     (enlargedUnitWord_correct p).2]
   ring
 
 
 
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



/-- Uniform entrywise error controls the error in every quadratic form. -/
theorem quadratic_error_bound {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hE : ∀ i j, |E i j| ≤ ε) (x : Fin n → ℝ) :
    |x ⬝ᵥ (E *ᵥ x)| ≤ (n : ℝ) * ε * (x ⬝ᵥ x) := by
  have hcs : (∑ i, |x i|) ^ 2 ≤ (n : ℝ) * (x ⬝ᵥ x) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin n => (1 : ℝ)) (fun i => |x i|)
    simpa [dotProduct, sq_abs, pow_two] using h
  calc
    _ = |∑ i, ∑ j, x i * E i j * x j| := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    _ ≤ ∑ i, ∑ j, |x i * E i j * x j| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, ε * |x i| * |x j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      calc
        _ ≤ |x i| * ε * |x j| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hE i j) (abs_nonneg _)) (abs_nonneg _)
        _ = _ := by ring
    _ = ε * (∑ i, |x i|) ^ 2 := by
      simp only [Finset.mul_sum, Finset.sum_mul, pow_two]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ε * ((n : ℝ) * (x ⬝ᵥ x)) := mul_le_mul_of_nonneg_left hcs hε
    _ = _ := by ring

































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

/-- A uniform form upper bound bounds each eigenvalue, without choosing coordinates. -/
theorem eigenvalue_le_of_form_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (k : ℝ)
    (hbound : ∀ x, x ⬝ᵥ (A *ᵥ x) ≤ k * (x ⬝ᵥ x)) (i : ι) :
    hA.eigenvalues i ≤ k := by
  let v : ι → ℝ := (hA.eigenvectorBasis i).ofLp
  have hv : v ≠ 0 := by
    intro h
    apply hA.eigenvectorBasis.toBasis.ne_zero i
    ext j
    exact congrFun h j
  have hxx : 0 < v ⬝ᵥ v := by
    simpa using (dotProduct_star_self_pos_iff (v := v)).mpr hv
  have he : A *ᵥ v = hA.eigenvalues i • v := hA.mulVec_eigenvectorBasis i
  have h := hbound v
  rw [he, dotProduct_smul, smul_eq_mul] at h
  exact (mul_le_mul_iff_of_pos_right hxx).mp h

/-- A positive semidefinite shape bounded by `k I` has determinant at most `kⁿ`. -/
theorem det_le_pow_of_form_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (k : ℝ)
    (hbound : ∀ x, x ⬝ᵥ (A *ᵥ x) ≤ k * (x ⬝ᵥ x)) :
    A.det ≤ k ^ Fintype.card ι := by
  rw [hA.1.det_eq_prod_eigenvalues]
  simpa [RCLike.ofReal_real_eq_id] using Finset.prod_le_prod
    (s := Finset.univ (α := ι)) (g := fun _ => k)
    (fun i _ => hA.eigenvalues_nonneg i)
    (fun i _ => eigenvalue_le_of_form_bound hA.1 k hbound i)



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

 
 
 
 theorem wordNonzero_correct (s : SignedWords) (hd : 0 < value s.2.2) :
     wordNonzero s=true ↔ signedFractionValue s≠0 := by
   have hdQ : (value s.2.2:ℚ)≠0 := by exact_mod_cast (ne_of_gt hd)
   have hn : signedFractionValue s=0 ↔ value s.2.1=0 := by
     rcases s with ⟨b,N,D⟩
     cases b <;> simp [signedFractionValue,signedValue,div_eq_zero_iff,hdQ]
   have hz := zeroWord_iff s.2.1
   cases hb : (trim s.2.1).isEmpty <;> simp_all [wordNonzero]
 
 
 
 
 
 
 
 
 
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

 
 
 
 theorem eraseIndex_eq (s : List α×ℕ) : eraseIndex s=s.1.eraseIdx s.2 := (List.eraseIdx_eq_take_drop_succ _ _).symm
 theorem eraseIndex_ofFn {n : ℕ} (a : Fin (n+1) → α) (j : Fin (n+1)) :
     eraseIndex (List.ofFn a,j.val)=List.ofFn (fun i => a (j.succAbove i)) := by
   rw [eraseIndex_eq]
   apply List.ext_getElem
   · rw [List.length_eraseIdx_of_lt (by simpa using j.isLt),List.length_ofFn,List.length_ofFn]; omega
   · intro i hi hi'
     have hin : i < n := by simpa only [List.length_ofFn] using hi'
     rw [List.getElem_eraseIdx]
     by_cases h : i < j.val
     · rw [dif_pos h,List.getElem_ofFn,List.getElem_ofFn]
       congr 1
       exact (Fin.succAbove_of_castSucc_lt j ⟨i,hin⟩ h).symm
     · rw [dif_neg h,List.getElem_ofFn,List.getElem_ofFn]
       congr 1
       exact (Fin.succAbove_of_le_castSucc j ⟨i,hin⟩ (by exact Nat.le_of_not_gt h)).symm

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
 theorem represents_rational_erase {n : ℕ} (bs : SignedVector) (a : Fin (n+1) → ℚ)
     (hA : RepresentsVector bs (rationalVector a)) (j : Fin (n+1)) :
     RepresentsVector (eraseIndex (bs,j.val)) (rationalVector (fun i => a (j.succAbove i))) := by
   obtain ⟨words,rfl,hD,hv⟩ := hA
   refine ⟨fun i => words (j.succAbove i),eraseIndex_ofFn words j,fun i => hD _,fun i => hv _⟩

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

 
 
 theorem eliminationRow_correct {n : ℕ} (as ps : SignedVector) (bs ds : SignedWords)
     (a p : Fin (n+1) → ℚ) (b d : ℚ) (j : Fin (n+1)) (hp : p j≠0)
     (ha : RepresentsVector as (rationalVector a)) (hps : RepresentsVector ps (rationalVector p))
     (hb : 0 < value bs.2.2) (hbv : signedFractionValue bs=b)
     (hd : 0 < value ds.2.2) (hdv : signedFractionValue ds=d) :
     RepresentsVector (eliminationRow ((as,bs),(j.val,(ps,ds)))).1 (rationalVector (eliminatedRow a p j)) ∧
       0 < value (eliminationRow ((as,bs),(j.val,(ps,ds)))).2.2.2 ∧
       signedFractionValue (eliminationRow ((as,bs),(j.val,(ps,ds)))).2=eliminatedOffset a p b d j := by
   let s : EliminationRowInput := ((as,bs),(j.val,(ps,ds)))
   have har := represents_lookup as (rationalVector a) ha j signedZero
   have hpr := represents_lookup ps (rationalVector p) hps j signedZero
   have hav : signedFractionValue (eliminationRowPivot s)=a j := Rat.cast_injective (α:=ℝ) har.2
   have hpv : signedFractionValue (eliminationNormalPivot s)=p j := Rat.cast_injective (α:=ℝ) hpr.2
   have hpnum := signed_num_positive_of_nonzero _ (by rw [hpv]; exact hp)
   have hrD : 0 < value (eliminationRatio s).2.2 := canonicalDiv_denpos _ _ har.1 hpnum
   have hr : signedFractionValue (eliminationRatio s)=a j/p j := by
     rw [eliminationRatio,canonicalDiv_value (eliminationRowPivot s) (eliminationNormalPivot s) har.1 hpnum,hav,hpv]
   have hrest := represents_rational_erase as a ha j
   have hnrest := represents_rational_erase ps p hps j
   have hscaled := represents_rational_scale _ _ hnrest _ hrD
   rw [hr] at hscaled
   have hrow := represents_rational_sub _ _ _ _ hrest hscaled
   have hrowEq : ((fun i => a (j.succAbove i))-(a j/p j) • (fun i => p (j.succAbove i)))=eliminatedRow a p j := by
     funext i; rfl
   rw [hrowEq] at hrow
   have hprodD := canonicalMul_denpos (eliminationRatio s) ds hrD hd
   have hprod := canonicalMul_value (eliminationRatio s) ds hrD hd
   have houtD := canonicalAdd_denpos bs _ hb hprodD
   have hout := canonicalAdd_value bs _ hb hprodD
   refine ⟨hrow,houtD,?_⟩
   change signedFractionValue (canonicalAdd (bs,canonicalMul (eliminationRatio s,ds)))=_
   rw [hout,hprod,hr,hbv,hdv]
   rfl

 theorem affineEliminate_correct {m n : ℕ} (rows : SignedMatrix) (offs ps : SignedVector) (ds : SignedWords)
     (A : Matrix (Fin m) (Fin (n+1)) ℚ) (b : Fin m → ℚ) (p : Fin (n+1) → ℚ)
     (d : ℚ) (j : Fin (n+1)) (hp : p j≠0)
     (hA : RepresentsRectMatrix rows A) (hb : RepresentsVector offs (rationalVector b))
     (hps : RepresentsVector ps (rationalVector p)) (hd : 0 < value ds.2.2) (hdv : signedFractionValue ds=d) :
     RepresentsRectMatrix (affineEliminate ((rows,offs),(j.val,(ps,ds)))).1
       (fun i => eliminatedRow (A i) p j) ∧
       RepresentsVector (affineEliminate ((rows,offs),(j.val,(ps,ds)))).2
         (rationalVector (fun i => eliminatedOffset (A i) p (b i) d j)) := by
   obtain ⟨rs,rfl,hrs⟩ := hA
   obtain ⟨bs,rfl,hbD,hbv⟩ := hb
   let out := fun i => eliminationRow ((rs i,bs i),(j.val,(ps,ds)))
   have he : eliminationRows ((List.ofFn rs,List.ofFn bs),(j.val,(ps,ds)))=List.ofFn out := by
     simp only [eliminationRows,arrayPairs_ofFn,List.map_ofFn]; rfl
   have hval (i : Fin m) := eliminationRow_correct (rs i) ps (bs i) ds (A i) p (b i) d j hp (hrs i) hps
     (hbD i) (Rat.cast_injective (α:=ℝ) (hbv i)) hd hdv
   constructor
   · refine ⟨fun i => (out i).1,?_,fun i => (hval i).1⟩
     simp only [affineEliminate,Function.comp_apply,he,List.map_ofFn]; rfl
   · refine ⟨fun i => (out i).2,?_,fun i => (hval i).2.1,?_⟩
     · simp only [affineEliminate,Function.comp_apply,he,List.map_ofFn]; rfl
     · intro i
       rw [(hval i).2.2]
       rfl

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

 theorem normalizeRectMatrix_rep {m n : ℕ} {bs : SignedMatrix} {A : Matrix (Fin m) (Fin n) ℚ}
     (hA : RepresentsRectMatrix bs A) :
     RepresentsRectMatrix (normalizeMatrix bs) A ∧ ∀ row∈normalizeMatrix bs,VectorCanonical row := by
   obtain ⟨rows,rfl,hrows⟩ := hA
   have he : normalizeMatrix (List.ofFn rows)=List.ofFn (fun i => normalizeVector (rows i)) := by
     simp only [normalizeMatrix,List.map_ofFn]; rfl
   rw [he]
   refine ⟨⟨fun i => normalizeVector (rows i),rfl,fun i => (normalizeVector_rep (hrows i)).1⟩,?_⟩
   intro row hrow
   obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
   exact (normalizeVector_rep (hrows i)).2
 
 
 
 
 theorem canonicalAffineEliminate_correct {m n : ℕ} (rows : SignedMatrix) (offs ps : SignedVector) (ds : SignedWords)
     (A : Matrix (Fin m) (Fin (n+1)) ℚ) (b : Fin m → ℚ) (p : Fin (n+1) → ℚ)
     (d : ℚ) (j : Fin (n+1)) (hp : p j≠0)
     (hA : RepresentsRectMatrix rows A) (hb : RepresentsVector offs (rationalVector b))
     (hps : RepresentsVector ps (rationalVector p)) (hd : 0 < value ds.2.2) (hdv : signedFractionValue ds=d) :
     RepresentsRectMatrix (canonicalAffineEliminate ((rows,offs),(j.val,(ps,ds)))).1
       (fun i => eliminatedRow (A i) p j) ∧
       RepresentsVector (canonicalAffineEliminate ((rows,offs),(j.val,(ps,ds)))).2
         (rationalVector (fun i => eliminatedOffset (A i) p (b i) d j)) ∧
       (∀ row∈(canonicalAffineEliminate ((rows,offs),(j.val,(ps,ds)))).1,VectorCanonical row) ∧
       VectorCanonical (canonicalAffineEliminate ((rows,offs),(j.val,(ps,ds)))).2 := by
   have hh := affineEliminate_correct rows offs ps ds A b p d j hp hA hb hps hd hdv
   have hm := normalizeRectMatrix_rep hh.1
   have hv := normalizeVector_rep hh.2
   exact ⟨hm.1,hv.1,hm.2,hv.2⟩

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

 
 
 
 
 theorem affineEvaluation_correct {m n : ℕ} (rows : SignedMatrix) (offs xs : SignedVector)
     (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (x : Fin n → ℚ)
     (hA : RepresentsRectMatrix rows A) (hb : RepresentsVector offs (rationalVector b))
     (hx : RepresentsVector xs (rationalVector x)) :
     RepresentsVector (affineEvaluation ((rows,offs),xs)) (rationalVector (A *ᵥ x+b)) := by
   exact represents_rational_add _ _ _ _ (represents_rect_matrix_vector rows A hA xs x hx) hb

 
 
 
 
 
 
 

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

 
 
 
 
 
 
 
 theorem oracleHeader_encoded (n B k : ℕ) (L : List Bool) :
     oracleHeader (encodeNat n++encodeNat B++encodeNat k++L)=(n,(k,L)) := by
   simp only [oracleHeader,Function.comp_apply,List.append_assoc,readUnboundedNatural_encoded,
     skipOracleBound,readWord_encoded,oracleCountHeader]
 
 
 
 
 
 
 
 

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

 theorem binary_hyperplane_recovery {n : ℕ} (V : Finset (Fin n → Bool))
     (u : Fin n → ℝ) (β : ℝ) (p : Fin n → ℤ) (d q : ℤ)
     (δ τ Q : ℝ) (hδ : 0≤δ) (hτ : 0≤τ) (hQ : |(q:ℝ)|≤ Q)
     (hp : ∀ i,|(p i:ℝ)-(q:ℝ)*u i|≤δ)
     (hd : |(d:ℝ)-(q:ℝ)*β|≤δ)
     (hthin : ∀ v∈V,|∑ i,u i*(if v i then 1 else 0)-β|≤τ)
     (hsmall : (n+1:ℝ)*δ+Q*τ<1) :
     ∀ z∈binaryHull V,∑ i,(p i:ℝ)*z i=(d:ℝ) := by
   have hvertex : ∀ v∈V,∑ i,(p i:ℝ)*(if v i then 1 else 0)=(d:ℝ) := by
     intro v hv
     have hs : |∑ i,((p i:ℝ)-(q:ℝ)*u i)*(if v i then 1 else 0)|≤(n:ℝ)*δ := by
       calc
         _≤∑ i,|((p i:ℝ)-(q:ℝ)*u i)*(if v i then 1 else 0)| := Finset.abs_sum_le_sum_abs _ _
         _≤∑ _i : Fin n,δ := by
           apply Finset.sum_le_sum
           intro i hi
           cases hvi : v i <;> simp only [hvi,Bool.false_eq_true,if_false,if_true,mul_zero,mul_one,abs_zero]
           · exact hδ
           · exact hp i
         _=_ := by simp
     have ht : |(q:ℝ)*(∑ i,u i*(if v i then 1 else 0)-β)|≤ Q*τ := by
       rw [abs_mul]
       exact mul_le_mul hQ (hthin v hv) (abs_nonneg _) (le_trans (abs_nonneg _) hQ)
     have he : (∑ i,(p i:ℝ)*(if v i then 1 else 0))-(d:ℝ)=
         (∑ i,((p i:ℝ)-(q:ℝ)*u i)*(if v i then 1 else 0))+
           (q:ℝ)*(∑ i,u i*(if v i then 1 else 0)-β)+((q:ℝ)*β-d) := by
       simp only [sub_mul,mul_sub,Finset.sum_sub_distrib,mul_assoc,←Finset.mul_sum]
       ring
     have hh := (abs_add_le (∑ i,((p i:ℝ)-(q:ℝ)*u i)*(if v i then 1 else 0))
       ((q:ℝ)*(∑ i,u i*(if v i then 1 else 0)-β))).trans (add_le_add hs ht)
     have hlast : |(q:ℝ)*β-d|≤δ := by rw [abs_sub_comm]; exact hd
     have hbound := (abs_add_le
       ((∑ i,((p i:ℝ)-(q:ℝ)*u i)*(if v i then 1 else 0))+(q:ℝ)*(∑ i,u i*(if v i then 1 else 0)-β))
       ((q:ℝ)*β-d)).trans (add_le_add hh hlast)
     have hz : |∑ i,(p i:ℝ)*(if v i then 1 else 0)-(d:ℝ)|<1 := by rw [he]; linarith
     let k : ℤ := ∑ i,p i*(if v i then 1 else 0)-d
     have hk : (k:ℝ)=∑ i,(p i:ℝ)*(if v i then 1 else 0)-(d:ℝ) := by
       simp only [k,Int.cast_sub,Int.cast_sum,Int.cast_mul,Int.cast_ite,Int.cast_one,Int.cast_zero]
     rw [←hk] at hz
     have hki : |k|<1 := by exact_mod_cast hz
     have hk0 : k=0 := by have := abs_lt.mp hki; omega
     rw [hk0,Int.cast_zero] at hk
     linarith
   have hconv : Convex ℝ {z : Fin n → ℝ | ∑ i,(p i:ℝ)*z i=(d:ℝ)} := by
     intro x hx y hy a b ha hb hab
     change (∑ i,(p i:ℝ)*x i)=(d:ℝ) at hx
     change (∑ i,(p i:ℝ)*y i)=(d:ℝ) at hy
     change (∑ i,(p i:ℝ)*(a • x+b • y) i)=(d:ℝ)
     simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib]
     have he1 : (∑ i,(p i:ℝ)*(a*x i))=a*∑ i,(p i:ℝ)*x i := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
     have he2 : (∑ i,(p i:ℝ)*(b*y i))=b*∑ i,(p i:ℝ)*y i := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
     rw [he1,he2,hx,hy,←add_mul,hab,one_mul]
   apply convexHull_min ?_ hconv
   rintro z ⟨v,hv,hz⟩
   have he := hvertex v hv
   change (∑ i,(p i:ℝ)*z i)=(d:ℝ)
   simpa only [←hz] using he

 theorem recovered_normal_nonzero {n : ℕ} (u : Fin n → ℝ) (p : Fin n → ℤ) (q : ℤ)
     (hq : q≠0) (i : Fin n) (hi : u i=1)
     (herr : |(p i:ℝ)-(q:ℝ)*u i|<1) : p≠0 := by
   intro hp
   rw [hp,Pi.zero_apply,Int.cast_zero,hi,mul_one,zero_sub,abs_neg] at herr
   have hqi : |q|<1 := by exact_mod_cast herr
   have hh := abs_lt.mp hqi
   exact hq (by omega)

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

 
 

 theorem ones_vector_rep (n : ℕ) :
     RepresentsVector (List.replicate n scalarOne) (rationalVector (fun _ : Fin n => (1:ℚ))) := by
   refine ⟨fun _ => scalarOne,by simp,fun _ => scalarOne_den,?_⟩
   intro i
   simp only [scalarOne_value,rationalVector,WithLp.ofLp_toLp,Rat.cast_one]
 theorem phaseGeometry_initial (n : ℕ) (V : Finset (Fin n → Bool)) : PhaseGeometry V (phaseInitial n) := by
   have hh := phaseInitial_correct n
   by_cases hn : n ≤ 1
   · apply PhaseGeometry.small hn
     refine ⟨rfl,by norm_num [phaseInitial],hh.2.1,?_,?_,hh.2.2.2.1,hh.2.2.2.2⟩
     · have he : (fun _ : Fin n => (((phaseInitial n).1.2:ℕ):ℚ)/2)=(0:Fin n → ℚ) := by
         funext i; simp only [phaseInitial,Nat.cast_zero,zero_div,Pi.zero_apply]
       rw [he]
       exact hh.2.2.1
     · intro he
       have hz : (phaseInitial n).1.2=0 := rfl
       omega
   · refine PhaseGeometry.large (by omega) (fun _ => List.replicate n scalarOne)
       (fun _ _ => (1:ℚ)) 0 (fun _ => ones_vector_rep n) ?_ rfl (phaseBudget_pos n).le ?_
     · intro j
       simp only [realVector,Rat.cast_one,dotProduct,one_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
       exact_mod_cast (by omega : 1 ≤ n)
     · intro j hj
       omega
 theorem phaseGeometry_dimension {n : ℕ} (V : Finset (Fin n → Bool)) (st : EllipsoidPhaseState)
     (h : PhaseGeometry V st) : st.1.1=n := by
   cases h with
   | small hn hs => exact hs.1
   | large hn vs a k hv ha hst hk hcuts =>
     rw [hst]
     exact congrArg Prod.fst (ellipsoidPrefix_correct hn vs a hv ha k).1
 

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

 
 
 theorem coordinateInsertion_project {n : ℕ} (p : Fin (n+1) → ℝ) (d : ℝ)
     (j : Fin (n+1)) (hp : p j≠0) (z : Fin (n+1) → ℝ) (hz : ∑ i,p i*z i=d) :
     coordinateInsertion p d j (coordinateProjection j z)=z := by
   funext i
   rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨i,rfl⟩
   · simp only [coordinateInsertion,Fin.insertNth_apply_same,coordinateProjection,LinearMap.coe_mk,AddHom.coe_mk]
     rw [Fin.sum_univ_succAbove (fun t => p t*z t) i] at hz
     apply (div_eq_iff hp).mpr
     linarith
   · simp only [coordinateInsertion,Fin.insertNth_apply_succAbove,coordinateProjection,LinearMap.coe_mk,AddHom.coe_mk]

 
 

 
 theorem insertion_projected_hull {n : ℕ} (V : Finset (Fin (n+1) → Bool))
     (p : Fin (n+1) → ℝ) (d : ℝ) (j : Fin (n+1)) (hp : p j≠0)
     (heq : ∀ z∈binaryHull V,∑ i,p i*z i=d) :
     ∀ y∈binaryHull (projectedBinarySet V j),coordinateInsertion p d j y∈binaryHull V := by
   apply convexHull_min ?_ ((convex_convexHull ℝ _).affine_preimage (coordinateInsertionAffine p d j))
   rintro y ⟨v,hv,hy⟩
   obtain ⟨v,hvV,rfl⟩ := Finset.mem_image.mp hv
   let z : Fin (n+1) → ℝ := fun i => if v i then 1 else 0
   have hz : z∈binaryHull V := subset_convexHull ℝ _ ⟨v,hvV,fun i => rfl⟩
   have hproj : y=coordinateProjection j z := by funext i; exact hy i
   change coordinateInsertion p d j y∈binaryHull V
   rw [hproj,coordinateInsertion_project p d j hp z (heq z hz)]
   exact hz

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

 theorem eliminated_row_evaluation {n : ℕ} (a p : Fin (n+1) → ℚ) (b d : ℚ)
     (j : Fin (n+1)) (hp : p j≠0) (y : Fin n → ℝ) :
     (∑ i,(eliminatedRow a p j i:ℝ)*y i)+(eliminatedOffset a p b d j:ℝ)=
       (∑ i,(a i:ℝ)*coordinateInsertion (fun i => (p i:ℝ)) (d:ℝ) j y i)+(b:ℝ) := by
   rw [Fin.sum_univ_succAbove (fun i => (a i:ℝ)*coordinateInsertion (fun i => (p i:ℝ)) (d:ℝ) j y i) j]
   simp only [eliminatedRow,eliminatedOffset,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_add,
     coordinateInsertion,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,sub_mul,Finset.sum_sub_distrib]
   have he : (∑ i,((a j:ℝ)/(p j:ℝ))*(p (j.succAbove i):ℝ)*y i)=
       ((a j:ℝ)/(p j:ℝ))*(∑ i,(p (j.succAbove i):ℝ)*y i) := by
     rw [Finset.mul_sum]
     apply Finset.sum_congr rfl
     intro i hi
     ring
   rw [he]
   ring

 theorem eliminated_row_integer_rep {n : ℕ} (u : Fin (n+1) → ℤ) (p : Fin (n+1) → ℤ)
     (v d D : ℤ) (j : Fin (n+1)) (hD : D≠0) (hp : p j≠0) :
     (∀ i,eliminatedRow (fun k => (u k:ℚ)/D) (fun k => (p k:ℚ)) j i=
       ((u (j.succAbove i)*p j-u j*p (j.succAbove i):ℤ):ℚ)/(D*p j:ℤ)) ∧
       eliminatedOffset (fun k => (u k:ℚ)/D) (fun k => (p k:ℚ)) ((v:ℚ)/D) (d:ℚ) j=
         ((v*p j+u j*d:ℤ):ℚ)/(D*p j:ℤ) := by
   have hdQ : (D:ℚ)≠0 := by exact_mod_cast hD
   have hpQ : (p j:ℚ)≠0 := by exact_mod_cast hp
   constructor
   · intro i
     simp only [eliminatedRow,Int.cast_sub,Int.cast_mul]
     field_simp <;> ring
   · simp only [eliminatedOffset,Int.cast_add,Int.cast_mul]
     field_simp <;> ring

 theorem integer_sum_products_height (a b c d : ℤ) (J H : ℕ)
     (ha : a.natAbs ≤ 2^J) (hb : b.natAbs ≤ 2^H)
     (hc : c.natAbs ≤ 2^J) (hd : d.natAbs ≤ 2^H) :
     (a*b+c*d).natAbs ≤ 2^(J+H+1) ∧ (a*b-c*d).natAbs ≤ 2^(J+H+1) := by
   have h1 := Nat.mul_le_mul ha hb
   have h2 := Nat.mul_le_mul hc hd
   have he : 2^J*2^H+2^J*2^H=2^(J+H+1) := by rw [pow_add,pow_add]; ring
   constructor
   · exact (Int.natAbs_add_le _ _).trans (by simpa only [Int.natAbs_mul,he] using Nat.add_le_add h1 h2)
   · exact (Int.natAbs_sub_le _ _).trans (by simpa only [Int.natAbs_mul,he] using Nat.add_le_add h1 h2)

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

 
 theorem affine_integer_height_initial (n : ℕ) :
     AffineIntegerHeight 0 (1:Matrix (Fin n) (Fin n) ℚ) (0:Fin n → ℚ) := by
   refine ⟨1,1,0,by decide,by norm_num,?_,?_⟩
   · intro i j
     simp only [Matrix.one_apply]
     split_ifs <;> norm_num
   · intro i; norm_num
 theorem affine_integer_height_step {m n J H : ℕ} (A : Matrix (Fin m) (Fin (n+1)) ℚ) (b : Fin m → ℚ)
     (hA : AffineIntegerHeight J A b) (p : Fin (n+1) → ℤ) (d : ℤ)
     (hp : ∀ i,(p i).natAbs ≤ 2^H) (hd : d.natAbs ≤ 2^H) (j : Fin (n+1)) (hj : p j≠0) :
     AffineIntegerHeight (J+H+1) (fun i => eliminatedRow (A i) (fun k => (p k:ℚ)) j)
       (fun i => eliminatedOffset (A i) (fun k => (p k:ℚ)) (b i) (d:ℚ) j) := by
   obtain ⟨D,U,v,hD,hDb,hU,hv⟩ := hA
   let D' := D*p j
   let U' : Matrix (Fin m) (Fin n) ℤ := fun i k => U i (j.succAbove k)*p j-U i j*p (j.succAbove k)
   let v' : Fin m → ℤ := fun i => v i*p j+U i j*d
   have hD' : D'≠0 := mul_ne_zero hD hj
   have hDb' : D'.natAbs ≤ 2^(J+H+1) := by
     dsimp only [D']
     rw [Int.natAbs_mul]
     have hh := Nat.mul_le_mul hDb (hp j)
     rw [←pow_add] at hh
     exact hh.trans (Nat.pow_le_pow_right (by omega) (by omega))
   refine ⟨D',U',v',hD',hDb',?_,?_⟩
   · intro i k
     have hh := integer_sum_products_height (U i (j.succAbove k)) (p j) (U i j) (p (j.succAbove k)) J H
       (hU _ _).1 (hp j) (hU _ _).1 (hp _)
     refine ⟨hh.2,?_⟩
     have hrow : A i=(fun k => (U i k:ℚ)/D) := funext (fun k => (hU i k).2)
     dsimp only
     rw [hrow]
     exact (eliminated_row_integer_rep (U i) p (v i) d D j hD hj).1 k
   · intro i
     have hh := integer_sum_products_height (v i) (p j) (U i j) d J H (hv i).1 (hp j) (hU _ _).1 hd
     refine ⟨hh.1,?_⟩
     have hrow : A i=(fun k => (U i k:ℚ)/D) := funext (fun k => (hU i k).2)
     dsimp only
     rw [hrow,(hv i).2]
     exact (eliminated_row_integer_rep (U i) p (v i) d D j hD hj).2
 

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

 theorem hyperplaneApproximation_correct {n : ℕ} (us cs : SignedVector) (u c : Fin n → ℚ)
     (hu : RepresentsVector us (rationalVector u)) (hc : RepresentsVector cs (rationalVector c)) :
     ∃ (P : Fin (n+1) → ℤ) (q : ℤ),q≠0 ∧
       RepresentsVector (hyperplaneApproximation (n,(us,cs))).1 (WithLp.toLp 2 (fun i => (P i:ℝ))) ∧
       0 < value (hyperplaneApproximation (n,(us,cs))).2.2.2 ∧
       (signedFractionValue (hyperplaneApproximation (n,(us,cs))).2:ℝ)=(q:ℝ) ∧
       (∀ i : Fin (n+1),|(q:ℝ)*((Fin.snoc (α:=fun _ : Fin (n+1) => ℚ) u ((n+1:ℚ)*(u ⬝ᵥ c)) i:ℚ):ℝ)-(P i:ℝ)| ≤ (2:ℝ)⁻¹^(n+4)) ∧
       |(q:ℝ)| ≤ (2:ℝ)^(approximationExponent n) := by
   have hh := canonicalApproximation_correct _ _ (hyperplaneCoordinates_correct us cs u c hu hc) (n+3)
   simpa only [hyperplaneApproximation,Function.comp_apply,hyperplaneApproximationData,
     hyperplanePrecision,approximationExponent,Nat.add_assoc] using hh

 theorem hyperplaneApproximation_recovers {n : ℕ} (us cs : SignedVector) (u c : Fin n → ℚ)
     (hu : RepresentsVector us (rationalVector u)) (hc : RepresentsVector cs (rationalVector c))
     (V : Finset (Fin n → Bool)) (j : Fin n) (hj : u j=1)
     (hthin : ∀ v∈V,|∑ i,(u i:ℝ)*(if v i then 1 else 0)-
       (((n+1:ℚ)*(u ⬝ᵥ c):ℚ):ℝ)| ≤ (n+1:ℝ)/(2:ℝ)^thinExponent n) :
     ∃ P : Fin (n+1) → ℤ,
       RepresentsVector (hyperplaneApproximation (n,(us,cs))).1 (WithLp.toLp 2 (fun i => (P i:ℝ))) ∧
       (fun i : Fin n => P i.castSucc)≠0 ∧
       ∀ z∈binaryHull V,∑ i,(P i.castSucc:ℝ)*z i=(P (Fin.last n):ℝ) := by
   obtain ⟨P,q,hq,hrep,hD,hval,herr,hbound⟩ := hyperplaneApproximation_correct us cs u c hu hc
   have he : ∀ i : Fin n,|(P i.castSucc:ℝ)-(q:ℝ)*(u i:ℝ)| ≤ (2:ℝ)⁻¹^(n+4) := by
     intro i
     have hh := herr i.castSucc
     simp only [Fin.snoc_castSucc] at hh
     rwa [abs_sub_comm] at hh
   have hd : |(P (Fin.last n):ℝ)-(q:ℝ)*(((n+1:ℚ)*(u ⬝ᵥ c):ℚ):ℝ)| ≤ (2:ℝ)⁻¹^(n+4) := by
     have hh := herr (Fin.last n)
     simp only [Fin.snoc_last] at hh
     rwa [abs_sub_comm] at hh
   have hδ : 0 ≤ (2:ℝ)⁻¹^(n+4) := by positivity
   have hτ : 0 ≤ (n+1:ℝ)/(2:ℝ)^thinExponent n := by positivity
   have hδsmall : (2:ℝ)⁻¹^(n+4) < 1 := by
     rw [inv_pow]
     exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by norm_num) (by omega))
   refine ⟨P,hrep,?_,?_⟩
   · apply recovered_normal_nonzero (fun i => (u i:ℝ)) (fun i => P i.castSucc) q hq j
       (by rw [hj,Rat.cast_one]) ((he j).trans_lt hδsmall)
   · exact binary_hyperplane_recovery V (fun i => (u i:ℝ))
       (((n+1:ℚ)*(u ⬝ᵥ c):ℚ):ℝ) (fun i => P i.castSucc) (P (Fin.last n)) q
       ((2:ℝ)⁻¹^(n+4)) ((n+1:ℝ)/(2:ℝ)^thinExponent n) ((2:ℝ)^approximationExponent n)
       hδ hτ hbound he hd hthin (hyperplane_precision_small n)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.HyperplaneCoefficientHeight
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools

 theorem integer_approximation_height (p q : ℤ) (a : ℝ) (K L : ℕ)
     (ha : |a| ≤ (2:ℝ)^L) (hq : |(q:ℝ)| ≤ (2:ℝ)^K)
     (he : |(q:ℝ)*a-(p:ℝ)| ≤ 1) : p.natAbs ≤ 2^(K+L+1) := by
   have hmul : |(q:ℝ)*a| ≤ (2:ℝ)^K*(2:ℝ)^L := by
     rw [abs_mul]; exact mul_le_mul hq ha (abs_nonneg _) (by positivity)
   have hbound : |(p:ℝ)| ≤ (2:ℝ)^K*(2:ℝ)^L+1 := by
     calc
       _ = |(q:ℝ)*a-((q:ℝ)*a-(p:ℝ))| := by congr 1; ring
       _ ≤ |(q:ℝ)*a|+|(q:ℝ)*a-(p:ℝ)| := by
         simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le ((q:ℝ)*a) 0 ((q:ℝ)*a-(p:ℝ))
       _ ≤ _ := add_le_add hmul he
   have h1 : (1:ℝ) ≤ (2:ℝ)^(K+L) := one_le_pow₀ (by norm_num)
   have hp : |(p:ℝ)| ≤ (2:ℝ)^(K+L+1) := by
     rw [←pow_add] at hbound
     rw [pow_succ]
     linarith
   have heq : (p.natAbs:ℝ)=|(p:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
   rw [←heq] at hp
   exact_mod_cast hp

 theorem hyperplane_beta_bound {n t : ℕ} (u c : Fin n → ℚ)
     (hu : ∀ i,|(u i:ℝ)| ≤ 1) (hc : ∀ i,|(c i:ℝ)| ≤ (2:ℝ)^(t+2)) :
     |(((n+1:ℚ)*(u ⬝ᵥ c):ℚ):ℝ)| ≤ (2:ℝ)^(t+2*n+3) := by
   have hs : |∑ i,(u i:ℝ)*(c i:ℝ)| ≤ (n:ℝ)*(2:ℝ)^(t+2) := by
     calc
       _ ≤ ∑ i,|(u i:ℝ)*(c i:ℝ)| := Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ _i : Fin n,(2:ℝ)^(t+2) := by
         apply Finset.sum_le_sum
         intro i hi
         rw [abs_mul]
         simpa only [one_mul] using mul_le_mul (hu i) (hc i) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
       _ = _ := by simp
   have hn : (n:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast Nat.le_of_lt n.lt_two_pow_self
   have hn1 : (n+1:ℝ) ≤ (2:ℝ)^(n+1) := by exact_mod_cast Nat.le_of_lt (n+1).lt_two_pow_self
   have hh := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ n+1)
   have hm := mul_le_mul hn1 hn (Nat.cast_nonneg n) (by positivity : (0:ℝ) ≤ (2:ℝ)^(n+1))
   have hfinal := mul_le_mul_of_nonneg_right hm (by positivity : (0:ℝ) ≤ (2:ℝ)^(t+2))
   have he : (2:ℝ)^(n+1)*(2:ℝ)^n*(2:ℝ)^(t+2)=(2:ℝ)^(t+2*n+3) := by
     rw [←pow_add,←pow_add]
     congr 1
     omega
   rw [he] at hfinal
   simp only [Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_one,dotProduct,Rat.cast_sum,
     abs_mul,abs_of_pos (by positivity : (0:ℝ) < n+1)]
   exact hh.trans (by simpa only [mul_assoc] using hfinal)

end EdgeSublinearMWIS.Main.ConvexTools

namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools
 theorem hyperplaneApproximation_height {n t : ℕ} (us cs : SignedVector) (u c : Fin n → ℚ)
     (hu : RepresentsVector us (rationalVector u)) (hc : RepresentsVector cs (rationalVector c))
     (hU : ∀ i,|(u i:ℝ)| ≤ 1) (hC : ∀ i,|(c i:ℝ)| ≤ (2:ℝ)^(t+2)) :
     ∃ (P : Fin (n+1) → ℤ) (q : ℤ),q≠0 ∧
       RepresentsVector (hyperplaneApproximation (n,(us,cs))).1 (WithLp.toLp 2 (fun i => (P i:ℝ))) ∧
       (∀ i,(P i).natAbs ≤ 2^(approximationExponent n+t+2*n+4)) ∧
       (∀ i : Fin (n+1),|(q:ℝ)*((Fin.snoc (α:=fun _ : Fin (n+1) => ℚ) u ((n+1:ℚ)*(u ⬝ᵥ c)) i:ℚ):ℝ)-(P i:ℝ)| ≤ (2:ℝ)⁻¹^(n+4)) := by
   obtain ⟨P,q,hq,hrep,hD,hval,herr,hbound⟩ := hyperplaneApproximation_correct us cs u c hu hc
   refine ⟨P,q,hq,hrep,?_,herr⟩
   have hβ := hyperplane_beta_bound u c hU hC
   have h1 : (1:ℝ) ≤ (2:ℝ)^(t+2*n+3) := one_le_pow₀ (by norm_num)
   have hδ : (2:ℝ)⁻¹^(n+4) ≤ 1 := pow_le_one₀ (by positivity) (by norm_num)
   intro i
   have ha : |((Fin.snoc (α:=fun _ : Fin (n+1) => ℚ) u ((n+1:ℚ)*(u ⬝ᵥ c)) i:ℚ):ℝ)| ≤ (2:ℝ)^(t+2*n+3) := by
     refine Fin.lastCases ?_ (fun k => ?_) i
     · simpa only [Fin.snoc_last] using hβ
     · simpa only [Fin.snoc_castSucc] using (hU k).trans h1
   have hh := integer_approximation_height (P i) q _ (approximationExponent n) (t+2*n+3) ha hbound ((herr i).trans hδ)
   convert hh using 1 <;> congr 1 <;> omega
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

 
 

 theorem normalizedColumn_self {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef) (k : Fin n) :
     normalizedColumn B k k=1 := by
   exact div_self (ne_of_gt (hB.diag_pos (i:=k)))
 theorem normalizedColumn_bounded {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef) (k : Fin n)
     (hmax : ∀ i,B i i≤ B k k) : ∀ i,|normalizedColumn B k i|≤1 := by
   intro i
   rw [normalizedColumn,abs_div,abs_of_pos (hB.diag_pos (i:=k))]
   exact (div_le_one (hB.diag_pos (i:=k))).mpr
     (positive_matrix_entry_bound B hB (B k k) (le_of_lt (hB.diag_pos (i:=k))) hmax i k)

 theorem normalizedColumn_thin {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef)
     (c : Fin n → ℝ) (k : Fin n) (D : ℝ) (hD : 0< D) (hlarge : D^2≤ B k k) :
     ∀ x∈inverseEllipsoid B c,|normalizedColumn B k ⬝ᵥ (x-c)|≤ D⁻¹ := by
   intro x hx
   let v := x-c
   have hq : v ⬝ᵥ (B *ᵥ v)≤1 := hx
   have hc := positive_matrix_cauchy B hB (Pi.single k 1) v
   simp only [dotProduct,mulVec,Pi.single_apply] at hc
   simp only [ite_mul,mul_ite,zero_mul,one_mul,mul_zero,mul_one,Finset.sum_ite_eq',Finset.mem_univ,if_true] at hc
   have hsym : B.IsSymm := isHermitian_iff_isSymm.mp hB.isHermitian
   have he : normalizedColumn B k ⬝ᵥ v=(∑ j,B k j*v j)/(B k k) := by
     simp only [normalizedColumn,dotProduct]
     rw [Finset.sum_div]
     apply Finset.sum_congr rfl
     intro j hj
     rw [hsym.apply j k]
     ring
   have hp : 0< B k k := hB.diag_pos
   have hmul := mul_le_mul_of_nonneg_left hq (le_of_lt hp)
   have hbound : (∑ j,B k j*v j)^2≤ B k k := hc.trans (by simpa only [dotProduct,mulVec,mul_one] using hmul)
   rw [he]
   have htarget : |(∑ j,B k j*v j)/(B k k)| *D≤1 := by
     rw [abs_div,abs_of_pos hp]
     have hs : |∑ j,B k j*v j|^2*D^2≤(B k k)^2 := by
       rw [sq_abs]
       have h1 := mul_le_mul_of_nonneg_left hlarge (sq_nonneg |∑ j,B k j*v j|)
       rw [sq_abs] at h1
       have h2 := mul_le_mul_of_nonneg_right hbound (le_of_lt hp)
       nlinarith
     have hroot : |∑ j,B k j*v j| *D≤ B k k :=
       (sq_le_sq₀ (by positivity) (le_of_lt hp)).mp (by nlinarith only [hs])
     have heq : |∑ j,B k j*v j| / B k k * D=(|∑ j,B k j*v j| *D)/B k k := by ring
     rw [heq]
     exact (div_le_one hp).mpr hroot
   rw [←one_div]
   exact (le_div_iff₀ hD).mpr htarget

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

omit [DecidableEq ι] in
theorem quadratic_parallelogram (A : Matrix ι ι ℝ) (u v : ι → ℝ) :
    (u + v) ⬝ᵥ (A *ᵥ (u + v)) + (u - v) ⬝ᵥ (A *ᵥ (u - v)) =
      2 * (u ⬝ᵥ (A *ᵥ u)) + 2 * (v ⬝ᵥ (A *ᵥ v)) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub]
  ring

/-- If a whole ball lies in an ellipsoid, its radius bounds the inverse shape
form. The ball and ellipsoid may have different centers. -/
theorem inverse_form_bound_of_ball {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (z c : ι → ℝ) (r : ℝ) (hr : 0 < r)
    (hball : ∀ e : ι → ℝ, e ⬝ᵥ e ≤ r ^ 2 →
      (z + e - c) ⬝ᵥ (A⁻¹ *ᵥ (z + e - c)) ≤ 1) :
    ∀ u : ι → ℝ, u ⬝ᵥ (A⁻¹ *ᵥ u) ≤ (r ^ 2)⁻¹ * (u ⬝ᵥ u) := by
  intro u
  by_cases hu : u = 0
  · simp [hu]
  have hnorm : 0 < u ⬝ᵥ u := by
    simpa using (dotProduct_star_self_pos_iff (v := u)).mpr hu
  let t := r / Real.sqrt (u ⬝ᵥ u)
  let e := t • u
  have ht : 0 < t := div_pos hr (Real.sqrt_pos.mpr hnorm)
  have hsq : (Real.sqrt (u ⬝ᵥ u)) ^ 2 = u ⬝ᵥ u := Real.sq_sqrt hnorm.le
  have he : e ⬝ᵥ e = r ^ 2 := by
    simp only [e, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    dsimp [t]
    field_simp
    nlinarith
  have hp := hball e he.le
  have hm := hball (-e) (by simpa using he.le)
  have hbase : 0 ≤ (z - c) ⬝ᵥ (A⁻¹ *ᵥ (z - c)) :=
    hA.inv.posSemidef.dotProduct_mulVec_nonneg _
  have hid := quadratic_parallelogram A⁻¹ (z - c) e
  have hp' : ((z - c) + e) ⬝ᵥ (A⁻¹ *ᵥ ((z - c) + e)) ≤ 1 := by
    have heq : (z - c) + e = z + e - c := by abel_nf
    rw [heq]
    exact hp
  have hm' : ((z - c) - e) ⬝ᵥ (A⁻¹ *ᵥ ((z - c) - e)) ≤ 1 := by
    have heq : (z - c) - e = z + -e - c := by abel_nf
    rw [heq]
    exact hm
  have hqe : e ⬝ᵥ (A⁻¹ *ᵥ e) ≤ 1 := by linarith
  have hqe' : t ^ 2 * (u ⬝ᵥ (A⁻¹ *ᵥ u)) ≤ 1 := by
    simpa only [e, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, ← mul_assoc, ← pow_two] using hqe
  have htform : t ^ 2 = r ^ 2 / (u ⬝ᵥ u) := by
    dsimp [t]
    rw [div_pow, hsq]
  rw [htform, div_mul_eq_mul_div] at hqe'
  have hscale : r ^ 2 * (u ⬝ᵥ (A⁻¹ *ᵥ u)) ≤ u ⬝ᵥ u :=
    (div_le_one hnorm).mp hqe'
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by simpa [mul_comm] using hscale)

/-- Containing a ball forces the determinant proxy used by the algorithm to
be at least the radius to the dimension. -/
theorem sqrt_det_lower_bound_of_ball {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (z c : ι → ℝ) (r : ℝ) (hr : 0 < r)
    (hball : ∀ e : ι → ℝ, e ⬝ᵥ e ≤ r ^ 2 →
      (z + e - c) ⬝ᵥ (A⁻¹ *ᵥ (z + e - c)) ≤ 1) :
    r ^ Fintype.card ι ≤ Real.sqrt A.det := by
  have hbound := inverse_form_bound_of_ball hA z c r hr hball
  have hdet := det_le_pow_of_form_bound hA.inv.posSemidef ((r ^ 2)⁻¹) hbound
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, inv_pow] at hdet
  have ha := hA.det_pos
  have hrpow : 0 < (r ^ 2) ^ Fintype.card ι := pow_pos (sq_pos_of_pos hr) _
  have hd : (r ^ 2) ^ Fintype.card ι ≤ A.det := (inv_le_inv₀ ha hrpow).mp hdet
  have hs := Real.sq_sqrt ha.le
  have hsr := Real.sqrt_nonneg A.det
  have hrr : (r ^ Fintype.card ι) ^ 2 = (r ^ 2) ^ Fintype.card ι := by ring
  nlinarith [pow_nonneg hr.le (Fintype.card ι)]

end EdgeSublinearMWIS.Main.GLS.EllipsoidBall
end

-- Solutions.EllipsoidLargeInverseDiagonal
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.EllipsoidMath

 theorem inverse_diag_large {n S : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
     (k : Fin n) (hmax : ∀ i,A⁻¹ i i≤ A⁻¹ k k)
     (hsmall : Real.sqrt A.det<(((2:ℝ)^(S+n+1))⁻¹)^n) :
     ((2:ℝ)^S)^2< A⁻¹ k k := by
   by_contra! hle
   let L : ℝ := ((2:ℝ)^S)^2
   let r : ℝ := ((2:ℝ)^(S+n+1))⁻¹
   have hL : 0≤ L := by positivity
   have hdiag : ∀ i,A⁻¹ i i≤ L := fun i => (hmax i).trans hle
   have hentry := positive_matrix_entry_bound A⁻¹ hA.inv L hL hdiag
   have hquad := GLS.EllipsoidRounding.quadratic_error_bound A⁻¹ L hL hentry
   have hcoef : (n:ℝ)*L*r^2≤1 := by
     have hn : (n:ℝ)≤(2:ℝ)^n := by exact_mod_cast (Nat.le_of_lt n.lt_two_pow_self)
     have hpow : (2:ℝ)^n≤(2:ℝ)^(2*n+2) := pow_le_pow_right₀ (by norm_num) (by omega)
     have h1 : (n:ℝ)≤(2:ℝ)^(2*n+2) := hn.trans hpow
     have hbound : (n:ℝ)*((2:ℝ)^S)^2≤((2:ℝ)^(S+n+1))^2 := by
       have hm := mul_le_mul_of_nonneg_right h1 (sq_nonneg ((2:ℝ)^S))
       have he : (2:ℝ)^(2*n+2)*((2:ℝ)^S)^2=((2:ℝ)^(S+n+1))^2 := by
         rw [←pow_mul,←pow_mul,←pow_add]
         congr 1
         ring
       simpa only [he] using hm
     dsimp only [L,r]
     rw [inv_pow,←div_eq_mul_inv]
     exact (div_le_one (by positivity)).mpr hbound
   have hball : ∀ e : Fin n → ℝ,e ⬝ᵥ e≤ r^2 → e ⬝ᵥ (A⁻¹ *ᵥ e)≤1 := by
     intro e he
     have hh := hquad e
     have hbound := (le_abs_self (e ⬝ᵥ (A⁻¹ *ᵥ e))).trans hh
     have hmul := mul_le_mul_of_nonneg_left he (by positivity : (0:ℝ)≤ n*L)
     exact hbound.trans (hmul.trans hcoef)
   have hlo := GLS.EllipsoidBall.sqrt_det_lower_bound_of_ball hA (0:Fin n → ℝ) (0:Fin n → ℝ) r
     (by dsimp [r]; positivity) (by intro e he; simpa only [zero_add,sub_zero] using hball e he)
   simp only [Fintype.card_fin] at hlo
   exact (not_lt_of_ge hlo) hsmall

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

 theorem ellipsoidThinDirection_correct {n S : ℕ} (hn : 0 < n) (bs : SignedMatrix)
     (A : Matrix (Fin n) (Fin n) ℚ) (hA : RepresentsMatrix bs A)
     (hp : (castMatrix A).PosDef)
     (hsmall : Real.sqrt (castMatrix A).det < (((2:ℝ)^(S+n+1))⁻¹)^n) :
     ∃ k : Fin n,(ellipsoidThinDirection bs).2=k.val ∧
       RepresentsVector (ellipsoidThinDirection bs).1
         (WithLp.toLp 2 (normalizedColumn ((castMatrix A)⁻¹) k)) ∧
       normalizedColumn ((castMatrix A)⁻¹) k k=1 ∧
       (∀ i,|normalizedColumn ((castMatrix A)⁻¹) k i| ≤ 1) ∧
       ∀ (c x : Fin n → ℝ),x∈inverseEllipsoid ((castMatrix A)⁻¹) c →
         |normalizedColumn ((castMatrix A)⁻¹) k ⬝ᵥ (x-c)| ≤ ((2:ℝ)^S)⁻¹ := by
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
   have hlarge := inverse_diag_large (castMatrix A) hp k hmaxR hsmall
   have he : rationalVector (fun i => A⁻¹ i k/A⁻¹ k k)=
       WithLp.toLp 2 (normalizedColumn ((castMatrix A)⁻¹) k) := by
     ext i
     change ((A⁻¹ i k/A⁻¹ k k:ℚ):ℝ)=_
     rw [Rat.cast_div]
     change (castMatrix A⁻¹) i k/(castMatrix A⁻¹) k k=_
     rw [hcast]; rfl
   rw [he] at hrep
   refine ⟨k,hk,hrep,normalizedColumn_self _ hp.inv k,
     normalizedColumn_bounded _ hp.inv k hmaxR,?_⟩
   intro c x hx
   exact normalizedColumn_thin _ hp.inv c k ((2:ℝ)^S) (by positivity) hlarge.le x hx

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

 
 
 theorem approximationExponent_mono {m n : ℕ} (h : m ≤ n) : approximationExponent m ≤ approximationExponent n := by
   dsimp [approximationExponent]
   gcongr
 theorem recoveryHeight_mono {m n : ℕ} (h : m ≤ n) : recoveryHeight m ≤ recoveryHeight n := by
   have h1 := approximationExponent_mono h
   have h2 := phaseBudget_mono h
   dsimp [recoveryHeight]
   omega
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

 theorem ellipsoidRecovery_height {n t : ℕ} (hn : 0 < n) (bs : SignedMatrix) (cs : SignedVector)
     (A : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ)
     (hA : RepresentsMatrix bs A) (hc : RepresentsVector cs (rationalVector c))
     (hp : (castMatrix A).PosDef) (hC : ∀ i,|(c i:ℝ)| ≤ (2:ℝ)^(t+2)) :
     ∃ P : Fin (n+1) → ℤ,
       RepresentsVector (ellipsoidRecovery (n,(bs,cs))).1 (WithLp.toLp 2 (fun i => (P i:ℝ))) ∧
       ∀ i,(P i).natAbs ≤ 2^(approximationExponent n+t+2*n+4) := by
   obtain ⟨k,hu,hU⟩ := ellipsoidThinDirection_rational hn bs A hA hp
   obtain ⟨P,q,hq,hrep,hheight,herr⟩ := hyperplaneApproximation_height _ cs _ c hu hc hU hC
   exact ⟨P,hrep,hheight⟩

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
 theorem affineLift_identity (N : ℕ) (z : Fin N → ℝ) :
     affineLift (1:Matrix (Fin N) (Fin N) ℚ) 0 z=z := by
   have he : ((1:Matrix (Fin N) (Fin N) ℚ).map (Rat.castHom ℝ))=(1:Matrix (Fin N) (Fin N) ℝ) := by
     ext i j
     simp [Matrix.one_apply,apply_ite]
   rw [affineLift,he,Matrix.one_mulVec]
   have hz : (fun i : Fin N => ((0:Fin N → ℚ) i:ℝ))=0 := by ext i; simp
   rw [hz,add_zero]

 
 
 theorem coreModel_initial (N : ℕ) (Orig : Finset (Fin N → Bool)) :
     CoreModel Orig (oracleInitial N).2 (1:Matrix (Fin N) (Fin N) ℚ) 0 Orig := by
   have hh := phaseInitial_correct N
   refine ⟨le_rfl,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,?_,phaseGeometry_initial N Orig,?_,fun h => h⟩
   · simpa only [affineHeight,Nat.sub_self,Nat.zero_mul] using ConvexTools.affine_integer_height_initial N
   · intro z hz
     rwa [affineLift_identity]
 theorem coreGeometry_initial (N : ℕ) (Orig : Finset (Fin N → Bool)) :
     CoreGeometry N Orig (oracleInitial N).2 := ⟨N,1,0,Orig,coreModel_initial N Orig⟩

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

 theorem phaseSplitCoefficients_correct {n : ℕ} (xs : SignedVector) (P : Fin (n+1) → ℤ)
     (hP : RepresentsVector xs (WithLp.toLp 2 (fun i => (P i:ℝ)))) :
     RepresentsVector (phaseSplitCoefficients (n,xs)).1 (rationalVector (fun i : Fin n => (P i.castSucc:ℚ))) ∧
       0 < value (phaseSplitCoefficients (n,xs)).2.2.2 ∧
       signedFractionValue (phaseSplitCoefficients (n,xs)).2=(P (Fin.last n):ℚ) := by
   have ht := represents_castSucc_take xs _ hP
   have hl := represents_lookup xs _ hP (Fin.last n) signedZero
   have he : (WithLp.toLp 2 (fun i : Fin n => (WithLp.toLp 2 (fun i => (P i:ℝ))) i.castSucc))=
       rationalVector (fun i : Fin n => (P i.castSucc:ℚ)) := by
     ext i; simp only [rationalVector,WithLp.ofLp_toLp,Rat.cast_intCast]
   rw [he] at ht
   refine ⟨ht,hl.1,?_⟩
   apply Rat.cast_injective (α:=ℝ)
   simpa only [phaseSplitCoefficients,Fin.val_last,Rat.cast_intCast,WithLp.ofLp_toLp] using hl.2

 theorem eliminationParameters_correct {n : ℕ} (ps : SignedVector) (ds : SignedWords)
     (p : Fin n → ℚ) (hps : RepresentsVector ps (rationalVector p)) (hp : p≠0) :
     ∃ j : Fin n,eliminationParameters (ps,ds)=(j.val,(ps,ds)) ∧ p j≠0 := by
   obtain ⟨hflag,j,hj,hpj⟩ := findNonzero_correct ps p hps hp
   exact ⟨j,by simp only [eliminationParameters,hj],hpj⟩

 theorem splitIntegerParameters_correct {n : ℕ} (xs : SignedVector) (P : Fin (n+1) → ℤ)
     (hP : RepresentsVector xs (WithLp.toLp 2 (fun i => (P i:ℝ))))
     (hp : (fun i : Fin n => P i.castSucc)≠0) :
     ∃ j : Fin n,
       eliminationParameters (phaseSplitCoefficients (n,xs))=(j.val,phaseSplitCoefficients (n,xs)) ∧
       P j.castSucc≠0 := by
   have hs := phaseSplitCoefficients_correct xs P hP
   have hq : (fun i : Fin n => (P i.castSucc:ℚ))≠0 := by
     intro hz
     apply hp
     funext i
     have hh := congrFun hz i
     change (P i.castSucc:ℚ)=0 at hh
     change P i.castSucc=0
     exact_mod_cast hh
   obtain ⟨j,hj,hpj⟩ := eliminationParameters_correct _ _ _ hs.1 hq
   refine ⟨j,hj,?_⟩
   intro hz; apply hpj; rw [hz,Int.cast_zero]

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

 theorem affineLift_elimination {N n : ℕ} (A : Matrix (Fin N) (Fin (n+1)) ℚ) (b : Fin N → ℚ)
     (p : Fin (n+1) → ℚ) (d : ℚ) (j : Fin (n+1)) (hp : p j≠0) (y : Fin n → ℝ) :
     affineLift (fun i => eliminatedRow (A i) p j) (fun i => eliminatedOffset (A i) p (b i) d j) y=
       affineLift A b (coordinateInsertion (fun i => (p i:ℝ)) (d:ℝ) j y) := by
   ext i
   exact eliminated_row_evaluation (A i) p (b i) d j hp y

 theorem coreModel_eliminate {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin (n+1)) ℚ) (b : Fin N → ℚ) (V : Finset (Fin (n+1) → Bool))
     (h : CoreModel Orig st A b V) (P : Fin ((n+1)+1) → ℤ)
     (hP : RepresentsVector (phaseRecoveredCoefficients st.2) (WithLp.toLp 2 (fun i => (P i:ℝ))))
     (hp : (fun i : Fin (n+1) => P i.castSucc)≠0)
     (hheight : ∀ i,(P i).natAbs ≤ 2^recoveryHeight N)
     (heq : ∀ z∈binaryHull V,∑ i,(P i.castSucc:ℝ)*z i=(P (Fin.last (n+1)):ℝ)) :
     ∃ j : Fin (n+1),CoreModel Orig (oracleDimensionReduction st)
       (fun i => eliminatedRow (A i) (fun k => (P k.castSucc:ℚ)) j)
       (fun i => eliminatedOffset (A i) (fun k => (P k.castSucc:ℚ)) (b i) (P (Fin.last (n+1)):ℚ) j)
       (projectedBinarySet V j) := by
   have hdim := phaseGeometry_dimension V st.2 h.phase
   let xs := phaseRecoveredCoefficients st.2
   let split := phaseSplitCoefficients (n+1,xs)
   have hs := phaseSplitCoefficients_correct xs P hP
   obtain ⟨j,hparams,hpj⟩ := splitIntegerParameters_correct xs P hP hp
   have hnormal : phaseNormalAndOffset st.2=split := by
     dsimp only [phaseNormalAndOffset]
     rw [hdim]
   have hparams' : phaseEliminationParameters st.2=(j.val,split) := by
     rw [phaseEliminationParameters,Function.comp_apply,hnormal]
     exact hparams
   have hpQ : (P j.castSucc:ℚ)≠0 := by exact_mod_cast hpj
   have hpR : (P j.castSucc:ℝ)≠0 := by exact_mod_cast hpj
   have hnew := canonicalAffineEliminate_correct st.1.1 st.1.2 split.1 split.2 A b
     (fun k => (P k.castSucc:ℚ)) (P (Fin.last (n+1)):ℚ) j hpQ h.affineRows h.affineOffsets hs.1 hs.2.1 hs.2.2
   have hAff : (oracleDimensionReduction st).1=canonicalAffineEliminate (st.1,(j.val,split)) := by
     simp only [oracleDimensionReduction,hparams']
   have hPhase : (oracleDimensionReduction st).2=phaseInitial n := by
     simp only [oracleDimensionReduction,hdim,Nat.add_sub_cancel]
   have hnewHeight := affine_integer_height_step A b h.height (fun k => P k.castSucc)
     (P (Fin.last (n+1))) (fun k => hheight k.castSucc) (hheight _) j hpj
   have hlevel : affineHeight N (n+1)+recoveryHeight N+1=affineHeight N n := by
     have horder := h.order
     have hsub : N-n=N-(n+1)+1 := by omega
     dsimp only [affineHeight]
     rw [hsub]
     ring
   rw [hlevel] at hnewHeight
   refine ⟨j,⟨by have hh := h.order; omega,?_,?_,?_,?_,hnewHeight,?_,?_,?_⟩⟩
   · rw [hAff]; exact hnew.1
   · rw [hAff]; exact hnew.2.1
   · rw [hAff]; exact hnew.2.2.1
   · rw [hAff]; exact hnew.2.2.2
   · rw [hPhase]; exact phaseGeometry_initial n (projectedBinarySet V j)
   · intro y hy
     rw [affineLift_elimination A b _ _ j hpQ]
     apply h.lifts
     apply insertion_projected_hull V (fun i => (P i.castSucc:ℝ)) (P (Fin.last (n+1)):ℝ) j hpR heq y hy
   · intro ho
     exact (h.nonempty ho).image (fun v i => v (j.succAbove i))

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

 theorem ellipsoidRecovery_correct {n : ℕ} (hn : 0 < n) (bs : SignedMatrix) (cs : SignedVector)
     (A : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ)
     (hA : RepresentsMatrix bs A) (hc : RepresentsVector cs (rationalVector c))
     (hp : (castMatrix A).PosDef)
     (hsmall : Real.sqrt (castMatrix A).det < (((2:ℝ)^(thinExponent n+n+1))⁻¹)^n)
     (V : Finset (Fin n → Bool))
     (hcontains : ∀ v∈V,(fun i => (if v i then 1 else 0)/(n+1:ℝ))∈
       inverseEllipsoid ((castMatrix A)⁻¹) (castVector c)) :
     ∃ P : Fin (n+1) → ℤ,
       RepresentsVector (ellipsoidRecovery (n,(bs,cs))).1 (WithLp.toLp 2 (fun i => (P i:ℝ))) ∧
       (fun i : Fin n => P i.castSucc)≠0 ∧
       ∀ z∈binaryHull V,∑ i,(P i.castSucc:ℝ)*z i=(P (Fin.last n):ℝ) := by
   obtain ⟨k,hk,hrep,hunit,hbounded,hthin⟩ := ellipsoidThinDirection_correct hn bs A hA hp hsmall
   let u : Fin n → ℚ := fun i => A⁻¹ i k/A⁻¹ k k
   have hu : RepresentsVector (ellipsoidRecoveryDirection (n,(bs,cs))) (rationalVector u) := by
     have hcast := castMatrix_inv A (castMatrix_unit A hp)
     have he : WithLp.toLp 2 (normalizedColumn ((castMatrix A)⁻¹) k)=rationalVector u := by
       ext i
       change _=((A⁻¹ i k/A⁻¹ k k:ℚ):ℝ)
       rw [Rat.cast_div]
       change _=(castMatrix A⁻¹) i k/(castMatrix A⁻¹) k k
       rw [hcast]; rfl
     rw [he] at hrep
     exact hrep
   have huReal : ∀ i,(u i:ℝ)=normalizedColumn ((castMatrix A)⁻¹) k i := by
     intro i
     change ((A⁻¹ i k/A⁻¹ k k:ℚ):ℝ)=_
     rw [Rat.cast_div]
     change (castMatrix A⁻¹) i k/(castMatrix A⁻¹) k k=_
     rw [castMatrix_inv A (castMatrix_unit A hp)]; rfl
   have huk : u k=1 := by
     apply Rat.cast_injective (α:=ℝ)
     simpa only [Rat.cast_one,huReal] using hunit
   have hthin' : ∀ v∈V,|∑ i,(u i:ℝ)*(if v i then 1 else 0)-
       (((n+1:ℚ)*(u ⬝ᵥ c):ℚ):ℝ)| ≤ (n+1:ℝ)/(2:ℝ)^thinExponent n := by
     intro v hv
     have hh := hthin (castVector c) (fun i => (if v i then 1 else 0)/(n+1:ℝ)) (hcontains v hv)
     have he : (∑ i,(u i:ℝ)*(if v i then 1 else 0))-(((n+1:ℚ)*(u ⬝ᵥ c):ℚ):ℝ)=
         (n+1:ℝ)*(normalizedColumn ((castMatrix A)⁻¹) k ⬝ᵥ
           ((fun i => (if v i then 1 else 0)/(n+1:ℝ))-castVector c)) := by
       simp only [Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_one,dotProduct,Rat.cast_sum,
         Pi.sub_apply,castVector,mul_sub,Finset.mul_sum,Finset.sum_sub_distrib]
       apply congrArg₂ (fun a b : ℝ => a-b) <;> apply Finset.sum_congr rfl <;> intro i hi <;> rw [huReal] <;> field_simp <;> ring
     rw [he,abs_mul,abs_of_pos (by positivity : (0:ℝ) < n+1)]
     have h := mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ) ≤ n+1)
     simpa only [div_eq_mul_inv] using h
   have hh := hyperplaneApproximation_recovers _ cs u c hu hc V k huk hthin'
   exact hh

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryScaledUnit
noncomputable section

open scoped Classical BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools

 theorem binary_scaled_unit {n : ℕ} (v : Fin n → Bool) :
     (fun i => (if v i then 1 else 0)/(n+1:ℝ)) ⬝ᵥ
       (fun i => (if v i then 1 else 0)/(n+1:ℝ)) ≤ 1 := by
   have hp : 0 < (n+1:ℝ) := by positivity
   have hterm : ∀ i : Fin n,((if v i then 1 else 0)/(n+1:ℝ))*
       ((if v i then 1 else 0)/(n+1:ℝ)) ≤ 1/(n+1:ℝ)^2 := by
     intro i
     cases hv : v i <;> simp only [hv,Bool.false_eq_true,if_false,if_true,zero_div,zero_mul]
     · positivity
     · exact le_of_eq (by field_simp [ne_of_gt hp])
   have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i hi => hterm i)
   change (∑ i,((if v i then 1 else 0)/(n+1:ℝ))*((if v i then 1 else 0)/(n+1:ℝ))) ≤ 1
   apply hh.trans
   simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←mul_div_assoc,mul_one]
   apply (div_le_one (by positivity)).mpr
   have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
   nlinarith

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

 theorem ellipsoid_phase_recovery {n : ℕ} (hn : 2 ≤ n) (vs : ℕ → SignedVector)
     (a : ℕ → Fin n → ℚ) (hv : ∀ k,RepresentsVector (vs k) (rationalVector (a k)))
     (ha : ∀ k,1 ≤ realVector (a k) ⬝ᵥ realVector (a k))
     (V : Finset (Fin n → Bool))
     (hcuts : ∀ j < thresholdSteps n (thinExponent n+n+1),∀ v∈V,
       realVector (a j) ⬝ᵥ ((fun i => (if v i then 1 else 0)/(n+1:ℝ))-
         realVector (centers n a 0 j)) ≤ 0) :
     let st := ellipsoidPrefix n vs (thresholdSteps n (thinExponent n+n+1))
     ∃ P : Fin (n+1) → ℤ,
       RepresentsVector (ellipsoidRecovery (n,st.2)).1 (WithLp.toLp 2 (fun i => (P i:ℝ))) ∧
       (fun i : Fin n => P i.castSucc)≠0 ∧
       ∀ z∈binaryHull V,∑ i,(P i.castSucc:ℝ)*z i=(P (Fin.last n):ℝ) := by
   let K := thresholdSteps n (thinExponent n+n+1)
   let st := ellipsoidPrefix n vs K
   have hs := ellipsoidPrefix_correct hn vs a hv ha K
   have hp := (shapes_invariant n hn a ha K).1
   have hsmall := shapes_below_threshold n hn a ha (thinExponent n+n+1)
   apply ellipsoidRecovery_correct (by omega) st.2.1 st.2.2 (shapes n a K) (centers n a 0 K) hs.2.1 hs.2.2.1 hp hsmall V
   intro v hvV
   have hz : realVector (0:Fin n → ℚ)=(0:Fin n → ℝ) := by ext i; simp [realVector]
   have hh := preserves_points_up_to n hn a ha 0
     (fun i => (if v i then 1 else 0)/(n+1:ℝ))
     (by simpa only [hz,sub_zero] using binary_scaled_unit v) K (fun j hj => hcuts j hj v hvV)
   exact hh

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

 theorem phaseGeometry_recovery_height {n : ℕ} (V : Finset (Fin n → Bool)) (st : EllipsoidPhaseState)
     (h : PhaseGeometry V st) (hn : 2 ≤ n) :
     ∃ P : Fin (n+1) → ℤ,
       RepresentsVector (phaseRecoveredCoefficients st) (WithLp.toLp 2 (fun i => (P i:ℝ))) ∧
       ∀ i,(P i).natAbs ≤ 2^recoveryHeight n := by
   cases h with
   | small hnsmall hs => omega
   | large hn vs a k hv ha hst hbudget hcuts =>
     have hs := ellipsoidPrefix_correct hn vs a hv ha k
     have hp := (shapes_invariant n hn a ha k).1
     obtain ⟨P,hrep,hheight⟩ := ellipsoidRecovery_height (by omega) _ _ (shapes n a k)
       (centers n a 0 k) hs.2.1 hs.2.2.1 hp (centers_magnitude n hn a ha k)
     refine ⟨P,?_,?_⟩
     · have hdata : phaseRecoveryInput st=(n,(ellipsoidPrefix n vs k).2) := by
         dsimp only [phaseRecoveryInput]
         rw [hst,hs.1]
       have hword : phaseRecoveredCoefficients st=(ellipsoidRecovery (n,(ellipsoidPrefix n vs k).2)).1 := by
         rw [phaseRecoveredCoefficients,Function.comp_apply,Function.comp_apply,hdata]
       rw [hword]
       exact hrep
     · intro i
       apply (hheight i).trans
       apply Nat.pow_le_pow_right (by omega)
       dsimp [recoveryHeight]
       omega
 theorem integer_representations_unique {n : ℕ} (xs : SignedVector) (P Q : Fin n → ℤ)
     (hP : RepresentsVector xs (WithLp.toLp 2 (fun i => (P i:ℝ))))
     (hQ : RepresentsVector xs (WithLp.toLp 2 (fun i => (Q i:ℝ)))) : P=Q := by
   have he := represents_unique hP hQ
   funext i
   have hh := congrArg (fun v : Vec n => v i) he
   change (P i:ℝ)=(Q i:ℝ) at hh
   exact_mod_cast hh

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

 theorem phaseGeometry_boundary_certificate {n : ℕ} (V : Finset (Fin n → Bool)) (st : EllipsoidPhaseState)
     (h : PhaseGeometry V st) (hn : 2 ≤ n) (hk : st.1.2=phaseBudget n) :
     ∃ P : Fin (n+1) → ℤ,
       RepresentsVector (phaseRecoveredCoefficients st) (WithLp.toLp 2 (fun i => (P i:ℝ))) ∧
       (fun i : Fin n => P i.castSucc)≠0 ∧
       ∀ z∈binaryHull V,∑ i,(P i.castSucc:ℝ)*z i=(P (Fin.last n):ℝ) := by
   cases h with
   | small hnsmall hs => omega
   | large hn vs a k hv ha hst hbudget hcuts =>
     have hmeta := (ellipsoidPrefix_correct hn vs a hv ha k).1
     have he : k=phaseBudget n := by
       have hh := congrArg Prod.snd hmeta
       rw [←hst] at hh
       simpa only [hh] using hk
     subst k
     obtain ⟨P,hrep,hp,heq⟩ := ellipsoid_phase_recovery hn vs a hv ha V hcuts
     refine ⟨P,?_,hp,heq⟩
     have hdata : phaseRecoveryInput st=(n,(ellipsoidPrefix n vs (phaseBudget n)).2) := by
       dsimp only [phaseRecoveryInput]
       rw [hst,hmeta]
     have hword : phaseRecoveredCoefficients st=(ellipsoidRecovery (n,(ellipsoidPrefix n vs (phaseBudget n)).2)).1 := by
       rw [phaseRecoveredCoefficients,Function.comp_apply,Function.comp_apply,hdata]
     rw [hword]
     exact hrep
 theorem coreGeometry_at_boundary {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig st A b V) (hn : 2 ≤ n) (hk : st.2.1.2=phaseBudget n) :
     CoreGeometry N Orig (oracleDimensionReduction st) := by
   obtain ⟨P,hP,hp,heq⟩ := phaseGeometry_boundary_certificate V st.2 h.phase hn hk
   obtain ⟨Q,hQ,hheight⟩ := phaseGeometry_recovery_height V st.2 h.phase hn
   have hPQ := integer_representations_unique _ P Q hP hQ
   have hheightN : ∀ i,(P i).natAbs ≤ 2^recoveryHeight N := by
     intro i
     rw [hPQ]
     exact (hheight i).trans (Nat.pow_le_pow_right (by omega) (recoveryHeight_mono h.order))
   cases n with
   | zero => omega
   | succ n =>
     obtain ⟨j,hnew⟩ := coreModel_eliminate Orig st A b V h P hP hp hheightN heq
     exact ⟨n,_,_,_,hnew⟩

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

 theorem coreGeometry_bigCut {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig st A b V) (hn : 2 ≤ n) (hk : st.2.1.2 < phaseBudget n)
     (ps : SignedVector) (p : Fin n → ℤ)
     (hp : RepresentsVector ps (rationalVector (fun i => (p i:ℚ)))) (hne : p≠0)
     (hcut : ∀ c : Fin n → ℚ,RepresentsVector st.2.2.2 (rationalVector c) →
       ∀ v∈V,realVector (fun i => (p i:ℚ)) ⬝ᵥ
         ((fun i => (if v i then 1 else 0)/(n+1:ℝ))-realVector c) ≤ 0) :
     CoreGeometry N Orig (oracleBigCut (ps,st)).2 := by
   have hm := coreModel_phase_advance Orig st A b V h hn hk ps p hp hne hcut
   have hd := phaseGeometry_dimension V st.2 h.phase
   have hnewdim : (oraclePhaseAdvance (ps,st)).2.1.1=n := by
     simpa only [phaseAdvance_counter] using hd
   have hnewcounter : (oraclePhaseAdvance (ps,st)).2.1.2=st.2.1.2+1 := rfl
   change CoreGeometry N Orig (oracleBoundary (oraclePhaseAdvance (ps,st)))
   unfold oracleBoundary
   split_ifs with hb
   · have hbound : phaseBudget n ≤ st.2.1.2+1 := by
       simpa only [oracleAtBoundary,hnewdim,hnewcounter,decide_eq_true_eq] using hb
     have he : (oraclePhaseAdvance (ps,st)).2.1.2=phaseBudget n := by rw [hnewcounter]; omega
     exact coreGeometry_at_boundary Orig _ A b V hm hn he
   · exact ⟨n,A,b,V,hm⟩

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
 theorem strict_cut_excludes {N : ℕ} (Orig : Finset (Fin N → Bool)) (cut : RationalHalfspace N)
     (y : Fin N → ℚ) (h : StrictOracleCut Orig cut y) :
     (fun i => (y i:ℝ))∉binaryHull Orig := by
   intro hy
   have hh := h.2 _ hy
   rw [←halfspace_eval_cast] at hh
   have hlt : (cut.bound:ℝ) < (cut.eval y:ℝ) := by exact_mod_cast h.1
   linarith
 theorem binary_vertex_mem {n : ℕ} (V : Finset (Fin n → Bool)) (v : Fin n → Bool) (hv : v∈V) :
     (fun i => if v i then (1:ℝ) else 0)∈binaryHull V := subset_convexHull ℝ _ ⟨v,hv,fun _ => rfl⟩
 theorem binaryHull_empty_of_not_nonempty {n : ℕ} (V : Finset (Fin n → Bool)) (hV : ¬V.Nonempty) :
     binaryHull V=∅ := by
   have he : V=∅ := Finset.not_nonempty_iff_eq_empty.mp hV
   simp [binaryHull,he]
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
 theorem model_cleared_zero_empty {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig st A b V) (cut : RationalHalfspace N) (c : Fin n → ℚ)
     (hc : StrictOracleCut Orig cut (A *ᵥ ((n+1:ℚ) • c)+b))
     (p : Fin n → ℤ) (T : ℝ) (hT : 0 < T)
     (hp : ∀ i,(p i:ℝ)=T*((cut.normal ᵥ* A) i:ℝ)) (hp0 : p=0) : binaryHull Orig=∅ := by
   apply binaryHull_empty_of_not_nonempty
   intro ho
   obtain ⟨v,hv⟩ := h.nonempty ho
   have hh := model_cleared_central Orig st A b V h cut c hc p T hT hp v hv
   rw [hp0] at hh
   have he : realVector (fun i : Fin n => ((0:Fin n → ℤ) i:ℚ))=0 := by ext i; simp [realVector]
   rw [he,zero_dotProduct] at hh
   exact (lt_irrefl _ hh)

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

 theorem scalarHalf_den : 0 < value scalarHalf.2.2 := by decide
 theorem scalarHalf_value : signedFractionValue scalarHalf=(1/2:ℚ) := by norm_num [scalarHalf,signedFractionValue,signedValue,value]
 theorem scalarHalf_canonical : signedReduced scalarHalf=scalarHalf := by decide
 theorem halfVector_rep (n : ℕ) :
     RepresentsVector (List.replicate n scalarHalf) (rationalVector (fun _ : Fin n => (1/2:ℚ))) := by
   refine ⟨fun _ => scalarHalf,by simp,fun _ => scalarHalf_den,?_⟩
   intro i
   rw [scalarHalf_value]
   rfl
 theorem halfVector_canonical (n : ℕ) : VectorCanonical (List.replicate n scalarHalf) := by
   intro s hs
   have he : s=scalarHalf := List.eq_of_mem_replicate hs
   rw [he]
   exact scalarHalf_canonical

 theorem model_small_zero_cut {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig st A b V) (hn : n ≤ 1) (cut : RationalHalfspace N)
     (hc : StrictOracleCut Orig cut b) : ∀ v∈V,∀ i,v i=true := by
   intro v hv i
   cases hi : v i with
   | true => rfl
   | false =>
     have hfalse : ∀ j,v j=false := by
       intro j
       have he : j=i := Fin.ext (by have hi' := i.isLt; have hj' := j.isLt; omega)
       rwa [he]
     have hz : (fun j => if v j then (1:ℝ) else 0)=(0:Fin n → ℝ) := by
       ext j; simp [hfalse j]
     have hvertex := h.lifts _ (binary_vertex_mem V v hv)
     rw [hz] at hvertex
     have hlift : affineLift A b (0:Fin n → ℝ)=(fun i => (b i:ℝ)) := by
       simp only [affineLift,Matrix.mulVec_zero,zero_add]
     rw [hlift] at hvertex
     exact (strict_cut_excludes Orig cut b hc hvertex).elim

 theorem coreModel_small_advance {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig st A b V) (hn : n ≤ 1) (hk : st.2.1.2=0)
     (cut : RationalHalfspace N) (hc : StrictOracleCut Orig cut b) (ps : SignedVector) :
     CoreModel Orig (oracleSmallAdvance (ps,st)).2 A b V := by
   have hsmall : SmallPhaseGeometry V st.2 := by
     cases h.phase with
     | small hn hs => exact hs
     | large hnlarge vs a k hv ha hst hbudget hcuts => omega
   have hdim := hsmall.1
   have hnewphase : PhaseGeometry V (oracleSmallAdvance (ps,st)).2.2 := by
     apply PhaseGeometry.small hn
     refine ⟨hdim,by norm_num [oracleSmallAdvance],hsmall.2.2.1,?_,?_,hsmall.2.2.2.2.2.1,?_⟩
     · simpa only [oracleSmallAdvance,hdim,Nat.cast_one] using halfVector_rep n
     · intro he
       exact model_small_zero_cut Orig st A b V h hn cut hc
     · simpa only [oracleSmallAdvance,hdim] using halfVector_canonical n
   exact ⟨h.order,h.affineRows,h.affineOffsets,h.rowsCanonical,h.offsetsCanonical,h.height,hnewphase,h.lifts,h.nonempty⟩

 theorem model_small_one_cut_empty {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig st A b V) (hn : n ≤ 1) (hvone : ∀ v∈V,∀ i,v i=true)
     (cut : RationalHalfspace N)
     (hc : StrictOracleCut Orig cut (A *ᵥ ((n+1:ℚ) • (fun _ : Fin n => (1/2:ℚ)))+b)) :
     binaryHull Orig=∅ := by
   apply binaryHull_empty_of_not_nonempty
   intro ho
   obtain ⟨v,hv⟩ := h.nonempty ho
   have hz : (fun i => if v i then (1:ℝ) else 0)=
       (n+1:ℝ) • realVector (fun _ : Fin n => (1/2:ℚ)) := by
     ext i
     have hn1 : n=1 := by have hh := i.isLt; omega
     change (if v i then (1:ℝ) else 0)=(n+1:ℝ)*((1/2:ℚ):ℝ)
     rw [hvone v hv i]
     norm_num [hn1]
   have hvertex := h.lifts _ (binary_vertex_mem V v hv)
   rw [hz,←affine_query_cast] at hvertex
   exact strict_cut_excludes Orig cut _ hc hvertex

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
 theorem phaseGeometry_small_center {n : ℕ} (V : Finset (Fin n → Bool)) (st : EllipsoidPhaseState)
     (h : PhaseGeometry V st) (hn : n ≤ 1) : SmallPhaseGeometry V st := by
   cases h with
   | small hn hs => exact hs
   | large hnlarge vs a k hv ha hst hk hcuts => omega
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

 theorem oraclePreparedCut_sound {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig st A b V) (hg : CounterGood N st)
     (cut : RationalHalfspace N) (c0 : Fin n → ℚ)
     (hc0 : RepresentsVector st.2.2.2 (rationalVector c0))
     (hc : StrictOracleCut Orig cut (A *ᵥ ((n+1:ℚ) • c0)+b))
     (ps : SignedVector) (p : Fin n → ℤ)
     (hp : RepresentsVector ps (rationalVector (fun i => (p i:ℚ))))
     (T : ℝ) (hT : 0 < T) (hscale : ∀ i,(p i:ℝ)=T*((cut.normal ᵥ* A) i:ℝ)) :
     CoreGeometry N Orig (oraclePreparedCut (ps,st)).2 ∧
       ((oraclePreparedCut (ps,st)).1=true → binaryHull Orig=∅) := by
   have hdim := phaseGeometry_dimension V st.2 h.phase
   have hcounter : st.2.1.2 < phaseBudget n := by simpa only [hdim] using hg.2.1
   have hfalseBig : (oracleBigCut (ps,st)).1=false := rfl
   have hfalseSmall : (oracleSmallAdvance (ps,st)).1=false := rfl
   unfold oraclePreparedCut
   split_ifs with hflag
   · have hNZ : (findNonzero ps).1=true := hflag
     have hpQ := (findNonzero_true_iff ps _ hp).mp hNZ
     have hpInt := (integer_cast_vector_ne_zero p).mp hpQ
     unfold oracleNonzeroCut
     split_ifs with hsmall
     · have hn : n ≤ 1 := by simpa only [oracleSmall,hdim,decide_eq_true_eq] using hsmall
       have hs := phaseGeometry_small_center V st.2 h.phase hn
       unfold oracleSmallCut
       split_ifs with hfirst
       · have hk0 : st.2.1.2=0 := by simpa only [oracleSmallFirst,decide_eq_true_eq] using hfirst
         have hcent : RepresentsVector st.2.2.2 (rationalVector (fun _ : Fin n => (0:ℚ))) := by
           simpa only [hk0,Nat.cast_zero,zero_div] using hs.2.2.2.1
         have hcEq : c0=(0:Fin n → ℚ) := by
           have he := represents_rational_unique _ _ _ hc0 hcent
           funext i
           exact congrFun he i
         have hc' : StrictOracleCut Orig cut b := by
           simpa only [hcEq,smul_zero,Matrix.mulVec_zero,zero_add] using hc
         have hm := coreModel_small_advance Orig st A b V h hn hk0 cut hc' ps
         refine ⟨⟨n,A,b,V,hm⟩,?_⟩
         intro hh
         rw [hfalseSmall] at hh
         contradiction
       · have hk1 : st.2.1.2=1 := by
           have hn0 : ¬st.2.1.2=0 := by simpa only [oracleSmallFirst,decide_eq_true_eq] using hfirst
           have hkbound := hs.2.1
           omega
         have hcent : RepresentsVector st.2.2.2 (rationalVector (fun _ : Fin n => (1/2:ℚ))) := by
           simpa only [hk1,Nat.cast_one] using hs.2.2.2.1
         have hcEq := represents_rational_unique _ _ _ hc0 hcent
         have hc' : StrictOracleCut Orig cut (A *ᵥ ((n+1:ℚ) • (fun _ : Fin n => (1/2:ℚ)))+b) := by rwa [hcEq] at hc
         have hempty := model_small_one_cut_empty Orig st A b V h hn (hs.2.2.2.2.1 hk1) cut hc'
         exact ⟨⟨n,A,b,V,h⟩,fun _ => hempty⟩
     · have hn : 2 ≤ n := by
         have hh : ¬n ≤ 1 := by simpa only [oracleSmall,hdim,decide_eq_true_eq] using hsmall
         omega
       have hcut : ∀ c : Fin n → ℚ,RepresentsVector st.2.2.2 (rationalVector c) →
           ∀ v∈V,realVector (fun i => (p i:ℚ)) ⬝ᵥ
             ((fun i => (if v i then 1 else 0)/(n+1:ℝ))-realVector c) ≤ 0 := by
         intro c hcrep v hv
         have he := represents_rational_unique _ _ _ hcrep hc0
         rw [he]
         exact (model_cleared_central Orig st A b V h cut c0 hc p T hT hscale v hv).le
       have hm := coreGeometry_bigCut Orig st A b V h hn hcounter ps p hp hpInt hcut
       refine ⟨hm,?_⟩
       intro hh
       rw [hfalseBig] at hh
       contradiction
   · have hp0 : p=0 := by
       by_contra hpNZ
       have hpQ := (integer_cast_vector_ne_zero p).mpr hpNZ
       have hh := (findNonzero_true_iff ps _ hp).mpr hpQ
       exact hflag hh
     have hempty := model_cleared_zero_empty Orig st A b V h cut c0 hc p T hT hscale hp0
     exact ⟨⟨n,A,b,V,h⟩,fun _ => hempty⟩

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

 theorem oracleActiveCut_sound {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig st.2 A b V) (hg : CounterGood N st.2)
     (cut : RationalHalfspace N) (as : SignedVector)
     (has : RepresentsVector as (rationalVector cut.normal)) (c0 : Fin n → ℚ)
     (hc0 : RepresentsVector st.2.2.2.2 (rationalVector c0))
     (hc : StrictOracleCut Orig cut (A *ᵥ ((n+1:ℚ) • c0)+b)) :
     CoreGeometry N Orig (oracleActiveCut (as,st)).2 ∧
       ((oracleActiveCut (as,st)).1=true → binaryHull Orig=∅) := by
   have hdim := phaseGeometry_dimension V st.2.2 h.phase
   obtain ⟨p,T,hT,hprep,hscale,hcore⟩ := oraclePrepareCut_correct as st.2 A cut.normal h.affineRows has hdim
   let ps := (oraclePrepareCut (as,st.2)).1
   have hps : RepresentsVector ps (rationalVector (fun i => (p i:ℚ))) := by
     rw [integer_rationalVector]
     exact hprep
   have hout := oraclePreparedCut_sound Orig st.2 A b V h hg cut c0 hc0 hc ps p hps T hT hscale
   have he : oraclePrepareCut (as,st.2)=(ps,st.2) := Prod.ext rfl hcore
   simpa only [oracleActiveCut,he] using hout

 theorem oracleCut_sound {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool))
     (h : CoreModel Orig st.2 A b V) (hg : CounterGood N st.2)
     (hsound : st.1=true → binaryHull Orig=∅)
     (cut : RationalHalfspace N) (as : SignedVector)
     (has : RepresentsVector as (rationalVector cut.normal)) (c0 : Fin n → ℚ)
     (hc0 : RepresentsVector st.2.2.2.2 (rationalVector c0))
     (hc : st.1=false → StrictOracleCut Orig cut (A *ᵥ ((n+1:ℚ) • c0)+b)) :
     CoreGeometry N Orig (oracleCut (as,st)).2 ∧
       ((oracleCut (as,st)).1=true → binaryHull Orig=∅) := by
   cases he : st.1 with
   | true =>
     rw [oracleCut_rejected as st he]
     exact ⟨⟨n,A,b,V,h⟩,hsound⟩
   | false =>
     have hh := oracleActiveCut_sound Orig st A b V h hg cut as has c0 hc0 (hc he)
     simpa only [oracleCut,he,Bool.false_eq_true,if_false] using hh

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

 
 theorem oracleTranscriptState_nil (N : ℕ) : oracleTranscriptState ([]:List (RationalHalfspace N))=oracleInitial N := rfl
 theorem oracleTranscriptState_append {N : ℕ} (cuts : List (RationalHalfspace N)) (cut : RationalHalfspace N) :
     oracleTranscriptState (cuts++[cut])=oracleCut (rationalWords cut.normal,oracleTranscriptState cuts) := by
   simp only [oracleTranscriptState,oracleExecute,List.map_append,List.map_singleton,List.foldl_append,List.foldl_cons,List.foldl_nil]
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

 theorem admissible_prefix_sound {N : ℕ} (E : Program) (hE : ImplementsBinaryOracle E)
     (bound : Polynomial ℕ) (Orig : Finset (Fin N → Bool))
     (qs : List (Fin N → ℚ)) (cuts : List (RationalHalfspace N))
     (hadm : AdmissibleDialogue E bound N Orig qs cuts) (i : ℕ) (hi : i ≤ cuts.length) :
     CoreGeometry N Orig (oracleTranscriptState (cuts.take i)).2 ∧
       ((oracleTranscriptState (cuts.take i)).1=true → binaryHull Orig=∅) := by
   induction i with
   | zero =>
     simp only [List.take_zero,oracleTranscriptState_nil]
     refine ⟨coreGeometry_initial N Orig,?_⟩
     intro he
     change Bool.false=true at he
     contradiction
   | succ i ih =>
     have hil : i < cuts.length := by omega
     obtain ⟨hgeom,hsound⟩ := ih (by omega)
     obtain ⟨n,A,b,V,hmodel⟩ := hgeom
     let st := oracleTranscriptState (cuts.take i)
     have htake : cuts.take (i+1)=cuts.take i++[cuts[i]] := List.take_succ_eq_append_getElem hil
     rw [htake,oracleTranscriptState_append]
     cases hs : st.1 with
     | true =>
       rw [oracleCut_rejected _ st hs]
       exact ⟨⟨n,A,b,V,hmodel⟩,hsound⟩
     | false =>
       obtain ⟨c0,hc0⟩ := phaseGeometry_center V st.2.2 hmodel.phase
       have hc := dialogue_query_is_native E hE bound Orig qs cuts hadm i hil A b V hmodel hs c0 hc0
       have hg := transcript_counter_live (cuts.take i) hs
       exact oracleCut_sound Orig st A b V hmodel hg hsound cuts[i] _ (rationalWords_rep cuts[i].normal) c0 hc0 (fun _ => hc)
 

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

theorem solution {N : ℕ} (E : Program) (hE : ImplementsBinaryOracle E)
    (bound : Polynomial ℕ) (Orig : Finset (Fin N → Bool))
    (qs : List (Fin N → ℚ)) (cuts : List (RationalHalfspace N))
    (hadm : AdmissibleDialogue E bound N Orig qs cuts) (i : ℕ) (hi : i ≤ cuts.length) :
    CoreGeometry N Orig (oracleTranscriptState (cuts.take i)).2 ∧
      ((oracleTranscriptState (cuts.take i)).1=true → binaryHull Orig=∅) := by
  exact admissible_prefix_sound E hE bound Orig qs cuts hadm i hi
