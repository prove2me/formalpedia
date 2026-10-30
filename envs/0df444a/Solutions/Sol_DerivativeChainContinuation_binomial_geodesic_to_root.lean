-- Prove2me | solution 1 for DerivativeChainContinuation.binomial_geodesic_to_root
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:45:51.073024+00:00
-- url     : https://prove2.me/submissions/ef866c29-12fb-4334-bd54-af9deee2782f

import Mathlib
import Definitions.Def_DerivativeChainContinuation_BinomialRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial



theorem binomialPoly_eval_root (q r : ℕ) (c b : ℂ) (hb : b^q= -c) :
    (binomialPoly q r c).eval b=0 := by
  simp only [binomialPoly,eval_add,eval_pow,eval_X,eval_mul,eval_C,pow_add,hb]
  ring

theorem binomialPoly_derivative_succ (q r : ℕ) (c : ℂ) :
    (binomialPoly q (r+1) c).derivative =
      C (q+r+1 : ℂ)*binomialPoly q r (c*((r+1 : ℕ):ℂ)/(q+r+1 : ℂ)) := by
  have hn : (q+r+1 : ℂ) ≠ 0 := by exact_mod_cast (show q+r+1 ≠ 0 by omega)
  have he : (q+r+1 : ℂ)*(c*((r+1 : ℕ):ℂ)/(q+r+1 : ℂ))=c*((r+1 : ℕ):ℂ) := by
    field_simp
  simp only [binomialPoly,derivative_add,derivative_X_pow,derivative_C_mul,
    show q+(r+1)-1=q+r by omega, show r+1-1=r by omega]
  simp only [mul_add,← mul_assoc,← C_mul,he]
  simp only [Nat.cast_add,Nat.cast_one,map_add,map_one]
  ring

theorem binomialPoly_base_root_zero (q k : ℕ) (c : ℂ) (hk : 0 < k) (hkq : k < q) :
    (derivative^[k] (binomialPoly q 0 c)).eval 0=0 := by
  have he : derivative^[k] ((X:Polynomial ℂ)^q+C c) =
      derivative^[k] ((X:Polynomial ℂ)^q)+derivative^[k] (C c) := by
    simp only [← Module.End.pow_apply,map_add]
  simp only [binomialPoly,Nat.add_zero,pow_zero,mul_one,he,
    iterate_derivative_C hk,add_zero,iterate_derivative_X_pow_eq_C_mul,
    eval_mul,eval_C,eval_pow,eval_X]
  rw [zero_pow (by omega : q-k ≠ 0),mul_zero]

end DerivativeChainContinuation



set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace DerivativeChainContinuation
open Polynomial



end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (q r : ℕ) (hq : 2 ≤ q) (c b : ℂ) (hb : b^q= -c) :
    ∃ z : ℕ → ℂ, z 0=0 ∧ z (q+r-1)=b ∧
      (∀ i < q+r, (derivative^[q+r-(i+1)] (binomialPoly q r c)).eval (z i)=0) ∧
      (∀ i < q+r-1, ‖z (i+1)-z i‖ = ‖z (i+1)‖-‖z i‖) := by
  induction r generalizing c b with
  | zero =>
    let z : ℕ → ℂ := fun i => if i < q-1 then 0 else b
    refine ⟨z,?_,?_,?_,?_⟩
    · simp [z,show 0 < q-1 by omega]
    · simp [z]
    · intro i hi
      by_cases he : i < q-1
      · simp only [z,if_pos he,Nat.add_zero]
        exact binomialPoly_base_root_zero q (q-(i+1)) c (by omega) (by omega)
      · have heq : q+0-(i+1)=0 := by omega
        simp only [z,if_neg he,heq,Function.iterate_zero_apply]
        exact binomialPoly_eval_root q 0 c b hb
    · intro i hi
      have hi' : i < q-1 := by omega
      by_cases he : i+1 < q-1 <;> simp [z,he,hi']
  | succ r ih =>
    let ratio : ℝ := (r+1 : ℕ)/(q+r+1 : ℕ)
    have hr0 : 0 ≤ ratio := by dsimp [ratio]; positivity
    have hr1 : ratio ≤ 1 := by
      dsimp [ratio]
      apply (div_le_one (by positivity : (0:ℝ) < (q+r+1 : ℕ))).mpr
      exact_mod_cast (show r+1 ≤ q+r+1 by omega)
    let t := ratio^((q:ℝ)⁻¹)
    have ht0 : 0 ≤ t := Real.rpow_nonneg hr0 _
    have ht1 : t ≤ 1 := Real.rpow_le_one hr0 hr1 (by positivity)
    have htq : t^q=ratio := Real.rpow_inv_natCast_pow hr0 (by omega)
    let c' := c*((r+1 : ℕ):ℂ)/(q+r+1 : ℂ)
    let b' := (t:ℂ)*b
    have hb' : b'^q= -c' := by
      dsimp only [b',c']
      rw [mul_pow,← Complex.ofReal_pow,htq,hb]
      dsimp only [ratio]
      push_cast
      ring
    obtain ⟨f,hf0,hfend,hfroot,hfstep⟩ := ih c' b' hb'
    let z : ℕ → ℂ := fun i => if i < q+r then f i else b
    refine ⟨z,?_,?_,?_,?_⟩
    · simp [z,show 0 < q+r by omega,hf0]
    · simp [z,show q+Nat.succ r-1=q+r by omega]
    · intro i hi
      by_cases he : i < q+r
      · have hk : q+Nat.succ r-(i+1)=(q+r-(i+1))+1 := by omega
        simp only [z,if_pos he,hk,Function.iterate_succ_apply]
        rw [binomialPoly_derivative_succ,iterate_derivative_C_mul,eval_mul,hfroot i he,mul_zero]
      · have hk : q+Nat.succ r-(i+1)=0 := by omega
        simp only [z,if_neg he,hk,Function.iterate_zero_apply]
        exact binomialPoly_eval_root q (r+1) c b hb
    · intro i hi
      have hi' : i < q+r := by omega
      by_cases he : i+1 < q+r
      · simp only [z,if_pos he,if_pos hi']
        exact hfstep i (by omega)
      · have hieq : i=q+r-1 := by omega
        simp only [z]
        rw [if_neg he,if_pos hi',hieq,hfend]
        have hnorm : ‖b'‖=t*‖b‖ := by
          simp [b',norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht0]
        have heq : b-b'=((1-t:ℝ):ℂ)*b := by dsimp [b']; push_cast; ring
        rw [heq,hnorm,norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr ht1)]
        ring
