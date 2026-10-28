-- Prove2me | solution 1 for D1Bound5.full_ring_finitePDetFactor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:58:24.580513+00:00
-- url     : https://prove2.me/submissions/4d9ee229-9b7a-425d-8176-a63ddd5554e9

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePIntegralRows_Definitions
import Definitions.Def_D1Bound5_FinitePMatrix_Definitions
import Theorems.Thm_D1Bound5_one_le_norm_integer

section
open scoped NumberField
open Module

namespace D1Bound5





/-- The potential zero-leading-coefficient case has no hidden rank loss:
if both determinant factors vanish, the two first anchors coincide. -/
theorem finiteP_factor_identity {R : Type*} [CommRing R] (a b s : R) :
    (a-b)^2 = 4*finitePLeadingFactor a b s-(6*s+a+b)*finitePLinearFactor a b s := by
  dsimp [finitePLeadingFactor,finitePLinearFactor]
  ring

@[simp] theorem map_finitePLeadingFactor {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b s : R) :
    f (finitePLeadingFactor a b s) = finitePLeadingFactor (f a) (f b) (f s) := by
  simp [finitePLeadingFactor, map_ofNat]



private theorem finitePLinearFactor_norm_le (a b s : ℂ)
    (hAB : ‖a‖ ≤ ‖b‖) (hBS : ‖b‖ ≤ ‖s‖) :
    ‖finitePLinearFactor a b s‖ ≤ 4*‖s‖ := by
  calc
    _ ≤ ‖2*s-a‖+‖b‖ := norm_sub_le _ _
    _ ≤ (‖2*s‖+‖a‖)+‖b‖ := add_le_add (norm_sub_le _ _) le_rfl
    _ = 2*‖s‖+‖a‖+‖b‖ := by norm_num [norm_mul]
    _ ≤ _ := by linarith only [hAB,hBS]

/-- Actual integral arithmetic rules out a zero determinant factor. A
nonzero leading factor is an algebraic integer of norm at least one; a
zero leading factor is excluded by the exact identity above. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ) (a b s c : 𝓞 K)
    (hs : s ≠ 0) (hab : a ≠ b)
    (hAB : ‖phi (a : K)‖ ≤ ‖phi (b : K)‖)
    (hBS : ‖phi (b : K)‖ ≤ ‖phi (s : K)‖)
    (hC : 200*‖phi (s : K)‖ ≤ ‖phi (c : K)‖) :
    finitePDetFactor (phi (a : K)) (phi (b : K)) (phi (s : K)) (phi (c : K)) ≠ 0 := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hs0 : f s ≠ 0 := by
    intro h
    apply hs
    exact hf (by simpa only [map_zero] using h)
  have hS : 0 < ‖f s‖ := norm_pos_iff.mpr hs0
  have hab0 : f a ≠ f b := fun h => hab (hf h)
  change ‖f a‖ ≤ ‖f b‖ at hAB
  change ‖f b‖ ≤ ‖f s‖ at hBS
  change 200*‖f s‖ ≤ ‖f c‖ at hC
  change finitePDetFactor (f a) (f b) (f s) (f c) ≠ 0
  intro hzero
  have hfactor : 7*finitePLinearFactor (f a) (f b) (f s)+
      6*f c*finitePLeadingFactor (f a) (f b) (f s) = 0 := by
    simpa only [finitePDetFactor,finitePLeadingFactor,finitePLinearFactor] using hzero
  by_cases hW : finitePLeadingFactor a b s = 0
  · have hW' : finitePLeadingFactor (f a) (f b) (f s) = 0 := by
      rw [← map_finitePLeadingFactor f a b s,hW,map_zero]
    have ht : finitePLinearFactor (f a) (f b) (f s) = 0 := by
      rw [hW',mul_zero,add_zero] at hfactor
      exact (mul_eq_zero.mp hfactor).resolve_left (by norm_num)
    have hid := finiteP_factor_identity (f a) (f b) (f s)
    rw [hW',ht,mul_zero,mul_zero,sub_zero] at hid
    have hd : f a-f b = 0 := by
      have hh : (f a-f b)*(f a-f b) = 0 := by simpa only [pow_two] using hid
      rcases mul_eq_zero.mp hh with h | h <;> exact h
    exact hab0 (sub_eq_zero.mp hd)
  · have hW1 : 1 ≤ ‖finitePLeadingFactor (f a) (f b) (f s)‖ := by
      have h := one_le_norm_integer hK phi hW
      change 1 ≤ ‖f (finitePLeadingFactor a b s)‖ at h
      simpa only [map_finitePLeadingFactor] using h
    have heq : 6*f c*finitePLeadingFactor (f a) (f b) (f s) =
        -(7*finitePLinearFactor (f a) (f b) (f s)) := by
      linear_combination hfactor
    have hnorm := congrArg norm heq
    norm_num only [norm_mul,norm_neg,Complex.norm_ofNat] at hnorm
    have ht := finitePLinearFactor_norm_le (f a) (f b) (f s) hAB hBS
    have hmul := mul_le_mul_of_nonneg_left hW1 (show 0 ≤ 6*‖f c‖ by positivity)
    nlinarith only [hnorm,ht,hmul,hC,hS]









end D1Bound5
end
