-- Prove2me | solution 1 for D1Bound5.pairClosure_complete_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:50:48.356925+00:00
-- url     : https://prove2.me/submissions/a491a875-2914-4924-8565-327f893d04b3

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DescentAlgebra_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SquareTest_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_QuadInt_rootCandidate_complete
import Theorems.Thm_D1Bound5_full_ring_small_pair_descent
import Theorems.Thm_D1Bound5_mutate_reverse_canonical
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

/-- Norm descent and algebraic reversibility turn two finite checks into a
complete bounded pair-extension list in the actual full integer ring. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {tau nu : ℤ} (hd : 0 < discriminant tau nu)
    (e : QuadInt tau nu ≃+* 𝓞 K) (a b : QuadInt tau nu)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a*b+1 ≠ 0)
    (hroot : ∃ r0, r0*r0 = a*b+1)
    (hNa : a.norm ≤ 8) (hNb : b.norm ≤ 8)
    (bound : ℤ) (vertices : List (QuadInt tau nu))
    (hseeds : ∀ z, PairExtension a b z → z.norm ≤ 1089 → z ∈ vertices)
    (hclosed : ∀ z ∈ vertices, ∀ w,
      (w = pairMutationPlus a b z ∨ w = pairMutationMinus a b z) →
      w.norm ≤ bound → w ∈ vertices)
    (z : QuadInt tau nu) (hz : PairExtension a b z) (hNz : z.norm ≤ bound) :
    z ∈ vertices := by
  have hnorm (x : QuadInt tau nu) :
      ‖phi (e x : K)‖^2 = (x.norm : ℝ) := norm_sq_full_ring_equiv e phi x
  have hsmall (x : QuadInt tau nu) (hx : x.norm ≤ 8) :
      ‖phi (e x : K)‖ < 3 := by
    have hc : (x.norm : ℝ) ≤ 8 := by exact_mod_cast hx
    nlinarith only [hnorm x, hc, _root_.norm_nonneg (phi (e x : K))]
  have hmap (x r0 r s : QuadInt tau nu) :
      e (mutate a b x r0 r s) = mutate (e a) (e b) (e x) (e r0) (e r) (e s) := by
    simp only [mutate, map_add, map_mul, map_one, map_ofNat]
  have aux : ∀ n : ℕ, ∀ x : QuadInt tau nu,
      x.norm.toNat = n → PairExtension a b x → x.norm ≤ bound → x ∈ vertices := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hnx hx hNx
      by_cases hsmallx : x.norm ≤ 1089
      · exact hseeds x hx hsmallx
      · let r0 := rootCandidate (a*b+1)
        let r := rootCandidate (a*x+1)
        let s := rootCandidate (b*x+1)
        have h0 : r0*r0 = a*b+1 := rootCandidate_complete hd hroot
        have hr : r*r = a*x+1 := rootCandidate_complete hd hx.1
        have hs : s*s = b*x+1 := rootCandidate_complete hd hx.2
        have h0e : (e r0)^2 = e a*e b+1 := by
          simpa only [pow_two, map_mul, map_add, map_one] using congrArg e h0
        have hre : (e r)^2 = e a*e x+1 := by
          simpa only [pow_two, map_mul, map_add, map_one] using congrArg e hr
        have hse : (e s)^2 = e b*e x+1 := by
          simpa only [pow_two, map_mul, map_add, map_one] using congrArg e hs
        have hae : e a ≠ 0 := by
          intro h
          apply ha
          apply e.injective
          simpa only [map_zero] using h
        have hbe : e b ≠ 0 := by
          intro h
          apply hb
          apply e.injective
          simpa only [map_zero] using h
        have habe : e a*e b+1 ≠ 0 := by
          intro h
          apply hab
          apply e.injective
          simpa only [map_mul, map_add, map_one, map_zero] using h
        have h33 : 33 ≤ ‖phi (e x : K)‖ := by
          have hc : (1089 : ℝ) < (x.norm : ℝ) := by exact_mod_cast (lt_of_not_ge hsmallx)
          nlinarith only [hnorm x, hc, _root_.norm_nonneg (phi (e x : K))]
        obtain ⟨w, hw, ⟨rw, hrw⟩, ⟨sw, hsw⟩, _, _, hdec⟩ :=
          full_ring_small_pair_descent hK phi (e a) (e b) (e x)
            (e r0) (e r) (e s) hae hbe habe h0e hre hse
            (hsmall a hNa) (hsmall b hNb) h33
        let y := e.symm w
        have hy : PairExtension a b y := by
          constructor
          · refine ⟨e.symm rw, ?_⟩
            simpa only [pow_two, map_mul, map_add, map_one, RingEquiv.symm_apply_apply]
              using congrArg e.symm hrw
          · refine ⟨e.symm sw, ?_⟩
            simpa only [pow_two, map_mul, map_add, map_one, RingEquiv.symm_apply_apply]
              using congrArg e.symm hsw
        have hNdec : y.norm < x.norm := by
          have hyN : ‖phi (w : K)‖^2 = (y.norm : ℝ) := by
            simpa only [y, RingEquiv.apply_symm_apply] using hnorm y
          rw [hyN, hnorm x] at hdec
          exact_mod_cast hdec
        have hny : y.norm.toNat < n := by
          have hynonneg := QuadInt.norm_nonneg hd y
          have hxnonneg := QuadInt.norm_nonneg hd x
          omega
        have hymem := ih y.norm.toNat hny y rfl hy (le_trans (le_of_lt hNdec) hNx)
        have hreverse : x = pairMutationPlus a b y ∨ x = pairMutationMinus a b y := by
          rcases hw with hw | hw
          · have hyEq : y = mutate a b x r0 r s := by
              apply e.injective
              simpa only [y, RingEquiv.apply_symm_apply, hmap] using hw
            rw [hyEq]
            exact mutate_reverse_canonical hd a b x r0 r s h0 hr hs
          · have hyEq : y = mutate a b x r0 r (-s) := by
              apply e.injective
              simpa only [y, RingEquiv.apply_symm_apply, hmap, map_neg] using hw
            rw [hyEq]
            exact mutate_reverse_canonical hd a b x r0 r (-s) h0 hr
              (by simpa only [neg_mul_neg] using hs)
        exact hclosed y hymem x hreverse hNx
  exact aux z.norm.toNat z rfl hz hNz

end D1Bound5
end
