-- Prove2me | solution 1 for D1Bound5.first_pair_geometry_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:14.477295+00:00
-- url     : https://prove2.me/submissions/77bf5ccb-1ab1-4b89-aaa4-72a755d66333

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.GCongr
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_FirstPairGeometry_Definitions

section
namespace D1Bound5





/-- Actual complex distance geometry for all first-pair rows with S≥15.
The same b-s distance controls both the Vandermonde and the relabeled
N3 residual, so no independent worst-case replacement is introduced. -/
theorem _root_.solution (a b s : ℂ) (A1 B1 d1 : ℝ)
    (hb : b ≠ 0) (hBS : ‖b‖ ≤ ‖s‖) (hS15 : 15 ≤ ‖s‖)
    (hA1 : ‖a‖ ≤ A1) (hB1 : ‖b‖ ≤ B1)
    (hd1 : ‖a-b‖/‖b‖ ≤ d1) :
    let Q := ‖coherentVandermonde3 (![a,b,s] : Fin 3 → ℂ)‖/(‖b‖*‖s‖^2)
    Q ≤ d1*(1+A1/15)*(1+B1/15) ∧
      Q^2*firstPairPhi b s ≤
        (‖a-b‖^2/‖b‖^2)*(1+A1/15)^2*(1+B1/15)^8 := by
  let B := ‖b‖
  let S := ‖s‖
  let x := ‖a-b‖/B
  let y := ‖a-s‖/S
  let z := ‖b-s‖/S
  let v := B/S
  let U := 1+A1/15
  let V := 1+B1/15
  have hB : 0 < B := norm_pos_iff.mpr hb
  have hS : 0 < S := by change 15 ≤ S at hS15; linarith only [hS15]
  have hA10 : 0 ≤ A1 := (norm_nonneg a).trans hA1
  have hB10 : 0 ≤ B1 := (norm_nonneg b).trans hB1
  have hU : 0 < U := by dsimp [U]; positivity
  have hV1 : 1 ≤ V := by
    dsimp [V]
    have hnonneg : 0 ≤ B1/15 := div_nonneg hB10 (by norm_num)
    linarith only [hnonneg]
  have hV : 0 < V := by linarith only [hV1]
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hd : 0 ≤ d1 := hx.trans hd1
  have hratioA : ‖a‖/S ≤ A1/15 := by
    apply (div_le_div_iff₀ hS (by norm_num : (0 : ℝ) < 15)).2
    have hh := mul_le_mul_of_nonneg_left hS15 hA10
    nlinarith only [hh,hA1]
  have hratioB : B/S ≤ B1/15 := by
    apply (div_le_div_iff₀ hS (by norm_num : (0 : ℝ) < 15)).2
    have hh := mul_le_mul_of_nonneg_left hS15 hB10
    nlinarith only [hh,hB1]
  have hyU : y ≤ U := by
    calc
      y ≤ (‖a‖+S)/S := div_le_div_of_nonneg_right (norm_sub_le a s) hS.le
      _ = 1+‖a‖/S := by field_simp [hS.ne']; ring
      _ ≤ U := add_le_add (le_refl 1) hratioA
  have hzV : z ≤ V := by
    calc
      z ≤ (B+S)/S := div_le_div_of_nonneg_right (norm_sub_le b s) hS.le
      _ = 1+B/S := by field_simp [hS.ne']; ring
      _ ≤ V := add_le_add (le_refl 1) hratioB
  have hv1 : v ≤ 1 := by
    apply (div_le_one hS).2
    exact hBS
  have hphi : firstPairPhi b s ≤ V^6 := by
    change max (z^6) (v*z^5) ≤ V^6
    apply max_le
    · gcongr
    · calc
        v*z^5 ≤ 1*V^5 := mul_le_mul hv1 (by gcongr) (pow_nonneg hz 5) (by norm_num)
        _ = V^5 := one_mul _
        _ ≤ V^6 := pow_le_pow_right₀ hV1 (by decide)
  have hq : ‖coherentVandermonde3 (![a,b,s] : Fin 3 → ℂ)‖/(B*S^2) = x*y*z := by
    change ‖(a-b)*(a-s)*(b-s)‖/(B*S^2) = x*y*z
    rw [norm_mul,norm_mul]
    dsimp [x,y,z]
    field_simp [hB.ne',hS.ne']
    <;> ring
  rw [hq]
  constructor
  · change x*y*z ≤ d1*U*V
    gcongr
  · have hqbound : (x*y*z)^2 ≤ x^2*U^2*V^2 := by
      have hh : x*y*z ≤ x*U*V := by gcongr
      have hh2 : (x*y*z)^2 ≤ (x*U*V)^2 := by gcongr
      simpa only [mul_pow] using hh2
    have hp := mul_le_mul hqbound hphi (by unfold firstPairPhi; positivity) (by positivity)
    calc
      (x*y*z)^2*firstPairPhi b s ≤ (x^2*U^2*V^2)*V^6 := hp
      _ = (‖a-b‖^2/B^2)*U^2*V^8 := by
        dsimp [x]
        field_simp [hB.ne']
        <;> ring

end D1Bound5
end
