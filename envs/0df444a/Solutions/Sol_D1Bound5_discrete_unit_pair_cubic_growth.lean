-- Prove2me | solution 1 for D1Bound5.discrete_unit_pair_cubic_growth
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:22:21.908621+00:00
-- url     : https://prove2.me/submissions/64c09e6c-7ce4-475e-ab30-cff6561c7570

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_exists_sign_root_perturbation
import Theorems.Thm_D1Bound5_unit_pair_cancellation_ne_zero
import Theorems.Thm_D1Bound5_unit_pair_cancellation_norm
import Theorems.Thm_D1Bound5_unit_pair_cubic_numeric

section
namespace D1Bound5

/-- The unit-pair root perturbations have a uniform rational margin.
Only the triangle inequalities for c+d and cd+1 are used. -/
theorem unit_pair_cubic_root_margin (C D Z W : ℝ)
    (hC : 9 ≤ C) (hCD : C ≤ D) (hW : W ≤ C+D)
    (hZ : C*D ≤ Z^2+1) : W < (1-(7/8 : ℝ)^2)*Z^2 := by
  have hD : 9 ≤ D := hC.trans hCD
  have hprod := mul_nonneg (sub_nonneg.mpr hC)
    (show 0 ≤ D by linarith only [hD])
  nlinarith only [hC,hCD,hD,hW,hZ,hprod]



end D1Bound5
end

section
open scoped NumberField
open Module

namespace D1Bound5





private theorem exists_unit_pair_integral_sign
    {R : Type*} [CommRing R] (f : R →+* ℂ) (u z : R) (W : ℝ)
    (hz : f z ≠ 0) (hW : 0 < W)
    (herr : ‖(f u)^2-(f z)^2‖ ≤ W)
    (hgap : W < (1-(7/8 : ℝ)^2)*‖f z‖^2) :
    ∃ U : R, (U = u ∨ U = -u) ∧ (15/8 : ℝ)*‖f z‖*‖f U-f z‖ < W := by
  obtain ⟨v,hv,hnear⟩ := exists_sign_root_perturbation
    (f u) (f z) (7/8) W hz (by norm_num) hW herr hgap
  norm_num at hnear
  rcases hv with rfl | rfl
  · exact ⟨u,Or.inl rfl,hnear⟩
  · exact ⟨-u,Or.inr rfl,by simpa only [map_neg] using hnear⟩

/-- The unit cubic gap in any discrete complex ring image. Both signs
are selected among the original ring roots; the lower bound on the
nonzero second-order form is derived from discreteness. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (hdiscrete : ∀ x : R, x ≠ 0 → 1 ≤ ‖f x‖)
    (c d z u v : R) (hC : 9 ≤ ‖f c‖) (hCD : ‖f c‖ ≤ ‖f d‖)
    (hneq : f c+f d ≠ 0)
    (hz : z^2 = c*d+1) (hu : u^2 = (c+1)*(d+1))
    (hv : v^2 = (1-c)*(1-d)) : ‖f c‖^3/2 < ‖f d‖ := by
  have hzC : (f z)^2 = f c*f d+1 := by
    simpa only [map_pow,map_mul,map_add,map_one] using congrArg f hz
  have huC : (f u)^2 = (f z)^2+(f c+f d) := by
    have h := congrArg f hu
    simp only [map_pow,map_mul,map_add,map_one] at h
    rw [h,hzC]
    ring
  have hvC : (f v)^2 = (f z)^2-(f c+f d) := by
    have h := congrArg f hv
    simp only [map_pow,map_mul,map_sub,map_one] at h
    rw [h,hzC]
    ring
  have hZ : ‖f c‖*‖f d‖ ≤ ‖f z‖^2+1 := by
    have hid : f c*f d = (f z)^2-1 := by rw [hzC]; ring
    have h := norm_sub_le ((f z)^2) (1 : ℂ)
    rw [← hid,norm_mul] at h
    simpa only [norm_pow,norm_one] using h
  have hD : 9 ≤ ‖f d‖ := hC.trans hCD
  have hCD81 : 81 ≤ ‖f c‖*‖f d‖ := by
    have hp := mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hD)
    nlinarith only [hp,hC,hD]
  have hZ0 : 0 < ‖f z‖ := by
    by_contra hbad
    have hn : ‖f z‖ = 0 := le_antisymm (le_of_not_gt hbad) (norm_nonneg _)
    nlinarith only [hZ,hCD81,hn]
  have hW0 : 0 < ‖f c+f d‖ := norm_pos_iff.mpr hneq
  have hW := norm_add_le (f c) (f d)
  have hgap := unit_pair_cubic_root_margin ‖f c‖ ‖f d‖ ‖f z‖ ‖f c+f d‖
    hC hCD hW hZ
  have huErr : ‖(f u)^2-(f z)^2‖ ≤ ‖f c+f d‖ := by rw [huC]; simp
  have hvErr : ‖(f v)^2-(f z)^2‖ ≤ ‖f c+f d‖ := by
    rw [hvC, show (f z)^2-(f c+f d)-(f z)^2 = -(f c+f d) by ring,
      norm_neg]
  obtain ⟨U,hU,hUnear⟩ := exists_unit_pair_integral_sign f u z ‖f c+f d‖
    (norm_pos_iff.mp hZ0) hW0 huErr hgap
  obtain ⟨V,hV,hVnear⟩ := exists_unit_pair_integral_sign f v z ‖f c+f d‖
    (norm_pos_iff.mp hZ0) hW0 hvErr hgap
  have hU2 : (f U)^2 = (f z)^2+(f c+f d) := by
    rcases hU with rfl | rfl
    · exact huC
    · simpa only [map_neg,neg_sq] using huC
  have hV2 : (f V)^2 = (f z)^2-(f c+f d) := by
    rcases hV with rfl | rfl
    · exact hvC
    · simpa only [map_neg,neg_sq] using hvC
  let L : R := U+V-2*z
  have hLimage : f L = f U+f V-2*f z := by
    simp only [L,map_sub,map_add,map_mul,map_ofNat]
  have hLn : L ≠ 0 := by
    intro h
    have hz0 : f U+f V-2*f z = 0 := by rw [← hLimage,h,map_zero]
    exact unit_pair_cancellation_ne_zero (f U) (f V) (f z) (f c+f d) hU2 hV2 hneq hz0
  have hL : 1 ≤ ‖f U+f V-2*f z‖ := by
    rw [← hLimage]
    exact hdiscrete L hLn
  exact unit_pair_cubic_numeric ‖f c‖ ‖f d‖ ‖f z‖ ‖f c+f d‖
    ‖f U-f z‖ ‖f V-f z‖ ‖f U+f V-2*f z‖
    hC hCD hZ0 hW0 (norm_nonneg _) (norm_nonneg _) hL hW hZ hUnear hVnear
    (unit_pair_cancellation_norm (f U) (f V) (f z) (f c+f d) hU2 hV2)





end D1Bound5
end
