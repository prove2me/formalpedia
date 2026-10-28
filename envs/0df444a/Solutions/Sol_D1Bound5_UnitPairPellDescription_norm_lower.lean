-- Prove2me | solution 1 for D1Bound5.UnitPairPellDescription.norm_lower
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:50:22.408556+00:00
-- url     : https://prove2.me/submissions/931b1860-dc64-408b-a0d9-470f43e58db9

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FullRingUnitPairPell_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg

section
namespace D1Bound5









/-- Both actual Pell alternatives have modulus at least d+1. The imaginary
case uses the identity |2uv sqrt(-d)|²=4dv²(dv²+1). -/
theorem _root_.solution
    (d : ℤ) (w z : ℂ) (hd : 0 < d) (hw : w*w = -(d : ℂ))
    (h : UnitPairPellDescription d w z) : (d : ℝ)+1 ≤ ‖z‖ := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show (1:ℤ)≤d by omega)
  have hnormInt (n : ℤ) : ‖(n : ℂ)‖ = |(n : ℝ)| := by
    rw [← Complex.ofReal_intCast]
    simp only [Complex.norm_real,Real.norm_eq_abs]
  have hnw : ‖w‖^2 = (d : ℝ) := by
    have hh := congrArg norm hw
    rw [norm_mul,norm_neg,hnormInt,abs_of_pos hdR] at hh
    nlinarith only [hh]
  have hvone (v : ℤ) (hv : v ≠ 0) : (1 : ℝ) ≤ (v : ℝ)^2 := by
    have hh : (1 : ℤ) ≤ v^2 := by have := sq_pos_of_ne_zero hv; omega
    exact_mod_cast hh
  rcases h with hreal | himag
  · obtain ⟨u,v,hv,_,hplus | hminus⟩ := hreal
    all_goals
      have hprod : (d : ℝ) ≤ (d : ℝ)*(v : ℝ)^2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hvone v hv) hdR.le
      have hpos : 0 ≤ ((d*v^2+1 : ℤ) : ℝ) := by push_cast; linarith only [hprod,hdR]
    · rw [hplus,hnormInt,abs_of_nonneg hpos]
      push_cast
      linarith only [hprod]
    · rw [hminus,norm_neg,hnormInt,abs_of_nonneg hpos]
      push_cast
      linarith only [hprod]
  · obtain ⟨u,v,hv,hPell,hz⟩ := himag
    have hPellR : (u : ℝ)^2-(d : ℝ)*(v : ℝ)^2 = 1 := by exact_mod_cast hPell
    let t : ℝ := (d : ℝ)*(v : ℝ)^2
    have htd : (d : ℝ) ≤ t := by
      dsimp [t]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hvone v hv) hdR.le
    have ht0 : 0 ≤ t := hdR.le.trans htd
    have hnz : ‖z‖^2 = 4*t*(t+1) := by
      rw [hz,norm_mul,mul_pow,hnormInt,sq_abs,hnw]
      push_cast
      dsimp [t]
      linear_combination 4*(d : ℝ)*(v : ℝ)^2*hPellR
    have hbase : ((d : ℝ)+1)^2 ≤ 4*(d : ℝ)*((d : ℝ)+1) := by
      nlinarith [sq_nonneg (d : ℝ)]
    have hmono : 4*(d : ℝ)*((d : ℝ)+1) ≤ 4*t*(t+1) := by gcongr
    apply (sq_le_sq₀ (by positivity : 0 ≤ (d : ℝ)+1) (norm_nonneg z)).mp
    rw [hnz]
    exact hbase.trans hmono

open scoped NumberField
open Module



end D1Bound5
end
