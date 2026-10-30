-- Prove2me | solution 1 for DerivativeChainPrivate.quadrant_phase_forces_nonnegative_im
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T03:18:41.191301+00:00
-- url     : https://prove2.me/submissions/d308b50b-b939-4917-b145-7c096ddacae8

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem solution (β z : ℂ) (k : ℝ)
    (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) (hx : 0 < z.re) (hk : 0 < k)
    (hphase : (β / z).im = 2 * z.re * z.im * k) :
    0 ≤ z.im ∧ (β.im = 0 → z.im = 0) := by
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  have hD : 0 < Complex.normSq z := by
    rw [← Complex.sq_norm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hquot : (β / z).im * Complex.normSq z = β.im * z.re - β.re * z.im := by
    rw [Complex.div_im]
    field_simp
  rw [hphase] at hquot
  have hcoeff : 0 < 2 * z.re * k * Complex.normSq z + β.re := by positivity
  have hprod : (2 * z.re * k * Complex.normSq z + β.re) * z.im = β.im * z.re := by
    nlinarith only [hquot]
  refine ⟨nonneg_of_mul_nonneg_right (hprod.symm ▸ mul_nonneg hI hx.le) hcoeff, ?_⟩
  intro hzero
  rw [hzero,zero_mul] at hprod
  exact (mul_eq_zero.mp hprod).resolve_left hcoeff.ne'
