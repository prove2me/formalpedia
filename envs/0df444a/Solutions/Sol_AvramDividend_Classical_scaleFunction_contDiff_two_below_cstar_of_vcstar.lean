-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_contDiff_two_below_cstar_of_vcstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T10:08:33.214919+00:00
-- url     : https://prove2.me/submissions/117e4fdf-a601-4d82-b503-d0be557e2b2c

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (W : ℝ → ℝ)
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0) :
    ContDiffOn ℝ 2 W (Ioo 0 (cstar W).toReal) := by
  let k : ℝ := divE (1 : ℝ) (scaleDeriv W (cstar W).toReal)
  have hfactor (z : ℝ) :
      divE (W z) (scaleDeriv W (cstar W).toReal) = k * W z := by
    dsimp [k]
    by_cases htop : scaleDeriv W (cstar W).toReal = ⊤
    · simp [divE, htop]
    · simp [divE, htop, div_eq_mul_inv, mul_comm]
  have hvc_factor :
      ∀ z ∈ Ioo (0 : ℝ) (cstar W).toReal,
        vcstar W z = k * W z := by
    intro z hz
    have hz0 : ¬ z < 0 := not_lt.mpr (le_of_lt hz.1)
    have hza : z ≤ (cstar W).toReal := le_of_lt hz.2
    simp [vcstar, barrierValue, hz0, hza, hfactor]
  have hscaled :
      ContDiffOn ℝ 2 (fun z => k⁻¹ * vcstar W z)
        (Ioo 0 (cstar W).toReal) := by
    simpa only [smul_eq_mul] using hvc.const_smul k⁻¹
  apply hscaled.congr
  intro z hz
  rw [hvc_factor z hz]
  field_simp [k, hk]
