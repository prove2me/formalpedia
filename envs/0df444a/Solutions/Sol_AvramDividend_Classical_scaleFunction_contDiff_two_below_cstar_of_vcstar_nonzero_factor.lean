-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_contDiff_two_below_cstar_of_vcstar_nonzero_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T11:43:05.764001+00:00
-- url     : https://prove2.me/submissions/a7810878-604f-4e04-885c-06168e7fe074

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (W : ℝ → ℝ)
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0) :
    ContDiffOn ℝ 2 W (Ioo 0 (cstar W).toReal) := by
  let k : ℝ := divE (1 : ℝ) (scaleDeriv W (cstar W).toReal)
  have hk' : k ≠ 0 := by
    simpa [k] using hk
  have hfactor (z : ℝ) :
      divE (W z) (scaleDeriv W (cstar W).toReal) = k * W z := by
    dsimp [k]
    by_cases htop : scaleDeriv W (cstar W).toReal = ⊤
    · simp [divE, htop]
    · simp [divE, htop, div_eq_mul_inv, mul_comm]
  have hvc_eq (z : ℝ) (hz : z ∈ Ioo 0 (cstar W).toReal) :
      vcstar W z = k * W z := by
    have hz0 : ¬ z < 0 := not_lt.mpr (le_of_lt hz.1)
    have hza : z ≤ (cstar W).toReal := le_of_lt hz.2
    simp [vcstar, barrierValue, hz0, hza, hfactor]
  have hscaled :
      ContDiffOn ℝ 2 (fun z => k * W z) (Ioo 0 (cstar W).toReal) := by
    exact hvc.congr (fun z hz => (hvc_eq z hz).symm)
  have hrecovered :
      ContDiffOn ℝ 2 (fun z : ℝ => k⁻¹ • (k * W z))
        (Ioo 0 (cstar W).toReal) :=
    hscaled.const_smul (k⁻¹)
  exact hrecovered.congr (fun z hz => by
    simp [smul_eq_mul, hk'])
