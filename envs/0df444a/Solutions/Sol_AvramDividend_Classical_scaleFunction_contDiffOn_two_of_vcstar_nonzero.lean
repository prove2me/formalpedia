-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_contDiffOn_two_of_vcstar_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T06:14:33.781978+00:00
-- url     : https://prove2.me/submissions/a9f26791-d2be-409d-8647-6c9f34412435

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

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
  have hbelow :
      ∀ z ∈ Ioo 0 (cstar W).toReal, vcstar W z = k * W z := by
    intro z hz
    have hz0 : ¬ z < 0 := not_lt_of_ge (le_of_lt hz.1)
    have hza : z ≤ (cstar W).toReal := le_of_lt hz.2
    simp [vcstar, barrierValue, hz0, hza, hfactor z]
  have hscaled :
      ContDiffOn ℝ 2 (fun z => k⁻¹ * vcstar W z)
        (Ioo 0 (cstar W).toReal) := by
    simpa only [smul_eq_mul] using
      (ContDiffOn.const_smul k⁻¹ hvc)
  refine hscaled.congr ?_
  intro z hz
  rw [hbelow z hz]
  simp [hk']
