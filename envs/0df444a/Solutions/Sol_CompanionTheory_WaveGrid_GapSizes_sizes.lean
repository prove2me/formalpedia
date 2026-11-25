-- Prove2me | solution 1 for CompanionTheory.WaveGrid.GapSizes.sizes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:04:43.743204+00:00
-- url     : https://prove2.me/submissions/f556eaaf-6cae-47aa-8408-b8743a063fcc

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_GapSizes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.WaveGrid CompanionTheory.WaveGrid.GapSizes
namespace CompanionTheory.WaveGrid.GapSizes
theorem _root_.solution (Cg m N P s : ℝ) (hCg : 1000 ≤ Cg) (hm2 : 2 ≤ m) (hmN : m ≤ N) (hPN : N ^ 3 ≤ P) (hs : 1 ≤ s) :
    120 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P / 4 ∧ 125 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P / 32 := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN3 : (0 : ℝ) ≤ N ^ 3 := by positivity
  have hm2' : (4 : ℝ) ≤ m ^ 2 := by nlinarith
  have hm4e : m ^ 4 = m ^ 2 * m ^ 2 := by ring
  have hm4 : (16 : ℝ) ≤ m ^ 4 := by rw [hm4e]; nlinarith
  have hm4' : 4 * m ^ 2 ≤ m ^ 4 := by rw [hm4e]; nlinarith
  have hCg0 : (0 : ℝ) ≤ Cg := by linarith
  constructor
  · have a : (16 : ℝ) ≤ m ^ 4 * s := le_trans hm4 (le_mul_of_one_le_right (by positivity) hs)
    have b : (16000 : ℝ) ≤ Cg * (m ^ 4 * s) := by nlinarith
    have c : 16000 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P :=
      le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))
    linarith
  · have b : 4000 * m ^ 2 ≤ Cg * m ^ 4 := by nlinarith
    have c : 4000 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P :=
      le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))
    linarith
end CompanionTheory.WaveGrid.GapSizes
