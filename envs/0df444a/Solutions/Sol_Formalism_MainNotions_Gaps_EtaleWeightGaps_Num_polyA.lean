-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.polyA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:53:07.843801+00:00
-- url     : https://prove2.me/submissions/5dd048c9-5c5a-489a-8a24-50c1648d1b40

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
theorem _root_.solution {Z PP tableDegreeThreeBase PO lk Dp : ℝ} (hZ : 10 ^ 60 ≤ Z) (hPP : Z ^ 12 ≤ PP) (hP0 : tableDegreeThreeBase ≤ 30 * Z)
    (hPO : PO ≤ 217 * Z ^ 2) (hl1 : 1 ≤ lk) (hl : lk ≤ 6 * Z) (hD : 1 ≤ Dp) :
    (2 * 0 + 1 / 2 + tableDegreeThreeBase * lk + 3 / 2 * (Z * lk + PO) ≤ PP) ∧
    (60 * 0 + 180 * (1 / 2) + 44 * (2 * 0 + 1 / 2 + tableDegreeThreeBase * lk + 3 / 2 * (Z * lk + PO)) + 22 * (2 * Z) ≤ PP ^ 2 * Dp) := by
  have hZ1 : (1 : ℝ) ≤ Z := le_trans (by norm_num) hZ
  have hZ0 : (0 : ℝ) ≤ Z := by linarith
  have hZZ : Z ≤ Z ^ 10 := by simpa using pow_le_pow_right₀ hZ1 (show 1 ≤ 10 by norm_num)
  have hZ10 : (10 : ℝ) ^ 60 ≤ Z ^ 10 := le_trans hZ hZZ
  have hZ12 : Z ^ 2 * 10 ^ 60 ≤ Z ^ 2 * Z ^ 10 := mul_le_mul_of_nonneg_left hZ10 (sq_nonneg Z)
  have e12 : Z ^ 2 * Z ^ 10 = Z ^ 12 := by ring
  have hZ2 : (1 : ℝ) ≤ Z ^ 2 := by nlinarith
  have a1 : tableDegreeThreeBase * lk ≤ 30 * Z * lk := mul_le_mul_of_nonneg_right hP0 (by linarith)
  have a2 : 30 * Z * lk ≤ 30 * Z * (6 * Z) := mul_le_mul_of_nonneg_left hl (by linarith)
  have a3 : Z * lk ≤ Z * (6 * Z) := mul_le_mul_of_nonneg_left hl hZ0
  have hE : 2 * 0 + 1 / 2 + tableDegreeThreeBase * lk + 3 / 2 * (Z * lk + PO) ≤ 600 * Z ^ 2 := by nlinarith
  have hP1 : (1 : ℝ) ≤ PP := by nlinarith
  have hPsq : PP * 1 ≤ PP * PP := mul_le_mul_of_nonneg_left hP1 (by linarith)
  have hPD : PP ^ 2 * 1 ≤ PP ^ 2 * Dp := mul_le_mul_of_nonneg_left hD (sq_nonneg PP)
  constructor
  · nlinarith
  · nlinarith
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
