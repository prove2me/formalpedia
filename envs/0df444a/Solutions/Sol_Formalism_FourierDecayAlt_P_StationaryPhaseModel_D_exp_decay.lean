-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_exp_decay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:35.059903+00:00
-- url     : https://prove2.me/submissions/5d687770-419e-4981-a706-c081f6b133d9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
noncomputable section
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    (1 + s) ^ (2 * n) * Real.exp (-s ^ 2) ≤ 2 ^ n * n.factorial * Real.exp 1 := by
  have h1 : (1 + s) ^ 2 ≤ 2 * (1 + s ^ 2) := by nlinarith [sq_nonneg (1 - s)]
  have h2 : (1 + s ^ 2) ^ n / n.factorial ≤ Real.exp (1 + s ^ 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) n
  have h3 : (1 + s ^ 2) ^ n ≤ n.factorial * Real.exp (1 + s ^ 2) := by
    rw [div_le_iff₀ (by positivity)] at h2
    linarith
  calc (1 + s) ^ (2 * n) * Real.exp (-s ^ 2) = ((1 + s) ^ 2) ^ n * Real.exp (-s ^ 2) := by rw [pow_mul]
    _ ≤ (2 * (1 + s ^ 2)) ^ n * Real.exp (-s ^ 2) := by gcongr
    _ = 2 ^ n * (1 + s ^ 2) ^ n * Real.exp (-s ^ 2) := by rw [mul_pow]
    _ ≤ 2 ^ n * (n.factorial * Real.exp (1 + s ^ 2)) * Real.exp (-s ^ 2) := by gcongr
    _ = 2 ^ n * n.factorial * (Real.exp (1 + s ^ 2) * Real.exp (-s ^ 2)) := by ring
    _ = 2 ^ n * n.factorial * Real.exp 1 := by rw [← Real.exp_add]; congr 2; ring
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
