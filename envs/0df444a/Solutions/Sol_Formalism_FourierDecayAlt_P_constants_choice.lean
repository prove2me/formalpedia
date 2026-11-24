-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.constants_choice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:58.536731+00:00
-- url     : https://prove2.me/submissions/1fcce65e-d011-4c4f-80cf-e7ed6c88e64e

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
private theorem le_constants_proof : Formalism.FourierDecayAlt.LE.Constants := by
  intro k r N C₂ C₆ I hN hC₂ hC₆ hI
  have hNr : (r:ℝ) + 1 ≤ N := by exact_mod_cast hN
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have hQ0 : (0:ℝ) ≤ ((r:ℝ) + 1) ^ 2 := by positivity
  have hkNQ : (0:ℝ) ≤ (k:ℝ) * N * ((r:ℝ) + 1) ^ 2 := by positivity
  have hN2Q : (0:ℝ) ≤ (N:ℝ) ^ 2 * ((r:ℝ) + 1) ^ 2 := by positivity
  have h26 : C₂ ≤ C₆ := by linarith
  have hC6 : 0 ≤ C₆ := by linarith
  have e1 : C₂ * ((k:ℝ) * N * ((r:ℝ) + 1) ^ 2) ≤ C₆ * ((k:ℝ) * N * ((r:ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_right h26 hkNQ
  have e2 : (6 * C₂) * ((N:ℝ) ^ 2 * ((r:ℝ) + 1) ^ 2) ≤ C₆ * ((N:ℝ) ^ 2 * ((r:ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_right hC₆ hN2Q
  have e3 : ((r:ℝ) + 1) * (N * ((r:ℝ) + 1) ^ 2) ≤ (N:ℝ) * (N * ((r:ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_right hNr (by positivity)
  have e4 : C₂ * (((r:ℝ) + 1) * (N * ((r:ℝ) + 1) ^ 2)) ≤ C₂ * ((N:ℝ) * (N * ((r:ℝ) + 1) ^ 2)) :=
    mul_le_mul_of_nonneg_left e3 hC₂.le
  have e5 : 0 ≤ C₂ * ((N:ℝ) * ((r:ℝ) + 1) ^ 2) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · push_cast
    nlinarith
  · nlinarith
end Formalism.FourierDecayAlt.P.LEx2
end

set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LE.Constants := Formalism.FourierDecayAlt.P.LEx2.le_constants_proof
end Formalism.FourierDecayAlt.P
