-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.arith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:45.148825+00:00
-- url     : https://prove2.me/submissions/448571c9-ad5b-4c24-9198-ddeceaf7a3de

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology MeasureTheory
noncomputable section
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
theorem _root_.solution (a b m : ℕ) {ε A : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / (2 * ((m : ℝ) + 2)))
    (hA : ((4 * (a + b) + 1 : ℕ) : ℝ) * ((m : ℝ) + 2) ^ 2 + 3 * ((m : ℝ) + 2) / ε ≤ A) :
    0 ≤ A ∧ ((4 * (m + 2) * (a + b) : ℕ) : ℝ) + ((m : ℝ) + 2) * ((m : ℝ) + 1) + 1 ≤ A ∧
      1 ≤ -ε * (((4 * (m + 2) * (a + b) : ℕ) : ℝ) + ((m : ℝ) + 2) * ((m : ℝ) + 1) - A) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hε1 : ε ≤ 1 := by
    refine hε.trans ?_
    rw [div_le_one (by positivity)]
    linarith
  set u : ℝ := 3 * ((m : ℝ) + 2) / ε with hu
  have hεu : ε * u = 3 * ((m : ℝ) + 2) := by
    rw [hu]
    field_simp
  have hu1 : 1 ≤ u := by
    rw [hu, le_div_iff₀ hε0]
    linarith
  have hab : (0 : ℝ) ≤ ((a : ℝ) + b) * ((m : ℝ) + 2) * ((m : ℝ) + 1) := by positivity
  have key : ((4 * (m + 2) * (a + b) : ℕ) : ℝ) + ((m : ℝ) + 2) * ((m : ℝ) + 1) + u ≤ A := by
    refine le_trans ?_ hA
    push_cast
    nlinarith
  have hE0 : (0 : ℝ) ≤ ((4 * (m + 2) * (a + b) : ℕ) : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, by linarith, ?_⟩
  · have : (0 : ℝ) ≤ ((m : ℝ) + 2) * ((m : ℝ) + 1) := by positivity
    linarith
  · have h1 : ε * u ≤ ε * (A - ((4 * (m + 2) * (a + b) : ℕ) : ℝ) - ((m : ℝ) + 2) * ((m : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) hε0.le
    nlinarith
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
