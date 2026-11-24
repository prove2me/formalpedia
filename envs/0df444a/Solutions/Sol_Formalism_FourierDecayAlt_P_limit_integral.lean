-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.limit_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:36.668902+00:00
-- url     : https://prove2.me/submissions/5eb4dfe8-42aa-495e-a4b4-25c1127ba4ca

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_scalePi
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_card_UT
import Theorems.Thm_Formalism_FourierDecayAlt_P_limit_matrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.StandardCharacterExists
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.LimitIntegral := by
  intro n β z hz V _ _ _ Φ
  set μ := muPi β (UT (n + 1)) with hμ
  set F : (UT (n + 1) → ℂ) → V := fun y => psi β (superSum (strictUpper y) / z) •
          Φ (wMat (n + 1) * (z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) + strictUpper y)) with hF
  have hS := scalePi β z (UT (n + 1)) hz
  have hemb : MeasurableEmbedding (fun v : UT (n + 1) → ℂ => z • v) := measurableEmbedding_const_smul₀ hz
  have h1 : ∫ y, F y ∂(Measure.map (fun v : UT (n + 1) → ℂ => z • v) μ) = ∫ v, F (z • v) ∂μ :=
    hemb.integral_map F
  have h2 : ∀ v : UT (n + 1) → ℂ, F (z • v) =
      psi β (superSum (upper v)) • Φ (ptLong (n + 1) z * upper v) := by
    intro v
    obtain ⟨e1, e2⟩ := limit_matrix n z hz (z • v)
    rw [smul_smul, inv_mul_cancel₀ hz, one_smul] at e1 e2
    simp only [hF]
    rw [e1, e2]
  rw [hS, integral_smul_nnreal_measure] at h1
  simp only [h2] at h1
  have hcard : 2 * Fintype.card (UT (n + 1)) = (n + 1) * n := by
    rw [card_UT, mul_comm]
    simpa using Finset.sum_range_id_mul_two (n + 1)
  rw [hcard] at h1
  unfold OmLong
  rw [← h1]
  have hpos : (0 : ℝ) < ‖z‖ ^ ((n + 1) * n) := by positivity
  rw [NNReal.smul_def, Real.coe_toNNReal _ (by positivity), ← Complex.coe_smul, smul_smul,
    ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_smul]
end Formalism.FourierDecayAlt.P
