-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordNormLpLemmas.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:39:42.071523+00:00
-- url     : https://prove2.me/submissions/463650b0-0f2f-4624-8591-71eabf6703ae

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialDegreeExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialTheoremCorollary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordNormLpLemmas
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas Formalism.FourierDecayAlt.P.RealWeightedForms
  Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion
open scoped Matrix
namespace Formalism.FourierDecayAlt.P.WordNormLpLemmas
theorem _root_.solution (a b Q W N N' T c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hQ : 0 < Q) (hW : 0 < W)
    (hN : 0 < N) (hN' : 0 < N') (hT : 0 ≤ T) (hc : 0 ≤ c) (hNT : N * N' / Q ≤ T ^ 2) :
    c * Real.sqrt (a * b / Q) / W ≤ c * T * ((a / (N * W) + b / (N' * W)) / 2) := by
  have hA : 0 ≤ a / (N * W) := by positivity
  have hB : 0 ≤ b / (N' * W) := by positivity
  have e : a * b / Q = W ^ 2 * ((a / (N * W)) * (b / (N' * W))) * (N * N' / Q) := by
    field_simp
  have hAB : (a / (N * W)) * (b / (N' * W)) ≤ ((a / (N * W) + b / (N' * W)) / 2) ^ 2 := by
    nlinarith [sq_nonneg (a / (N * W) - b / (N' * W))]
  have h1 : a * b / Q ≤ (W * T * ((a / (N * W) + b / (N' * W)) / 2)) ^ 2 := by
    rw [e]
    calc W ^ 2 * ((a / (N * W)) * (b / (N' * W))) * (N * N' / Q)
        ≤ W ^ 2 * ((a / (N * W)) * (b / (N' * W))) * T ^ 2 :=
          mul_le_mul_of_nonneg_left hNT (by positivity)
      _ ≤ W ^ 2 * ((a / (N * W) + b / (N' * W)) / 2) ^ 2 * T ^ 2 := by gcongr
      _ = (W * T * ((a / (N * W) + b / (N' * W)) / 2)) ^ 2 := by ring
  have h2 : Real.sqrt (a * b / Q) ≤ W * T * ((a / (N * W) + b / (N' * W)) / 2) :=
    (Real.sqrt_le_left (by positivity)).mpr h1
  calc c * Real.sqrt (a * b / Q) / W ≤ c * (W * T * ((a / (N * W) + b / (N' * W)) / 2)) / W := by
        gcongr
    _ = c * T * ((a / (N * W) + b / (N' * W)) / 2) := by field_simp
end Formalism.FourierDecayAlt.P.WordNormLpLemmas
