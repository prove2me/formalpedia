-- Prove2me | solution 1 for Freiman.cert_cross_polynomial_from_field
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:58:32.915971+00:00
-- url     : https://prove2.me/submissions/32a6c170-433f-42ce-a3e7-8b02e6509495

import Definitions.Def_Freiman_certificates
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Fin

open Freiman
open scoped BigOperators
set_option maxRecDepth 4096
set_option maxHeartbeats 12000000

open scoped BigOperators


theorem solution :
    (∀ x y : CertField, certFieldVal (certFieldAdd x y) = certFieldVal x + certFieldVal y) →
    (∀ x y : CertField, certFieldVal (certFieldSub x y) = certFieldVal x - certFieldVal y) →
    (∀ x y : CertField, certFieldVal (certFieldMul x y) = certFieldVal x * certFieldVal y) →
    ∀ (l u : CertThreshold) (r s : ℝ), certPolyEval (certCrossPolynomial l u) r s = certThresholdNum l s * certThresholdDen u r - certThresholdNum u s * certThresholdDen l r := by
  intro ha hs hm l u r s
  have hone : certFieldVal ⟨1,0,0,0⟩ = 1 := by simp [certFieldVal]
  simp [certPolyEval, certCrossPolynomial, Fin.sum_univ_succ,
    certProductCoefficients, ha, hs, hm, certThresholdNum, certThresholdDen, hone]
  ring

#print axioms solution
