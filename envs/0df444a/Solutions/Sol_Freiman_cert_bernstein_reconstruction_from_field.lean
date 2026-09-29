-- Prove2me | solution 1 for Freiman.cert_bernstein_reconstruction_from_field
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:58:52.964359+00:00
-- url     : https://prove2.me/submissions/2ce0d004-92eb-415f-b1b3-422946269d44

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
    (∀ (q : ℚ) (x : CertField), certFieldVal (certFieldScale q x) = (q:ℝ)*certFieldVal x) →
    ∀ (P : CertPoly22) (R : CertRectangle), certRectangleValid R → ∀ r s : ℝ, certPolyEval P r s = certBernsteinEval (certBernsteinCoefficients P R) R r s := by
  intro ha hm P R hR r s
  have hr : (R.r1 : ℝ) - R.r0 ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr (ne_of_gt hR.1))
  have hs : (R.s1 : ℝ) - R.s0 ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr (ne_of_gt hR.2))
  simp [certPolyEval, certBernsteinEval, certBernsteinCoefficients,
    certQuadBlend, ha, hm, certBernsteinWeight, certBernsteinBasis, Fin.sum_univ_succ]
  push_cast
  field_simp
  <;> ring

#print axioms solution
