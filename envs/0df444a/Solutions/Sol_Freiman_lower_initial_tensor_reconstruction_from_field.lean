-- Prove2me | solution 1 for Freiman.lower_initial_tensor_reconstruction_from_field
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T00:26:54.306645+00:00
-- url     : https://prove2.me/submissions/6b8638be-f0dd-4fc0-b5f9-2374dbcb5601

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

set_option maxRecDepth 40000

theorem solution
    (hadd : ∀ a b : CertField, certFieldVal (certFieldAdd a b) = certFieldVal a + certFieldVal b)
    (hscale : ∀ (q : ℚ) (a : CertField), certFieldVal (certFieldScale q a) = (q:ℝ)*certFieldVal a)
    (P : LowerInitialPoly) (x y z : ℝ) :
    lowerInitialPolyEval P x y z = lowerInitialBernsteinEval (lowerInitialBernstein P) x y z := by
  have blend : ∀ (a b : ℚ) (v : Fin 3 → CertField) (i : Fin 3),
      certFieldVal (certQuadBlend a b v i)
        = certFieldVal (v 0)
          + ((if i = 0 then a else if i = 1 then (a+b)/2 else b : ℚ) : ℝ) * certFieldVal (v 1)
          + ((if i = 0 then a^2 else if i = 1 then a*b else b^2 : ℚ) : ℝ) * certFieldVal (v 2) := by
    intro a b v i
    simp only [certQuadBlend, hadd, hscale]
    ring
  simp only [lowerInitialPolyEval, lowerInitialBernsteinEval, lowerInitialBernstein,
    lowerInitialWeight, certBernsteinBasis, blend, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Fin.isValue]
  push_cast
  ring
