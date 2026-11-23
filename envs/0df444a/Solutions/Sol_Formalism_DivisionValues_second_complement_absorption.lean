-- Prove2me | solution 1 for Formalism.DivisionValues.second_complement_absorption
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:43.545835+00:00
-- url     : https://prove2.me/submissions/448dbce7-2255-4290-9ed6-79749ef1f253

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open PlaceSumConjugation
namespace Formalism.DivisionValues
theorem _root_.solution (W' Dl er lg Eels C0 f m b L B0 : ℝ) (hB0 : B0 = f * m * b * L) (hf : 1 ≤ f)
    (hm : 1 ≤ m) (hb : 0 ≤ b) (hC0 : 0 ≤ C0) (hfbL : f * b * L ≤ B0)
    (hW : W' ≤ f * (2 * b)) (hDl : Dl ≤ f * (5 * C0 * b)) (her : er ≤ C0 * (f * (b + m * b)))
    (hlg0 : 0 ≤ lg) (hlg : lg ≤ C0 * L) (hE : Eels ≤ (2 * C0 + 10) * B0) :
    (W' + Dl + 2 * er) * lg + 2 * Eels ≤ (9 * C0 ^ 2 + 6 * C0 + 20) * B0 := by
  subst hB0
  have hf0 : 0 ≤ f := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hfb : 0 ≤ f * b := mul_nonneg hf0 hb
  have hfmb : 0 ≤ f * m * b := mul_nonneg (mul_nonneg hf0 hm0) hb
  have hS : W' + Dl + 2 * er ≤ f * b * (2 + 7 * C0) + 2 * C0 * (f * m * b) := by linarith
  have hU0 : 0 ≤ f * b * (2 + 7 * C0) + 2 * C0 * (f * m * b) :=
    add_nonneg (mul_nonneg hfb (by linarith)) (mul_nonneg (by linarith) hfmb)
  have h1 : (W' + Dl + 2 * er) * lg ≤ (f * b * (2 + 7 * C0) + 2 * C0 * (f * m * b)) * lg :=
    mul_le_mul_of_nonneg_right hS hlg0
  have h2 : (f * b * (2 + 7 * C0) + 2 * C0 * (f * m * b)) * lg ≤
      (f * b * (2 + 7 * C0) + 2 * C0 * (f * m * b)) * (C0 * L) :=
    mul_le_mul_of_nonneg_left hlg hU0
  have h3 : C0 * (2 + 7 * C0) * (f * b * L) ≤ C0 * (2 + 7 * C0) * (f * m * b * L) :=
    mul_le_mul_of_nonneg_left hfbL (mul_nonneg hC0 (by linarith))
  linarith
end Formalism.DivisionValues
