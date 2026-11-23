-- Prove2me | solution 1 for Formalism.DivisionValues.second_complement_els_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:44.242205+00:00
-- url     : https://prove2.me/submissions/6e870be1-288b-44d6-bb3e-1f3b22bc0aec

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
theorem _root_.solution (C0 B0 f b L k b' N X'' logd c Eels : ℝ) (hC0 : 0 ≤ C0) (hf : 1 ≤ f) (hb : 0 ≤ b)
    (hk : 1 ≤ k) (hb' : 0 ≤ b') (hc : c ≤ f) (hkb : k * b' ≤ b)
    (hX : f * k * N * X'' ≤ b) (hd0 : 0 ≤ logd) (hd : logd ≤ L) (hfbL : f * b * L ≤ B0)
    (hbB0 : b ≤ B0)
    (hE : Eels ≤ C0 * B0 + (c * (2 * b + 4 * k * b') + 4 * f * k * b') * logd +
      C0 * (f * k * N * X'')) : Eels ≤ (2 * C0 + 10) * B0 := by
  have hf0 : 0 ≤ f := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hkb0 : 0 ≤ k * b' := mul_nonneg hk0 hb'
  have hpos : 0 ≤ 2 * b + 4 * k * b' := by linarith
  have e1 : c * (2 * b + 4 * k * b') ≤ f * (2 * b + 4 * k * b') :=
    mul_le_mul_of_nonneg_right hc hpos
  have e2 : f * (k * b') ≤ f * b := mul_le_mul_of_nonneg_left hkb hf0
  have hcoef : c * (2 * b + 4 * k * b') + 4 * f * k * b' ≤ 10 * (f * b) := by linarith
  have e3 : (c * (2 * b + 4 * k * b') + 4 * f * k * b') * logd ≤ 10 * (f * b) * logd :=
    mul_le_mul_of_nonneg_right hcoef hd0
  have hfb : 0 ≤ f * b := mul_nonneg hf0 hb
  have e4 : f * b * logd ≤ f * b * L := mul_le_mul_of_nonneg_left hd hfb
  have e5 : C0 * (f * k * N * X'') ≤ C0 * B0 :=
    mul_le_mul_of_nonneg_left (le_trans hX hbB0) hC0
  linarith
end Formalism.DivisionValues
