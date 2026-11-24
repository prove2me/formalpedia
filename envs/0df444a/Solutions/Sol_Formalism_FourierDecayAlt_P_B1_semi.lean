-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B1.semi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:37:24.010797+00:00
-- url     : https://prove2.me/submissions/68cc7539-24a1-449a-98bf-a10ddaf56282

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B1
theorem _root_.solution : SeminormIneq := by
  intro V _ _ β hβ hnn x y
  obtain ⟨ba1, ba2, bs1, bs2⟩ := hβ
  have hre : ∀ z, 0 ≤ (β z z).re := by
    intro z
    exact (hnn z).2
  have hexp : ∀ t : ℝ, (β (x + ((-t : ℝ) : ℂ) • y) (x + ((-t : ℝ) : ℂ) • y)).re =
      (β y y).re * (t * t) + (-(β x y + β y x).re) * t + (β x x).re := by
    intro t
    simp only [ba1, ba2, bs1, bs2, Complex.conj_ofReal, Complex.add_re, Complex.re_ofReal_mul]
    ring
  have hq : ∀ t : ℝ, 0 ≤ (β y y).re * (t * t) + (-(β x y + β y x).re) * t + (β x x).re := by
    intro t
    rw [← hexp t]
    exact hre _
  have hd := discrim_le_zero hq
  simp only [discrim] at hd
  have h1 := hexp 1
  rw [show x + ((-(1 : ℝ) : ℝ) : ℂ) • y = x - y by
    rw [Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul, sub_eq_add_neg]] at h1
  rw [h1]
  have ha := hre x
  have hb := hre y
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hpa := Real.sqrt_nonneg (β x x).re
  have hpb := Real.sqrt_nonneg (β y y).re
  nlinarith [mul_nonneg hpa hpb, sq_nonneg (Real.sqrt (β x x).re - Real.sqrt (β y y).re),
    sq_nonneg ((β x y + β y x).re + 2 * (Real.sqrt (β x x).re * Real.sqrt (β y y).re))]
end Formalism.FourierDecayAlt.P.B1
