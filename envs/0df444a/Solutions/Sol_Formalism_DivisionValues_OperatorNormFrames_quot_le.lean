-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.quot_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:16.841621+00:00
-- url     : https://prove2.me/submissions/68027b8b-abf8-433d-82f9-f4a6fc1d46a6

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_cnorm_le_of_orth
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_quot_rep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open OperatorNormFrames
open Formalism.DivisionValues.OperatorNormFrames
namespace Formalism.DivisionValues.OperatorNormFrames
theorem _root_.solution {n D : ℕ} (Hc X0 : Matrix (Fin n) (Fin n) ℂ) (h0 : IsUnit X0.det)
    (hH : (X0⁻¹)ᴴ * X0⁻¹ = Hc) (Pc : Matrix (Fin D) (Fin n) ℂ) (XQ : Matrix (Fin D) (Fin D) ℂ)
    (hQ : IsUnit XQ.det) (hG : (XQ⁻¹)ᴴ * XQ⁻¹ = (Pc * Hc⁻¹ * Pcᴴ)⁻¹) (x : Fin n → ℂ) :
    fnorm XQ (Pc.mulVec x) ≤ fnorm X0 x := by
  obtain ⟨x0, hx0, hn, horth⟩ := quot_rep Hc X0 h0 hH Pc XQ hQ hG (Pc.mulVec x)
  have hw : Pc.mulVec (x - x0) = 0 := by
    rw [Matrix.mulVec_sub, hx0, sub_self]
  have h := horth _ hw
  rw [← hn]
  show Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ x0) ≤ Formalism.HermitianLatticesTheory.cnorm (X0⁻¹ *ᵥ x)
  have e : X0⁻¹ *ᵥ x = X0⁻¹ *ᵥ x0 + X0⁻¹ *ᵥ (x - x0) := by
    rw [← Matrix.mulVec_add]
    congr 1
    abel
  rw [e]
  exact cnorm_le_of_orth _ _ h
end Formalism.DivisionValues.OperatorNormFrames
