-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftToRightConversion.cv_LR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:29:26.291799+00:00
-- url     : https://prove2.me/submissions/0b1b981b-9c63-47f1-ac5a-624b553882a1

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftToRightConversion
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LeftToRightConversion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic
  Formalism.FourierDecayAlt.P.ListSumInequalities Formalism.FourierDecayAlt.P.ListSumSplittings
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.LeftToRightConversion
theorem _root_.solution {X g : Mat k r} (hg : g ∈ GV k r) (t : ℝ) :
    cv true X t g = cv false (-(g⁻¹ * X * g)) t g := by
  have hdu := WeylGroupFacts.isUnit_of_uh hg
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 hdu
  have hgi : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdu
  have hc : g * (g⁻¹ * X * g) * g⁻¹ = X := by
    simp only [Matrix.mul_assoc, hgi, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hgi, Matrix.one_mul]
  have e : g * ((t : ℂ) • -(g⁻¹ * X * g)) * g⁻¹ = -((t : ℂ) • X) := by
    rw [smul_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, hc]
  show NormedSpace.exp (-((t : ℂ) • X)) * g = g * NormedSpace.exp ((t : ℂ) • -(g⁻¹ * X * g))
  rw [← e, Matrix.exp_conj _ _ hu, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdu, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.LeftToRightConversion
