-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.cv_dil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:22:49.491961+00:00
-- url     : https://prove2.me/submissions/0f906b3f-cd13-41a2-975c-5a8a6b5ecba7

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_isUnit_det
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private lemma exp_conj_lemma (a A : Mat k r) (ha : IsUnit a) :
    NormedSpace.exp (a⁻¹ * A * a) = a⁻¹ * NormedSpace.exp A * a := by
  first
    | exact Matrix.exp_conj' a A ha
    | (have h := Matrix.exp_conj a⁻¹ A ((Matrix.isUnit_nonsing_inv_iff).mpr ha)
       rwa [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp ha)] at h)
section
variable {t : ℝ × ℝ} (h1 : t.1 ∈ Set.Icc (1 / 2 : ℝ) 2) (h2 : t.2 ∈ Set.Icc (1 / 2 : ℝ) 2)
include h1 h2
end
end Formalism.FourierDecayAlt.P.B4
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution (t : ℝ × ℝ) (h1 : t.1 ≠ 0) (h2 : t.2 ≠ 0) (b : Bool) (X g : Mat k r) (s : ℝ) :
    (aDil k r t.1)⁻¹ * cv b X s g * aDil k r t.2 =
      cv b (adj t (b, X)).2 s ((aDil k r t.1)⁻¹ * g * aDil k r t.2) := by
  have hu1 : IsUnit (aDil k r t.1) := (Matrix.isUnit_iff_isUnit_det _).mpr (aDil_isUnit_det _ h1)
  have hu2 : IsUnit (aDil k r t.2) := (Matrix.isUnit_iff_isUnit_det _).mpr (aDil_isUnit_det _ h2)
  have hsm : ∀ (c : ℂ) (a : Mat k r), c • (a⁻¹ * X * a) = a⁻¹ * (c • X) * a := by
    intro c a
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hsm' : ∀ (c : ℂ) (a : Mat k r), -(c • (a⁻¹ * X * a)) = a⁻¹ * (-(c • X)) * a := by
    intro c a
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  cases b
  · simp only [cv, adj, sel]
    rw [hsm, exp_conj_lemma _ _ hu2]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (aDil_isUnit_det _ h2)]
  · simp only [cv, adj, sel]
    rw [hsm', exp_conj_lemma _ _ hu1]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (aDil_isUnit_det _ h1)]
end Formalism.FourierDecayAlt.P.B4
