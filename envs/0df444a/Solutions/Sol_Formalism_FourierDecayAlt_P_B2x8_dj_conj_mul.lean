-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.dj_conj_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:04:48.471819+00:00
-- url     : https://prove2.me/submissions/f71ccdc8-0107-4fe5-bbc2-e533c59a476f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (a : Mat k r) (ha : IsUnit a.det) (p : Mt k r × Mt k r) :
    conjM a (mulM p) = mulM (conjM a p.1, conjM a p.2) := by
  unfold conjM mulM
  show a * (Matrix.of p.1 * Matrix.of p.2) * a⁻¹ = (a * Matrix.of p.1 * a⁻¹) * (a * Matrix.of p.2 * a⁻¹)
  have h : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a ha
  calc a * (Matrix.of p.1 * Matrix.of p.2) * a⁻¹ = a * Matrix.of p.1 * 1 * Matrix.of p.2 * a⁻¹ := by
        simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = (a * Matrix.of p.1 * a⁻¹) * (a * Matrix.of p.2 * a⁻¹) := by
        rw [← h]; simp only [Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P.B2x8
