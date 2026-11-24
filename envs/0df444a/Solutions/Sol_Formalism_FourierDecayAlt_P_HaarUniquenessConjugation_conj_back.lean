-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.conj_back
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:02:23.58507+00:00
-- url     : https://prove2.me/submissions/b778d6f3-4e41-4731-81ce-8ef615d43ea6

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftErrorLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarUniquenessConjugation

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
variable {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}
namespace Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
theorem _root_.solution (hP : IsUnit P.det) (U : Mat k r) : P * (P⁻¹ * U * P) * P⁻¹ = U := by
  have h : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  calc P * (P⁻¹ * U * P) * P⁻¹ = (P * P⁻¹) * U * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = U := by rw [h, Matrix.one_mul, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
