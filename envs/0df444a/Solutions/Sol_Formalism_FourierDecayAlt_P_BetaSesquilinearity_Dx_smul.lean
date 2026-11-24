-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dx_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:46:34.58481+00:00
-- url     : https://prove2.me/submissions/a3492b39-2be6-4c72-a0ca-f43aaf96e0df

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity

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
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (c : ℂ) (x : Bool × Mat k r) (f : Mat k r → E) :
    Dx x (fun g => c • f g) = fun g => c • Dx x f g := by
  funext g
  rw [Dx_eq, Dx_eq]
  show deriv (fun t : ℝ => c • f (crv x g t)) 0 = c • deriv (fun t : ℝ => f (crv x g t)) 0
  by_cases hc : c = 0
  · subst hc; simp
  by_cases hd : DifferentiableAt ℝ (fun t : ℝ => f (crv x g t)) 0
  · exact deriv_const_smul c hd
  · have hd' : ¬ DifferentiableAt ℝ (fun t : ℝ => c • f (crv x g t)) 0 := by
      intro h'
      apply hd
      have h2 : DifferentiableAt ℝ (fun t : ℝ => c⁻¹ • (c • f (crv x g t))) 0 := h'.const_smul c⁻¹
      simpa [smul_smul, inv_mul_cancel₀ hc] using h2
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd', smul_zero]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
