-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.norm_psiStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:31:05.211805+00:00
-- url     : https://prove2.me/submissions/385dddca-a51a-4400-b437-54cfacfdb79c

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open MeasureTheory Filter Topology
open Matrix Filter Topology
open Matrix MeasureTheory Filter Topology
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
variable {X : Type*} [TopologicalSpace X]
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution (k : ℕ) {p s : ℕ} (ρ : ℕ) (σ : Equiv.Perm (Fin p)) (z z' : Fin (2 * (p + s + ρ) + k + 1) → ℂ)
    (ξ : Xi k p s ρ σ) : ‖psiStar k ρ σ z z' ξ‖ = 1 := by
  unfold psiStar Formalism.QuantumDeterminants.psi psiH G.psi
  rw [norm_mul, norm_mul, norm_star, Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_I_mul_ofReal,
    Complex.norm_exp_I_mul_ofReal]
  norm_num
end Formalism.FourierDecayAlt.P.Ux10
