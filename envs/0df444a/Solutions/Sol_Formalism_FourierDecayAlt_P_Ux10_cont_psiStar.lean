-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.cont_psiStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:31:24.51487+00:00
-- url     : https://prove2.me/submissions/6710c508-f1b7-4e58-ab3f-f77e14b8b055

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_Rn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_continuous_psi_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_psiH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.continuous_psi_comp

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
theorem _root_.solution (k : ℕ) {p s : ℕ} (ρ : ℕ) (σ : Equiv.Perm (Fin p)) (z z' : Fin (2 * (p + s + ρ) + k + 1) → ℂ) :
    Continuous fun ξ : Xi k p s ρ σ => psiStar k ρ σ z z' ξ := by
  have h1 : Continuous fun ξ : Xi k p s ρ σ => Formalism.QuantumDeterminants.psi k (p + s + ρ) z cStd (Rn k (p + s) ρ ξ.1.1) :=
    continuous_psi_comp z cStd ((cont_Rn k (p + s) ρ).comp (continuous_fst.comp continuous_fst))
  have h2 : Continuous fun ξ : Xi k p s ρ σ => Formalism.QuantumDeterminants.psi k (p + s + ρ) z' cStd (Rn k (p + s) ρ ξ.1.2) :=
    continuous_psi_comp z' cStd ((cont_Rn k (p + s) ρ).comp (continuous_snd.comp continuous_fst))
  have h3 : Continuous fun ξ : Xi k p s ρ σ => psiH betaU σ ξ.2 := (cont_psiH betaU σ).comp continuous_snd
  unfold psiStar
  exact (h1.mul (continuous_star.comp h2)).mul h3
end Formalism.FourierDecayAlt.P.Ux10
