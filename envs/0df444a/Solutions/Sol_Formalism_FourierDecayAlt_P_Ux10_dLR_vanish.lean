-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.dLR_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:29:17.640425+00:00
-- url     : https://prove2.me/submissions/4244ecb8-2c6f-4d0d-aaed-8c66b3dee0ab

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_allLie_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dLR_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_dLR_zero


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
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : ∀ g ∈ B.GV k r, f g = 0) (u v : List (B.Mat k r)) (hu : ∀ X ∈ u, B.unitLie k r X)
    (hv : ∀ X ∈ v, B.unitLie k r X) : ∀ g ∈ B.GV k r, B.dLR u v f g = 0 := by
  intro g hg
  have h1 := W_congr (lr u v) (allLie_lr hu hv) (f := f) (f₂ := fun _ => (0 : E)) hf g hg
  rw [dLR_eq, h1, ← dLR_eq]
  have h2 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_zero (E := E) u v
  exact congrFun h2 g
end Formalism.FourierDecayAlt.P.Ux10
