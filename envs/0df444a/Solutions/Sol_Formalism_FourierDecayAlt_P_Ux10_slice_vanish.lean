-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.slice_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:26:12.722535+00:00
-- url     : https://prove2.me/submissions/4d6a149f-1f8b-4e76-9084-a74971b72615

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_gaXi_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_DjU_gaXi

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
theorem _root_.solution (hM : SliceMem) (hR : RadicalParam) (hZh : ZhSlice) {k p s ρ : ℕ} (σ : Equiv.Perm (Fin p))
    (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F₁ : B.Mat k (p + s + ρ) → E} {A₁ B₁ : ℝ} {Q : ℕ} {K : Set ℝ} (hS : Star k (p + s) ρ F₁ A₁ Q B₁ K)
    (ξ : Xi k p s ρ σ) (Z : G.Mat s) (hZ : G.detM Z ≠ 0) (hK : ‖(hMat σ d).det * G.detM Z‖ ∉ K) :
    ∀ γ ∈ B.GV k ρ, F₁ (gaXi k ρ σ d ξ Z γ) = 0 := by
  intro γ hγ
  by_contra hne
  have := hS.2.1 _ (gaXi_mem hM hR σ d hd ξ Z hZ hγ) hne
  rw [DjU_gaXi hZh] at this
  exact hK this
end Formalism.FourierDecayAlt.P.Ux10
