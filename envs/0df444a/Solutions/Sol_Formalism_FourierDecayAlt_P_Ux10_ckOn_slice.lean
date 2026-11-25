-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.ckOn_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:59:31.579087+00:00
-- url     : https://prove2.me/submissions/2e8c2c90-e64e-49a1-adac-d1f675517916

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cd_gaXi
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mono


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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution (hM : SliceMem) (hR : RadicalParam) {k p s ρ : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (hd : ∀ i, d i ≠ 0) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {F₁ : B.Mat k (p + s + ρ) → E}
    {Q : ℕ∞} (hF : B.CkOn Q (B.GV k (p + s + ρ)) F₁) (ξ : Xi k p s ρ σ) (Z : G.Mat s) (hZ : G.detM Z ≠ 0) :
    B.CkOn Q (B.GV k ρ) (fun γ => F₁ (gaXi k ρ σ d ξ Z γ)) := by
  intro γ₀ hγ₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hF _ (gaXi_mem hM hR σ d hd ξ Z hZ hγ₀)
  have hcd := cd_gaXi (k := k) σ d ξ Z
  refine ⟨(fun γ => gaXi k ρ σ d ξ Z γ) ⁻¹' U, fun γ => f' (gaXi k ρ σ d ξ Z γ),
    hU.preimage (continuousOn_univ.1 hcd.continuousOn), hgU, ?_, ?_⟩
  · exact hc.comp ((hcd.of_le (by exact_mod_cast le_top)).mono (Set.subset_univ _)) (fun x hx => hx)
  · intro γ hγ hγG
    exact hff _ hγ (gaXi_mem hM hR σ d hd ξ Z hZ hγG)
end Formalism.FourierDecayAlt.P.Ux10
