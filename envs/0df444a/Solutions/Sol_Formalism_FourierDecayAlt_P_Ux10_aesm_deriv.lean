-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.aesm_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:54:09.143389+00:00
-- url     : https://prove2.me/submissions/07f70247-3d3f-42e2-82cc-53a52c0f7e73

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_tendsto_inv_succ_nhdsNE

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution {G : α → ℝ → E} {G' : α → E} (hd : ∀ ξ, HasDerivAt (G ξ) (G' ξ) 0)
    (hm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (fun ξ => G ξ t) μ) : AEStronglyMeasurable G' μ := by
  have hm0 : AEStronglyMeasurable (fun ξ => G ξ 0) μ := hm.self_of_nhds
  have hev : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable (fun ξ => G ξ (((n : ℝ) + 1)⁻¹)) μ :=
    (tendsto_inv_succ_nhdsNE.mono_right nhdsWithin_le_nhds).eventually hm
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun (n : ℕ) ξ => ((((n + n₀ : ℕ) : ℝ) + 1)⁻¹)⁻¹ • (G ξ (0 + (((n + n₀ : ℕ) : ℝ) + 1)⁻¹) - G ξ 0)) ?_ ?_
  · intro n
    have h1 := hn₀ (n + n₀) (by omega)
    simp only [zero_add]
    exact (h1.sub hm0).const_smul _
  · refine Eventually.of_forall fun ξ => ?_
    exact ((hd ξ).tendsto_slope_zero).comp (tendsto_inv_succ_nhdsNE.comp (tendsto_add_atTop_nat n₀))
end Formalism.FourierDecayAlt.P.Ux10
