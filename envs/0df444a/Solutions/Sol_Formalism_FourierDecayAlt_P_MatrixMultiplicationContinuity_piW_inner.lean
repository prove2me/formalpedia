-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:33:11.020032+00:00
-- url     : https://prove2.me/submissions/3cff1456-1679-46ac-a859-1ebfe90aa367

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_uw_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_piW_facts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) {h : Formalism.FourierDecayAlt.ThreeDimData.Mx k r}
    (hh : h ∈ Formalism.QuantumDeterminants.UWset k r z) (η w : Wp) : ⟪η, π h w⟫_ℂ = ⟪π h⁻¹ η, w⟫_ℂ := by
  obtain ⟨h1, hmul, hnorm, -⟩ := piW_facts hT hπ
  obtain ⟨hi, hhi, -⟩ := uw_inv hh
  have hm := hmul h hh h⁻¹ hi
  rw [hhi, h1] at hm
  have hs : ∀ x, π h (π h⁻¹ x) = x := fun x => by
    have h3 := congrArg (fun T : Wp →L[ℂ] Wp => T x) hm
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h3
    exact h3.symm
  let L : Wp →ₗᵢ[ℂ] Wp := { toLinearMap := (π h : Wp →ₗ[ℂ] Wp), norm_map' := hnorm h hh }
  calc ⟪η, π h w⟫_ℂ = ⟪L (π h⁻¹ η), L w⟫_ℂ := by
        show ⟪η, π h w⟫_ℂ = ⟪π h (π h⁻¹ η), π h w⟫_ℂ
        rw [hs]
    _ = ⟪π h⁻¹ η, w⟫_ℂ := L.inner_map_map _ _
end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
