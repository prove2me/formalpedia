-- Prove2me | solution 1 for CompanionTheory.D.Upq.BesselFunctionalConstruction.shape_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:19:17.712467+00:00
-- url     : https://prove2.me/submissions/e851df1a-f8e4-49ba-a521-ebdd08dd7e1f

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_KFinFormOf
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_DD_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_bessel_smul


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
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.BesselFunctionalConstruction
open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
namespace CompanionTheory.D.Upq.BesselFunctionalConstruction
theorem _root_.solution (hR : RankOne) (hBB : BeBessel) : Shape := by
  intro hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z u π μW μN μG νq hS ⟨x0, hx0, y0, hy0, hne⟩
  have hsm := DD_smooth hIn.2.2.1 hS.1 hS.2.1 hS.2.2.2.2.1
  obtain ⟨L, hL⟩ := hR k r ε lam h H σ w0 Wp z u π μW μN μG νq hS
  rw [hL x0 (hsm x0 hx0) y0 (hsm y0 hy0)] at hne
  have hLx : L x0 ≠ 0 := fun h0 => hne (by ext ξ; simp [h0])
  have hLy : L y0 ≠ 0 := fun h0 => hne (by ext ξ; simp [h0])
  have hn : ⟪L y0, L y0⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hLy
  have hB := bessel_smul
    (hBB hIn k r ε lam h H σ w0 Wp z _ u π μW μN μG νq hS y0 (Or.inl hy0) (L y0))
    (⟪L y0, L y0⟫_ℂ)⁻¹
  have he : ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      (⟪L y0, L y0⟫_ℂ)⁻¹ • be z Formalism.QuantumDeterminants.cStd π σ μW μN x y0 (L y0) = L x := fun x hx => by
    rw [hL x hx y0 (hsm y0 hy0), ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul,
      inv_mul_cancel₀ hn, one_smul]
  refine ⟨_, hB, ⟨x0, hx0, by rw [he x0 (hsm x0 hx0)]; exact hLx⟩, fun x hx v hv => ?_⟩
  rw [he x hx, he v (hsm v hv), hL x hx v (hsm v hv)]
end CompanionTheory.D.Upq.BesselFunctionalConstruction
