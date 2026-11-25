-- Prove2me | solution 1 for CompanionTheory.CapEig.capelli_coefficient_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:59:25.339152+00:00
-- url     : https://prove2.me/submissions/7cd5b91a-2de1-4c26-b9f8-564d5b90d614

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_UniformCoefficientBounds_CoefBoundUniform
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_CoefCC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.CapEig
open CompanionTheory.D.Upq.Sm Formalism.FourierDecayAlt CompanionTheory.LimBd.Main
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace CompanionTheory.CapEig
theorem _root_.solution : CoefSmooth := by
  intro hK k r ε μ φ E _ _ T hφ g₀ hg₀
  obtain ⟨H, _, _, _, σ, v, w, hμ, hσ, hv, -, he⟩ := hφ
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hK k r ε μ H σ hμ hσ v hv g₀ hg₀
  refine ⟨U, fun x => (((innerSL ℂ w).smulRight T).restrictScalars ℝ) (F x), hU, hgU,
    (((innerSL ℂ w).smulRight T).restrictScalars ℝ).contDiff.comp_contDiffOn hF, fun g hg hgG => ?_⟩
  have e := hfF g hg hgG
  simp only at e
  simp [he g hgG, e]
end CompanionTheory.CapEig
