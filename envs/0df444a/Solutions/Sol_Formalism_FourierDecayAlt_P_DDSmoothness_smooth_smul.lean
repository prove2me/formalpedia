-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:53:59.38598+00:00
-- url     : https://prove2.me/submissions/55da5103-aca3-4a78-a66a-519d79b8822a

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LowSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate ContDiff
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.DDSmoothness
theorem _root_.solution {σ : Mx k r → (H →L[ℂ] H)} (a : ℂ) {v : H} (hv : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) :
    a • v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  simp only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH] at hv ⊢
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hv g₀ hg₀
  refine ⟨U, fun g => a • F g, hU, hgU, hF.const_smul a, fun g hg hgH => ?_⟩
  simp only [map_smul, hFe g hg hgH]
end Formalism.FourierDecayAlt.P.DDSmoothness
