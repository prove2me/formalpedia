-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DDSmoothness.smooth_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:54:01.864464+00:00
-- url     : https://prove2.me/submissions/6252a1d7-19ea-4177-a3e3-9c00170d85ed

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
theorem _root_.solution (σ : Mx k r → (H →L[ℂ] H)) : (0 : H) ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by
  simp only [PI.UpqRep.smoothVecs, Set.mem_setOf_eq, PI.UpqRep.IsSmoothVec, PI.UpqRep.SmoothOnH]
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => map_zero (σ g)⟩
end Formalism.FourierDecayAlt.P.DDSmoothness
