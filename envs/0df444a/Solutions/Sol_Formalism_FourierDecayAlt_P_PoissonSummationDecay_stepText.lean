-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PoissonSummationDecay.stepText
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:04.971795+00:00
-- url     : https://prove2.me/submissions/941e0903-4141-452d-9bd0-4529779f6ffd

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeTheta_ThetaShiftInversion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PoissonSummationDecay
open Formalism.FourierDecayAlt.F7
open Finset Polynomial
open MeasureTheory Formalism.H
open scoped FourierTransform RealInnerProductSpace ENNReal
namespace Formalism.FourierDecayAlt.P.PoissonSummationDecay
theorem _root_.solution (h : PoissonStep) (h2 : PoissonSummable) (h3 : ProductDecaySummable) :
    PoissonStepText := by
  intro V _ _ _ _ _ ι _ π hπ Λ _ _ φ C x hc hφ hsum hnn
  have hloc : LocSummable Λ (fun v => (φ v : ℂ)) :=
    h3 V ι π hπ Λ (fun v => (φ v : ℂ)) C (fun c => by simpa [Complex.norm_real] using hφ c)
  have hPA := h2 V Λ (fun v => (φ v : ℂ)) (Complex.continuous_ofReal.comp hc) hloc hsum x
  exact ⟨hPA, h V Λ φ x hPA hnn⟩
end Formalism.FourierDecayAlt.P.PoissonSummationDecay
