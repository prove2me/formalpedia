-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.hasDerivAt_br
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:03:15.967248+00:00
-- url     : https://prove2.me/submissions/8c70b544-6e4a-4cf6-8386-a92a95450c8d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThShiftInt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NeZeroOfAn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) : HasDerivAt (br s) ζ⁻¹ ζ := by
  cases s
  · simp only [brD, Bool.false_eq_true, ↓reduceIte, Set.mem_setOf_eq] at hs
    have e1 : br false = fun z : ℂ => Complex.log (-z) + Real.pi * I := by
      funext z
      simp [br]
    have h1 : HasDerivAt (fun z : ℂ => Complex.log (-z)) ((-ζ)⁻¹ * (-1)) ζ :=
      (Complex.hasDerivAt_log hs).comp ζ (hasDerivAt_neg ζ)
    have h2 := h1.add_const ((Real.pi : ℂ) * I)
    have e2 : (-ζ)⁻¹ * (-1) = ζ⁻¹ := by rw [inv_neg, neg_mul_neg, mul_one]
    rw [e2] at h2
    rw [e1]
    exact h2
  · simp only [brD, ↓reduceIte] at hs
    have e1 : br true = Complex.log := by
      funext z
      simp [br]
    rw [e1]
    exact Complex.hasDerivAt_log hs
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
