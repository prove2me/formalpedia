-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.measurable_apply_mulF_of_jetLocal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:19.565283+00:00
-- url     : https://prove2.me/submissions/ec57b8fb-088f-4a3e-be0a-6b8403aeb88c

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_meas_ld

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (hLeib : Leibniz) (B : Base) {A A' : Type} (T : Fn B A → Fn B A') (u : Fn B A) (M : ℕ)
    (hJ : JetLocal B T u) (hP : PolyS B T u M) (hm : ∀ p a, Measurable fun ω => dS B T u p ω a)
    (φ : ℝ → ℝ) (hφ : SmoothLog φ) (a : A') : Measurable fun ω => T (mulF B φ u) ω a := by
  have := hLeib B A A' T u M hJ hP φ hφ
  simp_rw [this]
  refine Finset.measurable_sum _ fun p _ => ?_
  refine Measurable.div_const (Measurable.mul ?_ (hm p a)) _
  exact Complex.measurable_ofReal.comp ((meas_ld p φ hφ).comp B.G_meas)
end Formalism.FourierDecayAlt.P.LEx2
