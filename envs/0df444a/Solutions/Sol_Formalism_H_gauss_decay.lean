-- Prove2me | solution 1 for Formalism.H.gauss_decay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:08.815912+00:00
-- url     : https://prove2.me/submissions/baea4841-d7d4-46d0-80e3-bfdee862a901

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_GaussSchwartz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap
noncomputable section
open Formalism Formalism.H
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace Formalism.H
theorem _root_.solution (t : ℝ) (ht : 0 < t) (b : ℝ) :
    (fun v : V => (Real.exp (-Real.pi * t * ‖v‖ ^ 2) : ℂ)) =O[cocompact V]
      (fun v => ‖v‖ ^ (-b)) := by
  have ha : -Real.pi * t < 0 := by nlinarith [Real.pi_pos]
  have h1 := ((rexp_neg_quadratic_isLittleO_rpow_atTop ha 0 (-b)).comp_tendsto
    (tendsto_norm_cocompact_atTop (E := V))).isBigO
  refine Asymptotics.IsBigO.of_norm_left ?_
  refine h1.congr_left fun v => ?_
  simp only [Function.comp]
  first
    | rw [zero_mul, add_zero, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    | simp [Real.abs_exp]
end Formalism.H
