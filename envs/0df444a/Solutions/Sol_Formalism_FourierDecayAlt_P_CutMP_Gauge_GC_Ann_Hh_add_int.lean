-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.Hh_add_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:59:03.9611+00:00
-- url     : https://prove2.me/submissions/10969d9a-560d-4100-8f35-8d7ada2a9ef4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ImCircleIntegral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThShiftInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex MeasureTheory intervalIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution {w : ℂ} (k : ℤ) : w + (k : ℂ) * (2 * Real.pi * I) ∈ Hh TT ↔ w ∈ Hh TT := by
  simp only [Hh, Set.mem_ofPred_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
