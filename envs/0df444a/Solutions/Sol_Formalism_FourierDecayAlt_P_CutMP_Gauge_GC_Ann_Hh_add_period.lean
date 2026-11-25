-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.Hh_add_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:32:00.018161+00:00
-- url     : https://prove2.me/submissions/002bcbe8-cee5-4066-8deb-61298e0833d8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtPrim
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FderivDecomp

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
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (TT : ℝ) (w : ℂ) (k : ℤ) : w + (k : ℂ) * (2 * Real.pi * I) ∈ Hh TT ↔ w ∈ Hh TT := by

  simp only [Hh, Set.mem_setOf_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
