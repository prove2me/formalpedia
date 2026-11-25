-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.actA_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:28:06.6178+00:00
-- url     : https://prove2.me/submissions/9fc79b4b-64f8-4b26-8527-170eb72094e0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTConnGaugeA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution (P : M.Par) (x : M.Ty P → (MA.DQ P).Pr) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (Matrix.diagonal x : MA.A P (MA.DQ P)) g ρ = (x ρ).1 (g ρ) := by
  unfold MA.actA
  refine (Fintype.sum_eq_single ρ (fun b hb => ?_)).trans ?_
  · have h0 := congrArg (fun m : (MA.DQ P).Pr => m.1 (g b)) (Matrix.diagonal_apply_ne x (Ne.symm hb))
    exact h0.trans (by first | rfl | simp)
  · exact congrArg (fun m : (MA.DQ P).Pr => m.1 (g ρ)) (Matrix.diagonal_apply_eq x ρ)
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
