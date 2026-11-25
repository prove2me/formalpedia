-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.actA_nabsA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:04:07.555521+00:00
-- url     : https://prove2.me/submissions/e12a7693-27e3-4d7f-8471-71165510edb7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTConnGaugeA
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_actA_diag

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
theorem _root_.solution (P : M.Par) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.nabsA P (MA.DQ P)) g ρ =
      -dzbQ P (g ρ) + (M.aC P ρ : ℂ) • mulQ P (MA.DQ P).zP (mulQ P ((MA.DQ P).ggiP P.TT) (g ρ)) := by
  unfold MA.nabsA
  rw [actA_diag]
  rfl
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
