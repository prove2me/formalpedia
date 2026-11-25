-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.actA_kap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:15:53.970696+00:00
-- url     : https://prove2.me/submissions/4e455a32-9479-43ed-845c-380c8b567015

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTConnGaugeA
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_actA_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_algebraMap_fst_apply

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
theorem _root_.solution (P : M.Par) (f : M.Ty P → ℂ) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.kap P (MA.DQ P) f) g ρ = f ρ • g ρ := by
  have hk : (MA.kap P (MA.DQ P) f : MA.A P (MA.DQ P)) =
      Matrix.diagonal (fun π => algebraMap ℂ (MA.DQ P).Pr (f π)) := by
    first
    | rfl
    | (ext i j; simp [MA.kap, Matrix.diagonal_apply])
  rw [hk, actA_diag, algebraMap_fst_apply]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
