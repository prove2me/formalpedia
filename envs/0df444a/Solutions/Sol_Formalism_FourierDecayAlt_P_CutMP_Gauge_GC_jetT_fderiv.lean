-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:18:11.927019+00:00
-- url     : https://prove2.me/submissions/b0739842-079d-44c2-9ba5-3e9b0a97e095

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTJet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution {D G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : D → G} {g₀ : D} {i : ℕ} (h : iteratedFDeriv ℝ (i + 1) F g₀ = 0) :
    iteratedFDeriv ℝ i (fderiv ℝ F) g₀ = 0 := by
  rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply] at h
  exact (LinearIsometryEquiv.map_eq_zero_iff _).1 h
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
