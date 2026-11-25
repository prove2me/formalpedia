-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.projI_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:31:26.066253+00:00
-- url     : https://prove2.me/submissions/fe45b839-01de-410f-8aa3-c0468e1b6af4

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_KLExA_projI_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_KLExA_sum_projI
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Submodule ℂ V}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
theorem _root_.solution (h : DirectSum.IsInternal S) (T : Module.End ℂ V) (hT : ∀ j, ∀ v ∈ S j, T v ∈ S j) (i : ι) (v : V) :
    projI h i (T v) = T.restrict (hT i) (projI h i v) := by
  have e : T v = ∑ j, ((T.restrict (hT j) (projI h j v) : S j) : V) := by
    conv_lhs => rw [← sum_projI h v]
    rw [map_sum]
    rfl
  rw [e, projI_sum]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
