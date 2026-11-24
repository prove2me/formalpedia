-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.projI_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:33:55.833087+00:00
-- url     : https://prove2.me/submissions/e47815a0-885e-4f54-bb56-397fdeebcda3

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_KLExA_projI_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_KLExA_projI_ne
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
theorem _root_.solution (h : DirectSum.IsInternal S) (y : ∀ j, S j) (i : ι) : projI h i (∑ j, (y j : V)) = y i := by
  rw [map_sum, Finset.sum_eq_single i (fun j _ hj => projI_ne h hj (y j)) (fun hi => absurd (Finset.mem_univ i) hi)]
  exact projI_self h (y i)
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
