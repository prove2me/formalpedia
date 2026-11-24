-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.sum_projI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:51:49.425315+00:00
-- url     : https://prove2.me/submissions/d131f008-9a6c-4b18-9fba-6ff55791e14c

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg
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
theorem _root_.solution (h : DirectSum.IsInternal S) (v : V) : ∑ j, (projI h j v : V) = v := by
  set e := LinearEquiv.ofBijective (DirectSum.coeLinearMap S) h with he
  have h1 : DirectSum.coeLinearMap S (e.symm v) = v := e.apply_symm_apply v
  conv_rhs => rw [← h1, ← DirectSum.sum_univ_of (e.symm v)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [DirectSum.coeLinearMap_of]
  rfl
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
