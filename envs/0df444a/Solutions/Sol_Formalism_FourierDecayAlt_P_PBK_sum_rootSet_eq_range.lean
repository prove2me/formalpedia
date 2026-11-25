-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.sum_rootSet_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:12.069416+00:00
-- url     : https://prove2.me/submissions/1fbbad5f-1915-44f8-8a4d-60ef4239d243

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_nthRoots_eq_R


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology Set Polynomial
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution {E : Type} [AddCommMonoid E] {s : ℕ} (hs : s ≠ 0) {w : ℂ} (hw : w ≠ 0)
    (F : ℂ → E) : ∑ z ∈ G.rootSet s w, F z = ∑ k ∈ Finset.range s, F (NthRootMeasurability.R s k w) := by
  have hnd := (Complex.isPrimitiveRoot_exp s hs).nthRoots_nodup hw
  rw [G.rootSet, ← Multiset.toFinset_eq hnd]
  show (Multiset.map F (nthRoots s w)).sum = _
  rw [Formalism.FourierDecayAlt.P.NthRootMeasurability.nthRoots_eq_R s hs w, Multiset.map_map]
  rfl
end Formalism.FourierDecayAlt.P.PBK
