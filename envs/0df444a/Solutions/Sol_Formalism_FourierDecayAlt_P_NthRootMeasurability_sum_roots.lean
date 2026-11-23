-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NthRootMeasurability.sum_roots
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:07.886831+00:00
-- url     : https://prove2.me/submissions/88f12a51-4a9b-4050-911b-a0853a16444c

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Theorems.Thm_Formalism_FourierDecayAlt_P_NthRootMeasurability_nthRoots_eq_R

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NthRootMeasurability
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.NthRootMeasurability
theorem _root_.solution (s : ℕ) (hs : s ≠ 0) (H : ℂ → ENNReal) (w : ℂ) :
    ((nthRoots s w).map H).sum = ∑ k ∈ Finset.range s, H (R s k w) := by
  rw [nthRoots_eq_R s hs, Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl
end Formalism.FourierDecayAlt.P.NthRootMeasurability
