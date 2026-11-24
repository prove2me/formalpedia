-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.pl_isTest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:54:03.371818+00:00
-- url     : https://prove2.me/submissions/41f47f9f-af90-4c36-bf18-6359af1d5381

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B3
open Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B3
theorem _root_.solution {a b k : ℝ} (ha : 0 < a) (hk : 0 ≤ k) : IsTest (pl a b k) := by
  have hsub : Function.support (pl a b k) ⊆ Set.Icc a b := by
    intro x hx
    by_contra h
    exact hx (pl_eq_zero hk (fun h' => h (Set.Ioo_subset_Icc_self h')))
  refine ⟨pl_contDiff a b k, HasCompactSupport.intro (isCompact_Icc (a := a) (b := b)) (fun x hx => ?_), ?_⟩
  · by_contra h
    exact hx (hsub h)
  · exact (closure_minimal hsub isClosed_Icc).trans (fun x hx => lt_of_lt_of_le ha hx.1)
end Formalism.FourierDecayAlt.P.B3
