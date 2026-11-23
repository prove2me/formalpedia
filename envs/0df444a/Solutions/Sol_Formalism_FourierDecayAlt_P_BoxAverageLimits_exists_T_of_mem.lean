-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.exists_T_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:02.288795+00:00
-- url     : https://prove2.me/submissions/b6ba4338-988b-4638-8d23-6c27eabb0fcf

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_BoxAverageLimits_le_atInfAll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.BoxAverageLimits
theorem _root_.solution {f : ℕ} {t : Set (V f)} (ht : t ∈ atInfAll f) :
    ∃ T : ℝ, {x : V f | ∀ v, T ≤ ‖x v‖} ⊆ t := by
  have hdir : Directed (fun x1 x2 => x1 ⊇ x2) (fun T : ℝ => {x : V f | ∀ v, T ≤ ‖x v‖}) := by
    intro T1 T2
    refine ⟨max T1 T2, fun x hx v => le_trans (le_max_left _ _) (hx v),
      fun x hx v => le_trans (le_max_right _ _) (hx v)⟩
  have hb := Filter.hasBasis_iInf_principal hdir
  obtain ⟨T, -, hT⟩ := hb.mem_iff.mp (le_atInfAll f ht)
  exact ⟨T, hT⟩
end Formalism.FourierDecayAlt.P.BoxAverageLimits
