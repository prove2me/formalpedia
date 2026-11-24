-- Prove2me | solution 1 for Formalism.L2.SG.AvgPf.fd_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:17:57.249307+00:00
-- url     : https://prove2.me/submissions/a1796776-d7da-4c5d-90f4-e6e5acfc9df9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_LieAveraging_LsSetresAvg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Set
open scoped Pointwise ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.AvgPf
namespace Formalism.L2.SG.AvgPf
theorem _root_.solution {Γ α : Type*} [Group Γ] [MulAction Γ α] [MeasurableSpace α] {μ : Measure α}
    [MeasurableConstSMul Γ α] [SMulInvariantMeasure Γ α μ] [Countable Γ] {S : Set α}
    (h : IsFundamentalDomain Γ S μ) (hμ : μ univ ≠ 0) : μ S ≠ 0 := by
  intro h0
  exact hμ (h.measure_zero_of_invariant _ (fun _ => Set.smul_set_univ) (by rw [Set.univ_inter]; exact h0))
end Formalism.L2.SG.AvgPf
