-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.sum_ind_Xs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:46:50.329167+00:00
-- url     : https://prove2.me/submissions/32b7f81d-142d-4d3c-a359-54f3d801dff8

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveSemidefinitePullback
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_last_size

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
noncomputable section
open Classical
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
theorem _root_.solution (T : Tower E) {i : ℕ} (hi : 1 ≤ i) :
    ∑ s ∈ Icc 1 i, ind (T.X i) (Xs T i s) = ind (T.X i) (T.X i) := by
  funext p
  obtain ⟨s, hs, hps⟩ := last_size T hi p.2
  rw [Finset.sum_apply, Finset.sum_eq_single s]
  · have hm : (p : Pt E) ∈ Xs T i s := by
      simp only [Xs, Finset.mem_filter]
      exact ⟨p.2, hps⟩
    simp [ind, hm]
  · intro s' _ hne
    have : (p : Pt E) ∉ Xs T i s' := by
      simp only [Xs, Finset.mem_filter, not_and]
      intro _ h
      rw [hps] at h
      exact hne (Option.some.inj h).symm
    simp [ind, this]
  · intro h; exact absurd hs h
end Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
