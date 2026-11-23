-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.bpt_add_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:34.288842+00:00
-- url     : https://prove2.me/submissions/be1e0a08-0bb0-4f04-96a7-1dbc3a4da765

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne

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
variable {Λ : Type} [AddCommGroup Λ] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.BoxAverageLimits
theorem _root_.solution (e : ι → Λ) (c : Λ) (m : ι → ℕ) (j : ι) :
    bpt e c m + e j = bpt e c (m + Pi.single j 1) := by
  unfold bpt
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  rw [add_assoc]
  congr 2
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ j) h
end Formalism.FourierDecayAlt.P.BoxAverageLimits
