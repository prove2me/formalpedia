-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.schur_lattice_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:51:13.483239+00:00
-- url     : https://prove2.me/submissions/d6dd1b32-63fb-4581-9de8-4b6ac44edc8e

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RowNormSquareBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_schur_two_factor_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset SchurNormSquareBounds
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.SchurLattice := by
  classical
  intro H _ _ G _ La ι PP _ T τ V P φ a ε hinj hco hφ hS ha hV
  constructor
  · have := schur_two_factor_bound H G La ι PP T τ V P φ a a ε hinj hco hφ hS
      (fun p t ht => ⟨ha p t ht, ha p t ht⟩) hV
    refine this.trans (le_of_eq ?_)
    congr 2
    rw [sum_comm]
    exact sum_congr rfl fun t _ => sum_congr rfl fun p _ => by ring
  · intro f m hcard hε hm ham
    refine add_le_add le_rfl ?_
    have h1 : ∑ t ∈ T, ∑ p, a p t ≤ ∑ t ∈ T, (3 : ℝ) ^ f * m t := by
      refine sum_le_sum fun t ht => ?_
      calc ∑ p, a p t ≤ ∑ _p : PP, m t := sum_le_sum fun p _ => ham p t ht
        _ = (Fintype.card PP : ℝ) * m t := by simp
        _ ≤ (3 : ℝ) ^ f * m t := by
          refine mul_le_mul_of_nonneg_right ?_ (hm t ht)
          exact_mod_cast hcard
    calc ε * ∑ t ∈ T, ∑ p, a p t ≤ ε * ∑ t ∈ T, (3 : ℝ) ^ f * m t :=
          mul_le_mul_of_nonneg_left h1 hε
      _ = (3 : ℝ) ^ f * ε * ∑ t ∈ T, m t := by rw [← mul_sum]; ring
end Formalism.FourierDecayAlt.P
