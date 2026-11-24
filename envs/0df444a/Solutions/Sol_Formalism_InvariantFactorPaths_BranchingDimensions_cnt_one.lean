-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.cnt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:00.826334+00:00
-- url     : https://prove2.me/submissions/c295a7a2-d4f6-4da0-b00e-80acea37d00b

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementL
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LDigits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (T Q c : ℕ) (hT : T ≤ Q) : cnt T Q 1 c = if c % Q < T then 1 else 0 := by
  have hbij : Function.Bijective (fun a : Fin T => (fun _ : Fin 1 => a)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun u => u 0, fun a => rfl, fun u => ?_⟩
    funext i
    rw [Subsingleton.elim i 0]
  have step : (∑ u : Fin 1 → Fin T, if (∑ l, (u l : ℕ)) % Q = c % Q then 1 else 0) =
      ∑ a : Fin T, if (a : ℕ) = c % Q then 1 else 0 := by
    symm
    refine Fintype.sum_bijective _ hbij _ _ (fun a => ?_)
    simp only [Fin.sum_univ_one]
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le a.isLt hT)]
  unfold cnt
  rw [Finset.card_filter, step]
  by_cases h : c % Q < T
  · rw [if_pos h, Finset.sum_eq_single (⟨c % Q, h⟩ : Fin T)]
    · simp
    · intro b _ hb
      exact if_neg (fun e => hb (Fin.ext e))
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro a _
    exact if_neg (fun e => h (lt_of_eq_of_lt e.symm a.isLt))
end Formalism.InvariantFactorPaths.BranchingDimensions
