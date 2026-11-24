-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.path_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:47:21.230148+00:00
-- url     : https://prove2.me/submissions/cf68e758-e24b-4d97-9d31-ca35d7c954fa

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_strip_bound

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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
theorem _root_.solution {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) : ∀ i ≤ N, ∀ m, |μ i m| ≤ ((∑ k ∈ range i, B k : ℕ) : ℤ) := by
  obtain ⟨h0, _, hstep⟩ := hp
  intro i
  induction i with
  | zero =>
    intro _ m
    simp [h0]
  | succ i ih =>
    intro hi m
    have ih' := ih (by omega) m
    have hs := hstep i (by omega)
    rw [Finset.sum_range_succ, Nat.cast_add]
    split_ifs at hs with hv
    · have := strip_bound hs m
      rw [abs_le] at ih' ⊢
      constructor <;> linarith [this.1, this.2]
    · have := strip_bound hs m
      rw [abs_le] at ih' ⊢
      constructor <;> linarith [this.1, this.2]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
