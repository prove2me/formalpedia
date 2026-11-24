-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:00.911539+00:00
-- url     : https://prove2.me/submissions/7748e879-5a19-4440-b44a-586aff1a7d3a

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs

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
open Letters
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (N : ℕ) (T : ℕ → ℕ → ℤ) (S : ℕ → ℕ → ℕ) (act : ℕ → Bool)
    (h0 : ∀ u, T 0 u ≤ S u 0)
    (hA : ∀ i u, i < N → act (i + 1) = true → T (i + 1) (u + 1) ≤ T i u ∧ S (u + 1) (i + 1) = S u i)
    (hA0 : ∀ i, i < N → act (i + 1) = true → T (i + 1) 0 - T i 0 ≤ (S 0 (i + 1) : ℤ) - S 0 i)
    (hI : ∀ i u, i < N → act (i + 1) = false → T (i + 1) u ≤ T i u ∧ S u (i + 1) = S u i) :
    ∀ i, i ≤ N → ∀ u, T i u ≤ S u i := by
  intro i
  induction i with
  | zero =>
    intro _ u
    exact h0 u
  | succ i ih =>
    intro hi u
    have ih' := ih (by omega)
    by_cases ha : act (i + 1) = true
    · cases u with
      | zero =>
        have h1 := hA0 i (by omega) ha
        have h2 := ih' 0
        linarith
      | succ u =>
        obtain ⟨h1, h2⟩ := hA i u (by omega) ha
        rw [h2]
        exact h1.trans (ih' u)
    · have ha' : act (i + 1) = false := by simpa using ha
      obtain ⟨h1, h2⟩ := hI i u (by omega) ha'
      rw [h2]
      exact h1.trans (ih' u)
end Formalism.InvariantFactorPaths.BranchingDimensions
