-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.pathWord_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:03:20.199093+00:00
-- url     : https://prove2.me/submissions/d73109ca-599c-4f64-99ec-654f93575541

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_hom_step

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
open Paths
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
theorem _root_.solution (R : Type*) [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ)
    (c : ℤ) (i : ℕ) : ∀ (j : ℕ) (J : Finset (Fin n)),
    IsWeightedHomogeneous (fun x : ℕ × Fin n => if x.1 = i then 1 else 0)
      (pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) j J)
      (if i < j ∧ colHeight (μ (i + 1)) c ≠ colHeight (μ i) c then 1 else 0) := by
  intro j
  induction j with
  | zero =>
    intro J
    rw [if_neg (by omega)]
    show IsWeightedHomogeneous _ (if J = ∅ then 1 else 0) 0
    split
    · exact isWeightedHomogeneous_one _ _
    · exact isWeightedHomogeneous_zero _ _ _
  | succ j ih =>
    intro J
    by_cases hch : colHeight (μ (j + 1)) c = colHeight (μ j) c
    · rw [pathWord, if_pos hch]
      have := ih J
      convert this using 2
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 h1) with h | h
        · exact h
        · subst h; exact absurd hch h2
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
    · rw [pathWord, if_neg hch]
      have := hom_step (fun x : ℕ × Fin n => if x.1 = i then 1 else 0) (isVec j == decide (1 ≤ c))
        (pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) j)
        (fun a => (X (j, a) : MvPolynomial (ℕ × Fin n) R)) _ (if j = i then 1 else 0) ih
        (fun m => isWeightedHomogeneous_X R _ (j, m)) J
      convert this using 1
      by_cases hji : j = i
      · subst hji
        simp [hch]
      · have : (i < j + 1) ↔ i < j := by omega
        simp [hji, this]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
