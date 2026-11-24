-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.isWeightedHomogeneous_zero_stripPathWord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:21.814872+00:00
-- url     : https://prove2.me/submissions/31ada2a4-aef8-4b16-b007-125a9df11490

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_wedge_term
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_contr_term
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace A1
section Top
variable {σ R M : Type*} [CommRing R] [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]
end Top
section Col
variable {R M : Type*} [CommRing R] [AddCommMonoid M] {n : ℕ}
private theorem stripPathWord_succ_eq_lemma_2 {R : Type*} [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ)
    (Xr : ℕ → Fin n → R) (i : ℕ) :
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c Xr (i + 1) = if Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ (i + 1)) c = Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight (μ i) c then
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c Xr i else Formalism.InvariantFactorPaths.GelfandTsetlinBases.stepF (isVec i == decide (1 ≤ c)) (Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c Xr i) (Xr i) := by
  rfl
private theorem isWH_sum_lemma_3 {σ R M ι : Type*} [CommRing R] [AddCommMonoid M] {w : σ → M} (s : Finset ι)
    (φ : ι → MvPolynomial σ R) (d : M) (h : ∀ i ∈ s, IsWeightedHomogeneous w (φ i) d) :
    IsWeightedHomogeneous w (∑ i ∈ s, φ i) d := by
  intro e he
  rw [coeff_sum] at he
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
  exact h i hi hne
end Col
end A1
namespace A1
end A1
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
variable {R M : Type*} [CommRing R] [AddCommMonoid M] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
theorem _root_.solution (w : ℕ × Fin n → M) (N : ℕ) (hw : ∀ x : ℕ × Fin n, x.1 ≠ N → w x = 0)
    (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ) : ∀ j ≤ N, ∀ J,
    IsWeightedHomogeneous w (pathWord isVec μ c (XR R n) j J) 0 := by
  intro j
  induction j with
  | zero =>
    intro _ J
    show IsWeightedHomogeneous w (if J = ∅ then (1 : MvPolynomial (ℕ × Fin n) R) else 0) 0
    split_ifs
    · apply isWeightedHomogeneous_one
    · apply isWeightedHomogeneous_zero
  | succ j ih =>
    intro hj J
    have hK : ∀ J, IsWeightedHomogeneous w (Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c (XR R n) j J) 0 := ih (by omega)
    have hw0 : ∀ m : Fin n, w (j, m) = 0 := fun m => hw (j, m) (show j ≠ N by omega)
    rw [stripPathWord_succ_eq_lemma_2]
    split_ifs with hc
    · exact hK J
    · unfold Formalism.InvariantFactorPaths.GelfandTsetlinBases.stepF
      split
      · show IsWeightedHomogeneous w (∑ m ∈ J, ((Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg J m : ℤ) : MvPolynomial (ℕ × Fin n) R) *
          Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c (XR R n) j (J.erase m) * XR R n j m) 0
        apply isWH_sum_lemma_3
        intro m _
        have := wedge_term w _ hK j J m
        rwa [hw0] at this
      · show IsWeightedHomogeneous w (∑ m ∈ Jᶜ, ((Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg J m : ℤ) : MvPolynomial (ℕ × Fin n) R) *
          XR R n j m * Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec μ c (XR R n) j (insert m J)) 0
        apply isWH_sum_lemma_3
        intro m _
        have := contr_term w _ hK j J m
        rwa [hw0] at this
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
