-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.pathWord_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:21.785273+00:00
-- url     : https://prove2.me/submissions/b3d7a150-7555-46f3-bed3-236667614273

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
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
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ μ' : ℕ → Fin n → ℤ) (c : ℤ)
    (Xr : ℕ → Fin n → R) : ∀ j, (∀ i ≤ j, μ i = μ' i) →
      pathWord isVec μ c Xr j = pathWord isVec μ' c Xr j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro h
    rw [stripPathWord_succ_eq_lemma_2, stripPathWord_succ_eq_lemma_2, ih (fun i hi => h i (by omega)), h (j + 1) le_rfl,
      h j (Nat.le_succ j)]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
