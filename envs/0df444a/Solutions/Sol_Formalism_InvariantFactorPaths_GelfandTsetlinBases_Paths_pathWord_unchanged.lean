-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.pathWord_unchanged
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:49.310264+00:00
-- url     : https://prove2.me/submissions/0899f638-cc1d-48c1-bec6-5ae9841a741a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight

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
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ)
    (c : ℤ) (Xr : ℕ → Fin n → R) : ∀ j : ℕ,
    (∀ i < j, colHeight (μ (i + 1)) c = colHeight (μ i) c) →
      pathWord isVec μ c Xr j = oneF ∧ colHeight (μ j) c = colHeight (μ 0) c := by
  intro j
  induction j with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ j ih =>
    intro h
    obtain ⟨a, b⟩ := ih fun i hi => h i (by omega)
    refine ⟨?_, (h j (by omega)).trans b⟩
    rw [pathWord, if_pos (h j (by omega))]
    exact a
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
