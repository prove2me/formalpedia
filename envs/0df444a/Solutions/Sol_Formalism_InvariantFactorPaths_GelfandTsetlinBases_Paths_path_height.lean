-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.path_height
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:49.457279+00:00
-- url     : https://prove2.me/submissions/d5560711-50f5-4e5a-b0e6-2eaa908518a2

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_strip_height

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
theorem _root_.solution {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) {i : ℕ} (hi : i < N) (c : ℤ) :
    if isVec i then
      colHeight (μ (i + 1)) c = colHeight (μ i) c ∨ colHeight (μ (i + 1)) c = colHeight (μ i) c + 1
    else
      colHeight (μ (i + 1)) c = colHeight (μ i) c ∨ colHeight (μ (i + 1)) c + 1 = colHeight (μ i) c := by
  obtain ⟨-, ha, hs⟩ := hp
  have h := hs i hi
  by_cases hv : isVec i = true
  · rw [if_pos hv] at h ⊢
    exact strip_height (ha _ hi) (ha _ hi.le) h c
  · rw [if_neg hv] at h ⊢
    rcases strip_height (ha _ hi.le) (ha _ hi) h c with e | e
    · exact Or.inl e.symm
    · exact Or.inr e.symm
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
