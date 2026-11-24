-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.exists_cols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:10:11.552923+00:00
-- url     : https://prove2.me/submissions/83a10148-4d1a-4062-801f-d37aa3b39e28

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_colHeight_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_pathWord_unchanged
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_path_finite


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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
theorem _root_.solution {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ N) : ∃ F : Finset ℤ, Cols isVec μ N F := by
  have hfin : (⋃ i ∈ Set.Iio N, {c : ℤ | colHeight (μ (i + 1)) c ≠ colHeight (μ i) c}).Finite :=
    Set.Finite.biUnion (Set.finite_Iio N) fun i hi => Paths.path_finite hp hi
  refine ⟨hfin.toFinset, fun c hc => ?_⟩
  have hun : ∀ i < N, colHeight (μ (i + 1)) c = colHeight (μ i) c := by
    intro i hi
    by_contra hne
    exact hc (hfin.mem_toFinset.2 (Set.mem_biUnion (show i ∈ Set.Iio N from hi) hne))
  refine ⟨fun R _ Xr => (Paths.pathWord_unchanged isVec μ c Xr N hun).1, fun I hI => ?_⟩
  have b := (Paths.pathWord_unchanged isVec μ c (fun _ _ => (0 : ℤ)) N hun).2
  have hcard := hI c
  rw [b, hp.1, Paths.colHeight_zero] at hcard
  apply Finset.card_eq_zero.1
  rw [hcard]; split_ifs <;> simp
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev
