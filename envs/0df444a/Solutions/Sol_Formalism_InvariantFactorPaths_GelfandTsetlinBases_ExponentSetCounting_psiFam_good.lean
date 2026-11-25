-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.psiFam_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:20:21.178066+00:00
-- url     : https://prove2.me/submissions/96e0c9ef-9994-4b45-9308-e8908a9805b7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_UnitAndFieldPowerLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_valuation_products_components


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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
theorem _root_.solution (k : Type) [Field k] (hn : 1 ≤ n) {i N : ℕ} (hi : i ≤ N) (isVec : ℕ → Bool) (B : ℕ → ℕ)
    (θ : WithBot ℤ) (M : WithTop ℤ) (x : PathIdx n N isVec B) (hx : GoodW θ M (x.1.1 i)) :
    GoodG isVec i θ M (psiFam k n N isVec B x) := by
  obtain ⟨h1, h2⟩ := valuation_products_components k n N i isVec B x.1.1 x.1.2 x.2.1 x.2.2.2.1 hi
  constructor
  · intro t ht
    have a1 := hx.1 ⟨n - 1, by omega⟩ (by simp only; omega)
    have a2 := h1 ⟨n - 1, by omega⟩ (by simp only; omega)
    rw [ht, WithBot.coe_le_coe] at a1
    exact (WithTop.coe_le_coe.2 a1).trans a2
  · intro t ht
    have a1 := hx.2 ⟨0, by omega⟩ rfl
    have a2 := h2 ⟨0, by omega⟩ rfl
    rw [ht, WithTop.coe_le_coe] at a1
    exact a2.trans (WithBot.coe_le_coe.2 a1)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
