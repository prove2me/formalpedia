-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ValuationParity.charge_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:52:48.340035+00:00
-- url     : https://prove2.me/submissions/054c2b60-0537-41f6-8e1a-87157478a23a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryAOneParity
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ValuationParity_val_odd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ValuationParity_parity_ne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ValuationParity_isLeast_val

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.ValuationParity
namespace Formalism.InvariantFactorPaths.G7.ValuationParity
theorem _root_.solution (hL : ChargeLemma) {ν r0 r1 E : ℕ} [NeZero ν] (p : ℕ) (hp : 1 ≤ p)
    (φ : PhiI ν r0 r1 E) :
    ∃ s s' : ZMod (2 * ν), ((s = pairFirst φ ∧ s' = pairSecond φ) ∨ (s = pairSecond φ ∧ s' = pairFirst φ)) ∧
      (s' - s).val % 2 = 1 ∧ s'.val % 2 ≠ s.val % 2 ∧
      p ^ (s' - s).val ≤ dAof p φ (s, φ.2.2.2.2) := by
  haveI : NeZero (2 * ν) := ⟨by have := NeZero.ne ν; omega⟩
  have hA1 : p ^ (1 + 2 * φ.2.1.val) ≤ dAof p φ (pairFirst φ, φ.2.2.2.2) := by
    simp only [dAof, Finsupp.add_apply, Finsupp.single_eq_same]
    exact Nat.le_add_right _ _
  have hA2 : p ^ (2 * φ.2.2.1.val) ≤ dAof p φ (pairSecond φ, φ.2.2.2.2) := by
    simp only [dAof, Finsupp.add_apply, Finsupp.single_eq_same]
    exact Nat.le_add_left _ _
  by_cases hij : φ.2.2.1.val ≤ φ.2.1.val
  · have hodd : pairSecond φ - pairFirst φ = 1 + 2 * ((φ.2.1.val : ZMod (2 * ν)) - (φ.2.2.1.val : ZMod (2 * ν))) := by
      unfold pairFirst pairSecond
      ring
    have hv := val_odd hodd
    have heq : pairFirst φ + ((1 + 2 * φ.2.1.val : ℕ) : ZMod (2 * ν)) =
        pairSecond φ + ((2 * φ.2.2.1.val : ℕ) : ZMod (2 * ν)) := by
      unfold pairFirst pairSecond
      push_cast
      ring
    have hd := hL (2 * ν) (pairFirst φ) (pairSecond φ) (1 + 2 * φ.2.1.val) (2 * φ.2.2.1.val) _ (by omega) heq
      (isLeast_val (pairFirst φ) (pairSecond φ) (by omega))
    exact ⟨pairFirst φ, pairSecond φ, Or.inl ⟨rfl, rfl⟩, hv, parity_ne hodd,
      le_trans (Nat.pow_le_pow_right hp hd) hA1⟩
  · have hodd : pairFirst φ - pairSecond φ =
        1 + 2 * ((φ.2.2.1.val : ZMod (2 * ν)) - (φ.2.1.val : ZMod (2 * ν)) - 1) := by
      unfold pairFirst pairSecond
      ring
    have hv := val_odd hodd
    have heq : pairSecond φ + ((2 * φ.2.2.1.val : ℕ) : ZMod (2 * ν)) =
        pairFirst φ + ((1 + 2 * φ.2.1.val : ℕ) : ZMod (2 * ν)) := by
      unfold pairFirst pairSecond
      push_cast
      ring
    have hd := hL (2 * ν) (pairSecond φ) (pairFirst φ) (2 * φ.2.2.1.val) (1 + 2 * φ.2.1.val) _ (by omega) heq
      (isLeast_val (pairSecond φ) (pairFirst φ) (by omega))
    exact ⟨pairSecond φ, pairFirst φ, Or.inr ⟨rfl, rfl⟩, hv, parity_ne hodd,
      le_trans (Nat.pow_le_pow_right hp hd) hA2⟩
end Formalism.InvariantFactorPaths.G7.ValuationParity
