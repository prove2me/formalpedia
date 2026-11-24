-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.end_determined
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:54:14.942502+00:00
-- url     : https://prove2.me/submissions/993045ce-ba5e-47b4-b136-9fb002de5897

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_rho_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_DD_apply

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
theorem _root_.solution {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ μ' : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ (N + 1)) (hp' : IsPath n isVec B μ' (N + 1)) (he : μ (N + 1) = μ' (N + 1))
    (v : Bool) (hΓ : rho n N v (DD μ N) = rho n N v (DD μ' N)) : μ N = μ' N := by
  funext m
  have h1 := rho_inj v hΓ m
  rw [DD_apply, DD_apply] at h1
  have h2 := congrArg (Nat.cast : ℕ → ℤ) h1
  obtain ⟨-, -, hs⟩ := hp
  obtain ⟨-, -, hs'⟩ := hp'
  have a := hs N (Nat.lt_succ_self N)
  have b := hs' N (Nat.lt_succ_self N)
  have he' := congrFun he m
  by_cases hv : isVec N = true
  · rw [if_pos hv] at a b
    have x1 := a.1 m
    have x2 := b.1 m
    rw [Int.toNat_of_nonneg (abs_nonneg _), Int.toNat_of_nonneg (abs_nonneg _),
      abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h2
    linarith
  · rw [if_neg hv] at a b
    have x1 := a.1 m
    have x2 := b.1 m
    rw [Int.toNat_of_nonneg (abs_nonneg _), Int.toNat_of_nonneg (abs_nonneg _),
      abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h2
    linarith
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
