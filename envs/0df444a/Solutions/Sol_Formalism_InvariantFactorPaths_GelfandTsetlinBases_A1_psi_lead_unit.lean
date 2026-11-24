-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.psi_lead_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:20:14.970803+00:00
-- url     : https://prove2.me/submissions/9650f13e-fe72-4700-8e1c-ecde4a5d3e79

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_psi_lead

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
theorem _root_.solution (k : Type) [Field k] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ (N + 1)) :
    ∃ u : kˣ, weightedHomogeneousComponent (wt n N (isVec N)) (rho n N (isVec N) (DD μ N))
        (psiPath k isVec μ (N + 1) (canIdx (μ (N + 1)))) =
      u • (psiPath k isVec μ N (canIdx (μ N)) * monomial (DD μ N) 1) := by
  obtain ⟨ε, hε, hL⟩ := psi_lead k hp
  have hne : (ε : k) ≠ 0 := by
    rcases hε with rfl | rfl <;> simp
  refine ⟨Units.mk0 _ hne, ?_⟩
  rw [hL.2, Units.smul_def, Units.val_mk0, smul_eq_C_mul, map_intCast, mul_assoc]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
