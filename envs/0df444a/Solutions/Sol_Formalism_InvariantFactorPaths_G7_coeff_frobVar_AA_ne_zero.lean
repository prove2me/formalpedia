-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.coeff_frobVar_AA_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:24.108883+00:00
-- url     : https://prove2.me/submissions/839c8b84-2885-4eec-8ccf-7d03c36503de

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_powq_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_AA_ne_zero

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {K : Type} [Field K] {p : ℕ} (hp : 2 ≤ p) {x y : Fin 2}
    {n : Fin 2 →₀ ℕ} (h : MvPowerSeries.coeff n (frobVar p (AA K p x y)) ≠ 0) :
    ∃ i j, i ≤ j ∧ n x = p * (p ^ 2) ^ i ∧ n y = (p ^ 2) ^ (j + 1) := by
  obtain ⟨m, rfl, hm⟩ := coeff_frobVar_ne_zero (by omega) h
  obtain ⟨i, j, hij, hx, hy⟩ := coeff_AA_ne_zero hm
  exact ⟨i, j, hij, by simp [hx], by simp [hy, powq_succ]⟩
end Formalism.InvariantFactorPaths.G7
