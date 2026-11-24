-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.coeff_frobVar_AA_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:24.284111+00:00
-- url     : https://prove2.me/submissions/126b2362-2350-4f8e-b8f5-bc197319c325

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_powq_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_AA_of
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_finset_fin_two_eq_cases

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
theorem _root_.solution (K : Type) [Field K] {p : ℕ} (hp : 2 ≤ p) {x y : Fin 2} (hxy : x ≠ y)
    {n : Fin 2 →₀ ℕ} {i j : ℕ} (hij : i ≤ j) (hx : n x = p * (p ^ 2) ^ i)
    (hy : n y = (p ^ 2) ^ (j + 1)) :
    MvPowerSeries.coeff n (frobVar p (AA K p x y)) = ((p : K) ^ (i + j + 1))⁻¹ := by
  have hn : n = p • (Finsupp.single x ((p ^ 2) ^ i) + Finsupp.single y (p * (p ^ 2) ^ j)) := by
    ext z
    rcases finset_fin_two_eq_cases x y hxy z with rfl | rfl
    · simp [hx, hxy.symm]
    · simp [hy, hxy, powq_succ]
  rw [hn, coeff_frobVar_smul (by omega)]
  exact coeff_AA_of K hp hij (by simp [hxy.symm]) (by simp [hxy])
end Formalism.InvariantFactorPaths.G7
