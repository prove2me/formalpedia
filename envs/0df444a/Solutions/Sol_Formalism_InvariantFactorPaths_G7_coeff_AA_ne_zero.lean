-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.coeff_AA_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:03.155865+00:00
-- url     : https://prove2.me/submissions/3e4e1268-441e-4ca8-838c-027d851ba3f5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA

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
theorem _root_.solution {K : Type} [Field K] {p : ℕ} {x y : Fin 2} {n : Fin 2 →₀ ℕ}
    (h : MvPowerSeries.coeff n (AA K p x y) ≠ 0) :
    ∃ i j, i ≤ j ∧ n x = (p ^ 2) ^ i ∧ n y = p * (p ^ 2) ^ j := by
  change AA K p x y n ≠ 0 at h
  simp only [AA] at h
  by_contra hc
  push_neg at hc
  apply h
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  refine if_neg ?_
  rintro ⟨h1, h2, h3⟩
  exact hc i j h1 h2 h3
end Formalism.InvariantFactorPaths.G7
