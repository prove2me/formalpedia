-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.coeff_frobVar_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:16.926806+00:00
-- url     : https://prove2.me/submissions/e4f8118c-1b51-42e0-b588-39e0bcf7564d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_of_not_dvd

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
theorem _root_.solution {K ι : Type} [Field K] {p : ℕ} (hp : p ≠ 0)
    {f : MvPowerSeries ι K} {n : ι →₀ ℕ} (h : MvPowerSeries.coeff n (frobVar p f) ≠ 0) :
    ∃ m : ι →₀ ℕ, n = p • m ∧ MvPowerSeries.coeff m f ≠ 0 := by
  have hd : ∀ i, p ∣ n i := by
    intro i
    by_contra hc
    exact h (coeff_frobVar_of_not_dvd hp f hc)
  have hn : n = p • n.mapRange (· / p) (by simp) := by
    ext i
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    exact (Nat.mul_div_cancel' (hd i)).symm
  refine ⟨_, hn, ?_⟩
  rw [hn, coeff_frobVar_smul hp] at h
  exact h
end Formalism.InvariantFactorPaths.G7
