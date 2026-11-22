-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.coeff_product_single_variables
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:14:36.444381+00:00
-- url     : https://prove2.me/submissions/38eaba10-9e6e-43a2-8c5b-f4de718cb0b6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_single_variable_series

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
theorem _root_.solution {K ι : Type} [Field K] {x y : ι} (hxy : x ≠ y)
    (hall : ∀ z : ι, z = x ∨ z = y) (f g : PowerSeries K) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (at1 x f * at1 y g) =
      PowerSeries.coeff (n x) f * PowerSeries.coeff (n y) g := by
  classical
  rw [MvPowerSeries.coeff_mul,
    Finset.sum_eq_single (Finsupp.single x (n x), Finsupp.single y (n y))]
  · simp [coeff_single_variable_series]
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    simp only at hab
    simp only [coeff_single_variable_series]
    by_cases ha : a = Finsupp.single x (a x)
    · by_cases hb : b = Finsupp.single y (b y)
      · exfalso
        apply hne
        have hbx : b x = 0 := by rw [hb, Finsupp.single_apply, if_neg hxy.symm]
        have hay : a y = 0 := by rw [ha, Finsupp.single_apply, if_neg hxy]
        have hx : n x = a x := by rw [← hab, Finsupp.add_apply, hbx, add_zero]
        have hy : n y = b y := by rw [← hab, Finsupp.add_apply, hay, zero_add]
        rw [hx, hy, ← ha, ← hb]
      · rw [if_neg hb, mul_zero]
    · rw [if_neg ha, zero_mul]
  · intro h
    exfalso
    apply h
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    ext z
    rcases hall z with rfl | rfl <;> simp [hxy, hxy.symm]
end Formalism.InvariantFactorPaths.G7
