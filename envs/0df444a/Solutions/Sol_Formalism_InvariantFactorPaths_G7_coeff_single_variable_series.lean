-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.coeff_single_variable_series
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:40.159855+00:00
-- url     : https://prove2.me/submissions/c1fada71-a43c-45c6-818e-43281bfc2d32

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
theorem _root_.solution {K ι : Type} [Field K] [DecidableEq ι] (x : ι) (f : PowerSeries K)
    (n : ι →₀ ℕ) : MvPowerSeries.coeff n (at1 x f) =
      if n = Finsupp.single x (n x) then PowerSeries.coeff (n x) f else 0 := by
  have hs : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  unfold at1
  rw [PowerSeries.coeff_subst hs]
  simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial, smul_eq_mul]
  rw [finsum_eq_single _ (n x)]
  · simp
  · intro d hd
    rw [if_neg, mul_zero]
    intro h
    apply hd
    rw [h]
    simp
end Formalism.InvariantFactorPaths.G7
