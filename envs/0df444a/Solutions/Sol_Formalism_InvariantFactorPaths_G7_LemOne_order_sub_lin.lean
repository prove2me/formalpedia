-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.order_sub_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:19.650637+00:00
-- url     : https://prove2.me/submissions/e8a2581c-5371-46ff-97b8-2d0a3388d605

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul

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
open Formalism.InvariantFactorPaths.G7.LemOne
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.LemOne
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF0 : MvPowerSeries.constantCoeff F = 0)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1) :
    ((2 : ℕ) : ℕ∞) ≤ (F - (MvPowerSeries.X 0 + MvPowerSeries.X 1)).order := by
  classical
  refine MvPowerSeries.nat_le_order fun d hd => ?_
  have hdeg : d.degree = d 0 + d 1 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  rw [map_sub, map_add, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X]
  rcases Nat.lt_or_ge d.degree 1 with h0 | h1
  · have hd0 : d = 0 := by
      ext x; fin_cases x
      · simp; omega
      · simp; omega
    subst hd0
    have : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) F = 0 := by
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hF0
    rw [this, if_neg, if_neg]
    · simp
    · intro h; have := congrArg (fun e => e 1) h; simp at this
    · intro h; have := congrArg (fun e => e 0) h; simp at this
  · have hd1 : d.degree = 1 := by omega
    rw [hF1 d hd1]
    by_cases h : d 0 = 1
    · have : d = Finsupp.single 0 1 := by
        ext x; fin_cases x
        · simpa using h
        · simp; omega
      subst this
      rw [if_pos rfl, if_neg]
      · simp
      · intro h; have := congrArg (fun e => e 1) h; simp at this
    · have : d = Finsupp.single 1 1 := by
        ext x; fin_cases x
        · simp; omega
        · simp; omega
      subst this
      rw [if_pos rfl, if_neg]
      · simp
      · intro h; have := congrArg (fun e => e 1) h; simp at this
end Formalism.InvariantFactorPaths.G7.LemOne
