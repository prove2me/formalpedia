-- Prove2me | solution 1 for Formalism.HermitianLattices.GlobalBoundRefinements.moduli_minimum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:06.568103+00:00
-- url     : https://prove2.me/submissions/adb77492-b991-4a40-ba91-b2bc97291df9

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvNormSqConjRatioPowIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimesInProgressionCountLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GlobalBoundRefinements
namespace Formalism.HermitianLattices.GlobalBoundRefinements
theorem _root_.solution : Ms_min := by
  intro K inst1 inst2 hTC x hx
  have hxK : (x : K) ≠ 0 := by
    first
    | simpa using hx
    | exact fun h => hx (by exact_mod_cast h)
  have hwpos : ∀ w : NumberField.InfinitePlace K, 0 < w (x : K) := fun w => w.pos_iff.mpr hxK
  have hmult : ∀ w : NumberField.InfinitePlace K, w.mult = 2 := by
    intro w
    have hc := hTC.isComplex w
    first
    | exact NumberField.InfinitePlace.mult_isComplex ⟨w, hc⟩
    | (simp only [NumberField.InfinitePlace.mult]
       rw [if_neg (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hc)])
  have hprod := NumberField.InfinitePlace.prod_eq_abs_norm (x : K)
  simp only [hmult] at hprod
  have hN : (1 : ℝ) ≤ ((|Algebra.norm ℚ (x : K)| : ℚ) : ℝ) := by
    have h1 : (Algebra.norm ℤ x : ℚ) = Algebra.norm ℚ (x : K) := Algebra.coe_norm_int x
    have h2 : Algebra.norm ℤ x ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
    have h3 : (1 : ℤ) ≤ |Algebra.norm ℤ x| := Int.one_le_abs h2
    rw [← h1]
    exact_mod_cast h3
  have hsum : ∑ w : NumberField.InfinitePlace K, Real.log (w (x : K) ^ 2)
      = Real.log (∏ w : NumberField.InfinitePlace K, w (x : K) ^ 2) := by
    rw [Real.log_prod]
    intro w _
    exact pow_ne_zero 2 (hwpos w).ne'
  have hlogprod : 0 ≤ Real.log (∏ w : NumberField.InfinitePlace K, w (x : K) ^ 2) := by
    rw [hprod]
    exact Real.log_nonneg hN
  have hpt : ∀ w : NumberField.InfinitePlace K, 1 + Real.log (w (x : K) ^ 2) ≤ w (x : K) ^ 2 := by
    intro w
    have := Real.log_le_sub_one_of_pos (pow_pos (hwpos w) 2)
    linarith
  calc (Fintype.card (NumberField.InfinitePlace K) : ℝ)
      = ∑ _w : NumberField.InfinitePlace K, (1 : ℝ) := by simp
    _ ≤ ∑ w : NumberField.InfinitePlace K, (1 + Real.log (w (x : K) ^ 2)) := by
        rw [Finset.sum_add_distrib, hsum]
        linarith
    _ ≤ ∑ w : NumberField.InfinitePlace K, w (x : K) ^ 2 := Finset.sum_le_sum (fun w _ => hpt w)
end Formalism.HermitianLattices.GlobalBoundRefinements
