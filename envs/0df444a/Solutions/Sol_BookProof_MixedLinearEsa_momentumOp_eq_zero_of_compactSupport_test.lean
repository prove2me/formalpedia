-- Prove2me | solution 1 for BookProof.MixedLinearEsa.momentumOp_eq_zero_of_compactSupport_test
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:25:29.04163+00:00
-- url     : https://prove2.me/submissions/cc7ae572-331c-427d-8399-1a0b9c122c3d

-- Generated from ChapterMixedLinearEsa.lean — solution of BookProof.MixedLinearEsa.momentumOp_eq_zero_of_compactSupport_test
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Theorems.Thm_BookProof_MixedLinearEsa_momentum_test_compactSupport_extend
import Theorems.Thm_BookProof_FourierMultiplierEsa_deficiencyTrivialAt_of_real_symbol
import Theorems.Thm_BookProof_FourierMultiplierEsa_fourier_momentumOp_apply
import Theorems.Thm_BookProof_StrichartzWave_inner_toLp_left
import Theorems.Thm_BookProof_StrichartzWave_opL2_apply
import Theorems.Thm_BookProof_StrichartzWave_schwartzEquiv_coe
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterStrichartzWave
open BookProof.MixedLinearEsa




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine
open BookProof.FourierMultiplierEsa
open BookProof.StrichartzWave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (m : V) {z : ℂ} (hz : z.im ≠ 0)
    (w : Lp ℂ 2 (volume : Measure V))
    (hw : ∀ φ : 𝓢(V, ℂ), HasCompactSupport (φ : V → ℂ) →
      ∫ x, (starRingEnd ℂ) ((momentumOp m φ) x) * (w x)
        = z * ∫ x, (starRingEnd ℂ) (φ x) * (w x)) :
    w = 0 := by

  refine deficiencyTrivialAt_of_real_symbol (momentumOp m)
    (fun x => 2 * Real.pi * (inner ℝ x m)) (fun f x => ?_) ?_ hz w ?_
  · simpa using fourier_momentumOp_apply f m x
  · exact contDiff_const.mul (((innerSL ℝ).flip m).contDiff)
  · intro v
    obtain ⟨f, rfl⟩ := (schwartzEquiv V).surjective v
    rw [opL2_apply, schwartzEquiv_coe, inner_toLp_left, inner_toLp_left]
    exact momentum_test_compactSupport_extend m z w hw f
