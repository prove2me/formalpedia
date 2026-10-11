-- Prove2me | solution 1 for BookProof.ChapterU.born_conditioning
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:57:05.965991+00:00
-- url     : https://prove2.me/submissions/03966943-00df-402b-af39-4fa65882b4fb

-- Generated from ChapterU.lean — solution of BookProof.ChapterU.born_conditioning
import Mathlib
import Definitions.Def_ChapterU
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterU



open MeasureTheory
open scoped ENNReal ProbabilityTheory TensorProduct

variable {X : Type*} [MeasurableSpace X]

set_option maxHeartbeats 1000000 in
theorem solution (Ψ : X → ℂ) (μ : Measure X) (E : Set X)
    (hE : MeasurableSet E) (hpos : bornMeasure Ψ μ E ≠ 0)
    (_hfin : bornMeasure Ψ μ E ≠ ∞) :
    bornMeasure (conditionedState Ψ μ E) μ = (bornMeasure Ψ μ)[|E] := by

  ext s hs;
  simp only [bornMeasure, norm_nonneg, ENNReal.ofReal_pow, ofReal_norm, withDensity_apply,
      ProbabilityTheory.cond_apply, MeasurableSet.inter, hs, hE];
  simp only [conditionedState, Complex.real_smul, Complex.ofReal_inv, enorm_mul];
  simp only [mul_pow, hs, ← lintegral_indicator, hE, MeasurableSet.inter];
  have h_const : (∫⁻ x, s.indicator (fun x => ‖(↑√((bornMeasure Ψ μ) E).toReal)⁻¹‖ₑ ^ 2 *
      ‖E.indicator Ψ x‖ₑ ^ 2) x ∂μ) = ‖(↑√((bornMeasure Ψ μ) E).toReal)⁻¹‖ₑ ^ 2 * ∫⁻ x, s.indicator
          (fun x => ‖E.indicator Ψ x‖ₑ ^ 2) x ∂μ := by
    rw [ ← MeasureTheory.lintegral_const_mul' ];
    · congr with x ; by_cases hx : x ∈ s <;> simp [ hx ];
    · finiteness
  convert h_const using 2;
  · norm_num [ ENorm.enorm ];
  · rw [ ← ENNReal.toReal_eq_toReal_iff' ] <;> norm_num;
    · unfold bornMeasure; aesop;
    · unfold bornMeasure at * ; aesop;
  · congr with x ; by_cases hx : x ∈ E <;> by_cases hx' : x ∈ s <;> simp [ hx, hx' ]
