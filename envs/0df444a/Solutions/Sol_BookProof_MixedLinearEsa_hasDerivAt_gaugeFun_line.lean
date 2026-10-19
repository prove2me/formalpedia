-- Prove2me | solution 1 for BookProof.MixedLinearEsa.hasDerivAt_gaugeFun_line
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:46:20.018997+00:00
-- url     : https://prove2.me/submissions/2f880ed8-4ab4-45ae-b93a-5182d51c8916

import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.hasDerivAt_gaugeFun_line
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]




omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem solution (b m : V) (hm : m ≠ 0) (x : V) :
    HasDerivAt (fun t : ℝ => gaugeFun b m (x + t • m))
      (gaugeFun b m x * (Complex.I * ((-(inner ℝ x b : ℝ) : ℝ) : ℂ))) 0 := by
  have hM : ‖m‖ ≠ 0 := norm_ne_zero_iff.mpr hm
  set a : ℝ := inner ℝ x b with ha
  set c : ℝ := inner ℝ x m with hc
  set B : ℝ := inner ℝ b m with hB
  set M : ℝ := ‖m‖ ^ 2 with hMdef
  have hM0 : M ≠ 0 := pow_ne_zero 2 hM
  have e : (fun t : ℝ => gaugePhase b m (x + t • m))
      = fun t => (-(a * c) / M + B * c ^ 2 / (2 * M ^ 2))
          + (-(B * c + a * M) / M + B * c / M) * t + (-(B * M) / M + B * M ^ 2 / (2 * M ^ 2)) * t ^ 2 := by
    funext t
    have h1 : (inner ℝ (x + t • m) b : ℝ) = a + t * B := by
      rw [inner_add_left, inner_smul_left, real_inner_comm b m]; simp [ha, hB]
    have h2 : (inner ℝ (x + t • m) m : ℝ) = c + t * M := by
      rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]; simp [hc, hMdef]
    simp only [gaugePhase, h1, h2]
    rw [← hB]
    have : ‖m‖ ^ 4 = M ^ 2 := by rw [hMdef]; ring
    rw [this, ← hMdef]
    field_simp
    ring
  have hQ : (-(B * c + a * M) / M + B * c / M) = -a := by field_simp; ring
  have hθ : HasDerivAt (fun t : ℝ => gaugePhase b m (x + t • m)) (-a) 0 := by
    rw [e]
    have h := (((hasDerivAt_id' (0:ℝ)).const_mul (-(B * c + a * M) / M + B * c / M)).const_add
      (-(a * c) / M + B * c ^ 2 / (2 * M ^ 2))).add
      ((hasDerivAt_pow 2 (0:ℝ)).const_mul (-(B * M) / M + B * M ^ 2 / (2 * M ^ 2)))
    refine h.congr_deriv ?_
    rw [hQ]; simp
  have hc' : HasDerivAt (fun t : ℝ => Complex.I * ((gaugePhase b m (x + t • m) : ℝ) : ℂ))
      (Complex.I * ((-a : ℝ) : ℂ)) 0 := hθ.ofReal_comp.const_mul Complex.I
  have hexp := hc'.cexp
  simp only [zero_smul, add_zero] at hexp
  unfold gaugeFun
  convert hexp using 1

