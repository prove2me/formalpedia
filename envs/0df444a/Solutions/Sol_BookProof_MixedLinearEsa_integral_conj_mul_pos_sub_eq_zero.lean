-- Prove2me | solution 1 for BookProof.MixedLinearEsa.integral_conj_mul_pos_sub_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T07:03:08.552278+00:00
-- url     : https://prove2.me/submissions/b3aecda9-86f7-480e-8a1f-1e3e415f6a08

-- Generated from ChapterMixedLinearEsa.lean — solution of BookProof.MixedLinearEsa.integral_conj_mul_pos_sub_eq_zero
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Theorems.Thm_BookProof_StrichartzWave_inner_toLp_left
import Theorems.Thm_BookProof_StrichartzWave_integrable_conj_schwartz_mul
import Theorems.Thm_BookProof_StrichartzWave_opL2_apply
import Theorems.Thm_BookProof_StrichartzWave_schwartzEquiv_coe
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStrichartzWave
open BookProof.MixedLinearEsa




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine
open BookProof.StrichartzWave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! `posOp_apply` and its helper exist in the source chapter but no
`Theorems/Thm_…` stub was generated for them, so a solution may not import them.
Both are one-line lemmas over declarations the platform DOES serve (`posOp` in
the published bundle, `smulLeftCLM_apply_apply` from Mathlib), so they are stated
locally as `private` and the file stays standalone.
-/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem hasTemperateGrowth_innerC' (b : V) :
    (fun x : V => ((inner ℝ x b : ℝ) : ℂ)).HasTemperateGrowth :=
  Complex.ofRealCLM.hasTemperateGrowth.comp ((innerSL ℝ).flip b).hasTemperateGrowth

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem posOp_apply' (b : V) (f : 𝓢(V, ℂ)) (x : V) :
    (posOp b f) x = ((inner ℝ x b : ℝ) : ℂ) * f x := by
  simp [posOp, smulLeftCLM_apply_apply (hasTemperateGrowth_innerC' b)]

set_option maxHeartbeats 1000000 in
theorem solution (b : V) (z : ℂ) (u : Lp ℂ 2 (volume : Measure V))
    (hu : ∀ v : schwartzDomain V,
      (inner ℂ (opL2 (posOp b) v) u : ℂ) = z * inner ℂ (v : Lp ℂ 2 _) u)
    (f : 𝓢(V, ℂ)) :
    ∫ x, (starRingEnd ℂ) (f x) * (((inner ℝ x b : ℝ) : ℂ) - z) * (u x) = 0 := by

  have h1 := hu (schwartzEquiv V f)
  rw [opL2_apply, schwartzEquiv_coe, inner_toLp_left, inner_toLp_left] at h1
  have hint1 : Integrable (fun x => (starRingEnd ℂ) (f x) * (u x)) (volume : Measure V) :=
    integrable_conj_schwartz_mul f u
  have hint2 : Integrable (fun x => (starRingEnd ℂ) ((posOp b f) x) * (u x))
      (volume : Measure V) := integrable_conj_schwartz_mul (posOp b f) u
  have hcomb : ∫ x, ((starRingEnd ℂ) ((posOp b f) x) * (u x)
      - z * ((starRingEnd ℂ) (f x) * (u x))) = 0 := by
    rw [integral_sub hint2 (hint1.const_mul z), MeasureTheory.integral_const_mul, h1]
    ring
  rw [← hcomb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [posOp_apply', map_mul, Complex.conj_ofReal]
  ring
