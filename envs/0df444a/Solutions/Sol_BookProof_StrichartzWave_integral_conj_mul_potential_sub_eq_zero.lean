-- Prove2me | solution 1 for BookProof.StrichartzWave.integral_conj_mul_potential_sub_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T07:03:10.586069+00:00
-- url     : https://prove2.me/submissions/4c61590b-cf20-4b7e-a523-a581a3730f55

-- Generated from ChapterWaveUnboundedPotential.lean — solution of BookProof.StrichartzWave.integral_conj_mul_potential_sub_eq_zero
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Theorems.Thm_BookProof_StrichartzWave_inner_toLp_left
import Theorems.Thm_BookProof_StrichartzWave_integrable_conj_schwartz_mul
import Theorems.Thm_BookProof_StrichartzWave_opL2_apply
import Theorems.Thm_BookProof_StrichartzWave_schwartzEquiv_coe
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! `potentialOp_apply` exists in the source chapter but no `Theorems/Thm_…`
stub was generated for it, so a solution may not import it.  It is a one-line
unfolding lemma over declarations the platform DOES serve (`potentialOp` in the
published bundle, `SchwartzMap.smulLeftCLM_apply_apply` from Mathlib), so it is
stated locally as `private` and the file stays standalone.
-/

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem hasTemperateGrowth_ofReal' {W : V → ℝ}
    (hW : Function.HasTemperateGrowth W) :
    Function.HasTemperateGrowth (fun x => (W x : ℂ)) := by
  exact Function.HasTemperateGrowth.comp Complex.ofRealCLM.hasTemperateGrowth hW

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
private theorem potentialOp_apply' {W : V → ℝ} (hW : Function.HasTemperateGrowth W)
    (f : 𝓢(V, ℂ)) (x : V) : potentialOp W f x = (W x : ℂ) * f x := by
  simp [potentialOp, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_ofReal' hW)]

set_option maxHeartbeats 1000000 in
theorem solution (W : V → ℝ) (hW : Function.HasTemperateGrowth W)
    (z : ℂ) (u : Lp ℂ 2 (volume : Measure V))
    (hu : ∀ v : schwartzDomain V,
      (inner ℂ (opL2 (potentialOp W) v) u : ℂ) = z * inner ℂ (v : Lp ℂ 2 _) u)
    (ψ : 𝓢(V, ℂ)) :
    ∫ x, (starRingEnd ℂ) (ψ x) * (((W x : ℝ) : ℂ) - z) * (u x) = 0 := by

  have h1 := hu (schwartzEquiv V ψ)
  rw [opL2_apply, schwartzEquiv_coe, inner_toLp_left, inner_toLp_left] at h1
  have hL : ∫ x, (starRingEnd ℂ) ((potentialOp W ψ) x) * (u x)
      = ∫ x, ((W x : ℝ) : ℂ) * ((starRingEnd ℂ) (ψ x) * (u x)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [potentialOp_apply' hW, map_mul, Complex.conj_ofReal]
    ring
  rw [hL] at h1
  have hint1 : Integrable (fun x => (starRingEnd ℂ) (ψ x) * (u x)) (volume : Measure V) :=
    integrable_conj_schwartz_mul ψ u
  have hint2 : Integrable (fun x => ((W x : ℝ) : ℂ) * ((starRingEnd ℂ) (ψ x) * (u x)))
      (volume : Measure V) := by
    have := integrable_conj_schwartz_mul (potentialOp W ψ) u
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [potentialOp_apply' hW, map_mul, Complex.conj_ofReal]
    ring
  have hcomb : ∫ x, (((W x : ℝ) : ℂ) * ((starRingEnd ℂ) (ψ x) * (u x))
      - z * ((starRingEnd ℂ) (ψ x) * (u x))) = 0 := by
    rw [integral_sub hint2 (hint1.const_mul z), MeasureTheory.integral_const_mul, h1]
    ring
  rw [← hcomb]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring
