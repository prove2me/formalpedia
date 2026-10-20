-- Prove2me | solution 1 for BookProof.StrichartzWave.opL2_potentialOp_eq_mulL2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:32:43.234395+00:00
-- url     : https://prove2.me/submissions/a68f04c0-ed2b-48c9-8199-eb4f4205d936

-- Generated from ChapterWaveUnboundedPotential.lean — theorem BookProof.StrichartzWave.opL2_potentialOp_eq_mulL2
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterWaveBoundedPotential
open BookProof.StrichartzWave



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

theorem sw_pot_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (W : V → ℝ) (hW : Function.HasTemperateGrowth W)
    (hmem : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure V)) (f : 𝓢(V, ℂ)) :
    opL2 (potentialOp W) (schwartzEquiv V f)
      = mulL2 (hmem.toLp _) (f.toLp 2 (volume : Measure V)) := by
  have hW' : Function.HasTemperateGrowth (fun x : V => ((W x : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.hasTemperateGrowth).comp hW
  have h1 : opL2 (potentialOp W) (schwartzEquiv V f) = (potentialOp W f).toLp 2 (volume : Measure V) := by
    simp [opL2]
  rw [h1]
  apply Lp.ext
  have e1 := SchwartzMap.coeFn_toLp (potentialOp W f) 2 (volume : Measure V)
  have e2 := ContinuousLinearMap.coeFn_holder (B := ContinuousLinearMap.mul ℂ ℂ) (r := (2 : ℝ≥0∞))
    (hmem.toLp _) (f.toLp 2 (volume : Measure V))
  have e3 := hmem.coeFn_toLp
  have e4 := SchwartzMap.coeFn_toLp f 2 (volume : Measure V)
  filter_upwards [e1, e2, e3, e4] with x h1 h2 h3 h4
  simp only [mulL2, ContinuousLinearMap.holderL, ContinuousLinearMap.holderₗ] at *
  rw [h1]
  erw [h2]
  rw [h3, h4, potentialOp, SchwartzMap.smulLeftCLM_apply_apply hW', smul_eq_mul]
  rfl

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {ι : Type*} [Fintype ι]
open BookProof.StrichartzWave in
theorem solution (W : V → ℝ) (hW : Function.HasTemperateGrowth W)
    (hmem : MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure V)) :
    opL2 (potentialOp W)
      = (mulL2 (hmem.toLp _)).toLinearMap ∘ₗ (schwartzDomain V).subtype := by 
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := (schwartzEquiv V).surjective x
  rw [sw_pot_apply W hW hmem f]
  rfl
