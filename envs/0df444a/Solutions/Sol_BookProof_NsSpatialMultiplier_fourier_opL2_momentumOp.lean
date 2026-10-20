-- Prove2me | solution 1 for BookProof.NsSpatialMultiplier.fourier_opL2_momentumOp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:13:22.90158+00:00
-- url     : https://prove2.me/submissions/2aec333a-608e-4c59-9836-6170d8e19e9a

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — theorem BookProof.NsSpatialMultiplier.fourier_opL2_momentumOp
import Mathlib
import Theorems.Thm_BookProof_NsSpatialMultiplier_hasTemperateGrowth_foSymbol
import Theorems.Thm_BookProof_FourierMultiplierEsa_fourier_momentumOp_apply
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterStrichartzWave
open BookProof.FarisLavine
open BookProof.FourierMultiplierEsa
open BookProof.StrichartzWave
open BookProof.NsSpatialMultiplier



open MeasureTheory SchwartzMap FourierTransform
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa

noncomputable section

theorem ns_fourier_mul {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) (σ : V → ℝ)
    (hP : ∀ (f : 𝓢(V, ℂ)) (x : V),
      (𝓕 (P f) : 𝓢(V, ℂ)) x = ((σ x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x)
    (hσ : Function.HasTemperateGrowth (fun x : V => ((σ x : ℝ) : ℂ)))
    (f : 𝓢(V, ℂ)) :
    l2Fourier V (opL2 P (schwartzEquiv V f))
      = (mulSymbolOp σ (𝓕 f)).toLp 2 (volume : Measure V) := by
  have h1 : opL2 P (schwartzEquiv V f) = (P f).toLp 2 (volume : Measure V) := by
    simp [opL2]
  rw [h1]
  have h2 : l2Fourier V ((P f).toLp 2 (volume : Measure V)) = (𝓕 (P f)).toLp 2 (volume : Measure V) :=
    SchwartzMap.toLp_fourier_eq (P f)
  rw [h2]
  congr 1
  ext x
  rw [hP f x, BookProof.NsSpatialMultiplier.mulSymbolOp, SchwartzMap.smulLeftCLM_apply_apply hσ, smul_eq_mul]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

variable (V) in
theorem solution (m : V) (f : 𝓢(V, ℂ)) :
    l2Fourier V (opL2 (momentumOp m) (schwartzEquiv V f))
      = (mulSymbolOp (fun x => 2 * Real.pi * (inner ℝ x m : ℝ)) (𝓕 f)).toLp
          2 (volume : Measure V) := by 
  have hσ : Function.HasTemperateGrowth (fun x : V => (((2 * Real.pi * (inner ℝ x m : ℝ)) : ℝ) : ℂ)) := by
    have h := BookProof.NsSpatialMultiplier.hasTemperateGrowth_foSymbol V (fun _ : Unit => (1:ℝ)) (fun _ => m)
    convert h using 2 with x
    simp [foSymbolFn]
  exact ns_fourier_mul _ _ (fun g x => BookProof.FourierMultiplierEsa.fourier_momentumOp_apply g m x) hσ f
