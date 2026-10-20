-- Prove2me | solution 1 for BookProof.NsSpatialMultiplier.fourier_opL2_firstOrderOp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:13:12.328437+00:00
-- url     : https://prove2.me/submissions/a6665809-7c0d-4ce3-918c-a3a3e0c868c0

-- Generated from ChapterNsSpatialMomentumMultiplier.lean — theorem BookProof.NsSpatialMultiplier.fourier_opL2_firstOrderOp
import Mathlib
import Theorems.Thm_BookProof_NsSpatialMultiplier_hasTemperateGrowth_foSymbol
import Theorems.Thm_BookProof_FourierMultiplierEsa_fourier_firstOrderOp_apply
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
theorem solution (c : ι → ℝ) (w : ι → V) (f : 𝓢(V, ℂ)) :
    l2Fourier V (opL2 (firstOrderOp c w) (schwartzEquiv V f))
      = (mulSymbolOp (foSymbolFn c w) (𝓕 f)).toLp 2 (volume : Measure V) := by 
  exact ns_fourier_mul _ _ (fun g x => BookProof.FourierMultiplierEsa.fourier_firstOrderOp_apply c w g x)
    (BookProof.NsSpatialMultiplier.hasTemperateGrowth_foSymbol V c w) f
