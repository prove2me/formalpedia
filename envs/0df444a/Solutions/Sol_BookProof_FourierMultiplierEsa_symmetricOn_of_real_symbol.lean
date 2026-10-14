-- Prove2me | solution 1 for BookProof.FourierMultiplierEsa.symmetricOn_of_real_symbol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T14:07:52.128058+00:00
-- url     : https://prove2.me/submissions/a8061ae1-5b08-45b8-a802-2f53b737e7c9

-- Generated from ChapterFourierMultiplierEsa.lean — solution of BookProof.FourierMultiplierEsa.symmetricOn_of_real_symbol
import Mathlib
import Definitions.Def_ChapterFourierMultiplierEsa
import Theorems.Thm_BookProof_StrichartzWave_inner_toLp_eq_integral_fourier
import Theorems.Thm_BookProof_StrichartzWave_opL2_apply
import Theorems.Thm_BookProof_StrichartzWave_schwartzEquiv_coe
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.FourierMultiplierEsa




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

set_option maxHeartbeats 1000000 in
theorem solution (P : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ)) (σ : V → ℝ)
    (hP : ∀ (f : 𝓢(V, ℂ)) (x : V),
      (𝓕 (P f) : 𝓢(V, ℂ)) x = ((σ x : ℝ) : ℂ) * (𝓕 f : 𝓢(V, ℂ)) x) :
    BookProof.FarisLavine.SymmetricOn (schwartzDomain V) (opL2 P) := by

  intro x y
  obtain ⟨f, rfl⟩ := (schwartzEquiv V).surjective x
  obtain ⟨g, rfl⟩ := (schwartzEquiv V).surjective y
  rw [opL2_apply, opL2_apply, schwartzEquiv_coe, schwartzEquiv_coe,
    inner_toLp_eq_integral_fourier, inner_toLp_eq_integral_fourier]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hP, map_mul, Complex.conj_ofReal]
  ring
