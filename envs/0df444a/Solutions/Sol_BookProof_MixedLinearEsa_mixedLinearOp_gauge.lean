-- Prove2me | solution 1 for BookProof.MixedLinearEsa.mixedLinearOp_gauge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:05:34.697989+00:00
-- url     : https://prove2.me/submissions/4e77c293-a2ab-45e2-89b0-6747c05e4255
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterMixedLinearEsa.lean — solution of BookProof.MixedLinearEsa.mixedLinearOp_gauge
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Theorems.Thm_BookProof_MixedLinearEsa_momentumOp_apply
import Theorems.Thm_BookProof_MixedLinearEsa_mixedLinearOp_apply
import Theorems.Thm_BookProof_MixedLinearEsa_hasDerivAt_gaugeFun_line
import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFourierMultiplierEsa
open BookProof.MixedLinearEsa




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine
open BookProof.FourierMultiplierEsa

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]


@[simp] private theorem gaugeSchwartz_apply (b m : V) (φ : 𝓢(V, ℂ))
    (hφ : HasCompactSupport (φ : V → ℂ)) (x : V) :
    gaugeSchwartz b m φ hφ x = gaugeFun b m x * φ x := rfl

set_option maxHeartbeats 1000000 in
theorem solution (b m : V) (hm : m ≠ 0) (φ : 𝓢(V, ℂ))
    (hφ : HasCompactSupport (φ : V → ℂ)) (x : V) :
    (mixedLinearOp b m (gaugeSchwartz b m φ hφ)) x
      = gaugeFun b m x * (momentumOp m φ x) := by

  have hφd : HasDerivAt (fun t : ℝ => φ (x + t • m)) (fderiv ℝ (φ : V → ℂ) x m) 0 :=
    (φ.differentiableAt).hasFDerivAt.hasLineDerivAt m
  have hνd := hasDerivAt_gaugeFun_line b m hm x
  have hprod : HasDerivAt (fun t : ℝ => gaugeFun b m (x + t • m) * φ (x + t • m))
      ((gaugeFun b m x * (Complex.I * ((-(inner ℝ x b : ℝ) : ℝ) : ℂ))) * φ x
        + gaugeFun b m x * fderiv ℝ (φ : V → ℂ) x m) 0 := by
    have h := hνd.mul hφd
    simp only [zero_smul, add_zero] at h
    exact h
  have hgd : HasDerivAt (fun t : ℝ => (gaugeSchwartz b m φ hφ) (x + t • m))
      (fderiv ℝ ((gaugeSchwartz b m φ hφ) : V → ℂ) x m) 0 :=
    ((gaugeSchwartz b m φ hφ).differentiableAt).hasFDerivAt.hasLineDerivAt m
  have hval := hgd.unique hprod
  rw [mixedLinearOp_apply, hval, momentumOp_apply, gaugeSchwartz_apply]
  push_cast
  linear_combination ((inner ℝ x b : ℝ) : ℂ) * gaugeFun b m x * φ x * Complex.I_mul_I
