-- Prove2me | solution 1 for BookProof.ChapterPaleyWienerSampling.bandSignal_congr_ae
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-20T16:41:16.305589+00:00
-- url     : https://prove2.me/submissions/dd65b73e-e3cb-40dd-a3d3-adbc95773d0b

-- Generated from ChapterPaleyWienerSampling.lean — solution of BookProof.ChapterPaleyWienerSampling.bandSignal_congr_ae
import Mathlib
import Definitions.Def_ChapterPaleyWienerSampling
import Theorems.Thm_BookProof_ChapterShannonSampling_half_add_period
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterPaleyWienerSampling




open MeasureTheory Complex AddCircle Set
open scoped Real FourierTransform
open BookProof.ChapterShannonSampling (sinc bandSignal exists_rep half_add_period)
open BookProof.ChapterShannonSampling

variable {T : ℝ} {f g : ℝ → ℂ}
variable {T : ℝ} [hT : Fact (0 < T)] {f g : ℝ → ℂ}

set_option maxHeartbeats 1000000 in
theorem solution {F G : AddCircle T → ℂ} (h : F =ᵐ[haarAddCircle (T := T)] G)
    (x : ℝ) : bandSignal (T := T) F x = bandSignal (T := T) G x := by

  have hT0 : (0 : ℝ) < T := hT.out
  have hvol : F =ᵐ[(volume : Measure (AddCircle T))] G := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.ae_smul_measure h _
  have hpull : (fun ξ : ℝ => F ξ)
      =ᵐ[(volume : Measure ℝ).restrict (Ioc (-(T / 2)) (-(T / 2) + T))] fun ξ : ℝ => G ξ :=
    (AddCircle.measurePreserving_mk T (-(T / 2))).quasiMeasurePreserving.ae_eq_comp hvol
  rw [half_add_period (T := T)] at hpull
  have hle : -(T / 2) ≤ T / 2 := by linarith
  rw [bandSignal, bandSignal, intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_of_le hle]
  refine setIntegral_congr_ae measurableSet_Ioc ((ae_restrict_iff' measurableSet_Ioc).mp ?_)
  filter_upwards [hpull] with ξ hξ
  rw [hξ]
