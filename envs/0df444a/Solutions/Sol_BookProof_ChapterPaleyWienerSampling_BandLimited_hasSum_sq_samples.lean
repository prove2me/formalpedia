-- Prove2me | solution 1 for BookProof.ChapterPaleyWienerSampling.BandLimited.hasSum_sq_samples
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-20T17:04:47.460153+00:00
-- url     : https://prove2.me/submissions/efc5cfe0-f640-4520-aa00-cac1ad64e49d

-- Generated from ChapterPaleyWienerSampling.lean — solution of BookProof.ChapterPaleyWienerSampling.BandLimited.hasSum_sq_samples
import Mathlib
import Definitions.Def_ChapterPaleyWienerSampling
import Theorems.Thm_BookProof_ChapterPaleyWienerSampling_BandLimited_eq_bandSignal_lp
import Theorems.Thm_BookProof_ChapterShannonSampling_half_add_period
import Theorems.Thm_BookProof_ChapterShannonSampling_hasSum_sq_samples
import Definitions.Def_ChapterShannonSampling
open BookProof.ChapterPaleyWienerSampling
open BookProof.ChapterPaleyWienerSampling.BandLimited




open MeasureTheory Complex AddCircle Set
open scoped Real FourierTransform
open BookProof.ChapterShannonSampling (sinc bandSignal exists_rep half_add_period)
open BookProof.ChapterShannonSampling

variable {T : ℝ} {f g : ℝ → ℂ}
variable {T : ℝ} [hT : Fact (0 < T)] {f g : ℝ → ℂ}

set_option maxHeartbeats 1000000 in
theorem solution (hf : BandLimited T f) :
    HasSum (fun n : ℤ => ‖f ((n : ℝ) / T)‖ ^ 2) (T * ∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2) := by

  have hT0 : (0 : ℝ) < T := hT.out
  have hbase := hasSum_sq_samples (bandSpectrumLp hf)
  have hcoe : ∀ n : ℤ,
      ‖bandSignal (T := T) ((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) :
        AddCircle T → ℂ) ((n : ℝ) / T)‖ ^ 2 = ‖f ((n : ℝ) / T)‖ ^ 2 := by
    intro n
    rw [← hf.eq_bandSignal_lp]
  simp_rw [hcoe] at hbase
  -- identify the energy of the spectrum on the circle with the energy of `𝓕 f` on the line
  have hband : (∫ ξ in (-(T / 2))..(-(T / 2) + T),
        ‖((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) : AddCircle T → ℂ) ξ‖ ^ 2)
      = ∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2 := by
    have hae : (fun ξ : ℝ =>
          ‖((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) : AddCircle T → ℂ) ξ‖ ^ 2)
        =ᵐ[(volume : Measure ℝ).restrict (Ioc (-(T / 2)) (-(T / 2) + T))]
          fun ξ : ℝ => ‖𝓕 f ξ‖ ^ 2 := by
      have hvol : ((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) : AddCircle T → ℂ)
          =ᵐ[(volume : Measure (AddCircle T))] bandSpectrum T f := by
        rw [AddCircle.volume_eq_smul_haarAddCircle]
        exact Measure.ae_smul_measure (memLp_bandSpectrum hf).coeFn_toLp _
      have hpull := (AddCircle.measurePreserving_mk T
        (-(T / 2))).quasiMeasurePreserving.ae_eq_comp hvol
      filter_upwards [hpull, ae_restrict_mem measurableSet_Ioc] with ξ hξ hmem
      rw [show ((bandSpectrumLp hf : Lp ℂ 2 (haarAddCircle (T := T))) : AddCircle T → ℂ)
        (ξ : AddCircle T) = bandSpectrum T f (ξ : AddCircle T) from hξ,
        bandSpectrum_coe_apply hmem]
    have hzero : ∀ ξ : ℝ, ξ ∉ Icc (-(T / 2)) (T / 2) → ‖𝓕 f ξ‖ ^ 2 = 0 := by
      intro ξ hξ
      have : T / 2 < |ξ| := by
        rcases lt_or_ge (T / 2) |ξ| with hlt | hge
        · exact hlt
        · exact absurd (abs_le.mp hge) (by simpa [Set.mem_Icc] using hξ)
      simp [hf.spectrum_support ξ this]
    rw [half_add_period (T := T)] at hae ⊢
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_congr_ae measurableSet_Ioc ((ae_restrict_iff' measurableSet_Ioc).mp hae),
      ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  rw [hband] at hbase
  exact hbase
