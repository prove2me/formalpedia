-- Prove2me | solution 1 for BookProof.ChapterPaleyWienerSampling.BandLimited.eq_bandSignal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-20T16:41:19.017563+00:00
-- url     : https://prove2.me/submissions/d158e534-07c7-4d09-a742-3b30dacf27f5

-- Generated from ChapterPaleyWienerSampling.lean — solution of BookProof.ChapterPaleyWienerSampling.BandLimited.eq_bandSignal
import Mathlib
import Definitions.Def_ChapterPaleyWienerSampling
import Theorems.Thm_BookProof_ChapterPaleyWienerSampling_BandLimited_integrable_fourier
import Theorems.Thm_BookProof_ChapterShannonSampling_half_add_period
import Theorems.Thm_BookProof_WeakSecondDeriv_IsTestFun_integrable
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
theorem solution (hf : BandLimited T f) (x : ℝ) :
    f x = bandSignal (T := T) (bandSpectrum T f) x := by

  have hT0 : (0 : ℝ) < T := hT.out
  have hinv : 𝓕⁻ (𝓕 f) = f :=
    hf.continuous.fourierInv_fourier_eq hf.integrable hf.integrable_fourier
  have hline : f x = ∫ ξ : ℝ, Complex.exp (2 * π * I * x * ξ) * 𝓕 f ξ := by
    conv_lhs => rw [← hinv]
    rw [Real.fourierInv_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
    congr 2
    push_cast
    ring
  have hzero : ∀ ξ : ℝ, ξ ∉ Icc (-(T / 2)) (T / 2) →
      Complex.exp (2 * π * I * x * ξ) * 𝓕 f ξ = 0 := by
    intro ξ hξ
    have hout : T / 2 < |ξ| := by
      rcases lt_or_ge (T / 2) |ξ| with hlt | hge
      · exact hlt
      · exact absurd (abs_le.mp hge) (by simpa [Set.mem_Icc] using hξ)
    simp [hf.spectrum_support ξ hout]
  have hband : (∫ ξ : ℝ, Complex.exp (2 * π * I * x * ξ) * 𝓕 f ξ)
      = ∫ ξ in (-(T / 2))..(T / 2), Complex.exp (2 * π * I * x * ξ) * 𝓕 f ξ := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hsig : (∫ ξ in (-(T / 2))..(T / 2), Complex.exp (2 * π * I * x * ξ) * 𝓕 f ξ)
      = bandSignal (T := T) (bandSpectrum T f) x := by
    rw [bandSignal]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun ξ hξ => ?_)
    have hξ' : ξ ∈ Ioc (-(T / 2)) (-(T / 2) + T) := by
      rw [Set.uIoc_of_le (by linarith)] at hξ
      exact ⟨hξ.1, by rw [half_add_period]; exact hξ.2⟩
    rw [bandSpectrum_coe_apply hξ']
  rw [hline, hband, hsig]
