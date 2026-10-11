-- Prove2me | solution 1 for ConnesGreen.canonical_quartet_escape_negative_ray_tests
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T16:49:55.46698+00:00
-- url     : https://prove2.me/submissions/0f917cdf-cf73-4700-b799-86e3fa64f850

import Theorems.Thm_ConnesGreen_canonical_quartet_escape_absolute_tail_background_tests
import Definitions.Def_ConnesGreen_original_quartet
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
import Definitions.Def_WeilMarker_regularized_cost
import Definitions.Def_ConnesGreen_small_support_constants
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesRZQuartet ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma ConnesGreen.negative_ray_term_bound (z : ℂ) (η : ℝ) (hη : 0 < η) :
    ‖z + (‖z‖ : ℂ)‖ ≤ η * ‖z‖ + (‖z‖ + z.re) / η := by
  have hd : 0 ≤ ‖z‖ + z.re := by
    have h := (neg_le_abs z.re).trans (Complex.abs_re_le_norm z)
    linarith
  have hs : ‖z + (‖z‖ : ℂ)‖ ^ 2 = 2 * ‖z‖ * (‖z‖ + z.re) := by
    have hz := Complex.sq_norm z
    simp only [Complex.normSq_apply] at hz
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, add_zero]
    nlinarith
  have hn := norm_nonneg z
  have hdiv : 0 ≤ (‖z‖ + z.re) / η := div_nonneg hd hη.le
  have hid : η * ((‖z‖ + z.re) / η) = ‖z‖ + z.re := by
    field_simp
  have hcross : (η * ‖z‖) * ((‖z‖ + z.re) / η) = ‖z‖ * (‖z‖ + z.re) := by
    calc
      _ = ‖z‖ * (η * ((‖z‖ + z.re) / η)) := by ring
      _ = _ := by rw [hid]
  have hright : 0 ≤ η * ‖z‖ + (‖z‖ + z.re) / η := by positivity
  nlinarith [sq_nonneg (η * ‖z‖), sq_nonneg ((‖z‖ + z.re) / η), norm_nonneg (z + (‖z‖ : ℂ))]

lemma ConnesGreen.negative_ray_series_bound {ι : Type*} (f : ι → ℂ)
    (hf : Summable (fun i => ‖f i‖)) (η : ℝ) (hη : 0 < η) :
    Summable (fun i => ‖f i + (‖f i‖ : ℂ)‖) ∧
      (∑' i, ‖f i + (‖f i‖ : ℂ)‖) ≤
        η * (∑' i, ‖f i‖) + ((∑' i, ‖f i‖) + (∑' i, f i).re) / η := by
  have hc : Summable f := hf.of_norm
  have hr : Summable (fun i => (f i).re) := Complex.reCLM.summable hc
  have hb := (hf.mul_left η).add ((hf.add hr).div_const η)
  have hs := Summable.of_nonneg_of_le (fun i => norm_nonneg _)
    (fun i => negative_ray_term_bound (f i) η hη) hb
  refine ⟨hs, ?_⟩
  have hle := hs.tsum_le_tsum (fun i => negative_ray_term_bound (f i) η hη) hb
  rw [Summable.tsum_add (hf.mul_left η) ((hf.add hr).div_const η),
    tsum_mul_left, tsum_div_const, hf.tsum_add hr] at hle
  have hre : (∑' i, (f i).re) = (∑' i, f i).re := (Complex.reCLM.map_tsum hc).symm
  rwa [hre] at hle

lemma ConnesGreen.negative_ray_compensated_norm {ι : Type*} (f : ι → ℂ)
    (hf : Summable (fun i => ‖f i‖)) (b : ℝ) :
    ‖(∑' i, f i) + (b : ℂ)‖ ≤
      (∑' i, ‖f i + (‖f i‖ : ℂ)‖) + |(∑' i, ‖f i‖) - b| := by
  have hc : Summable f := hf.of_norm
  have hn : Summable (fun i => (‖f i‖ : ℂ)) := Complex.ofRealCLM.summable hf
  have hnid : (∑' i, (‖f i‖ : ℂ)) = (↑(∑' i, ‖f i‖ : ℝ) : ℂ) :=
    (Complex.ofReal_tsum (fun i => ‖f i‖)).symm
  have hs := (negative_ray_series_bound f hf 1 (by norm_num)).1
  have hid : (∑' i, f i) + (b : ℂ) =
      (∑' i, (f i + (‖f i‖ : ℂ))) + ((b - (∑' i, ‖f i‖) : ℝ) : ℂ) := by
    rw [hc.tsum_add hn, hnid]
    push_cast
    ring
  rw [hid]
  calc
    _ ≤ ‖∑' i, (f i + (‖f i‖ : ℂ))‖ + ‖((b - (∑' i, ‖f i‖) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact add_le_add (norm_tsum_le_tsum_norm hs) le_rfl

lemma ConnesGreen.negative_ray_imaginary_bound {ι : Type*} (f : ι → ℂ)
    (hf : Summable (fun i => ‖f i‖)) :
    Summable (fun i => |(f i).im|) ∧
      (∑' i, |(f i).im|) ≤ (∑' i, ‖f i + (‖f i‖ : ℂ)‖) := by
  have hs := (negative_ray_series_bound f hf 1 (by norm_num)).1
  have hb : ∀ i, |(f i).im| ≤ ‖f i + (‖f i‖ : ℂ)‖ := by
    intro i
    simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using
      Complex.abs_im_le_norm (f i + (‖f i‖ : ℂ))
  have hi := Summable.of_nonneg_of_le (fun i => abs_nonneg _) hb hs
  exact ⟨hi, hi.tsum_le_tsum hb hs⟩

theorem solution
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, ∃ hc : 0 < c, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c)) ∧
((¬ (1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
        ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤ canonicalSupportRightMarker c hc.le (quartet ρ)) → ¬ (∃ ε : ℝ, 0 < ε ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + 1 →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          ‖sourceEmbed T (problemOneL g)‖ ^ 2 = 1 ∧
          (weilDistribution (conv g (starInv g))).re +
            ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
              (sourceEmbed T (problemOneL g))‖ ^ 2 < -ε) →
        ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
          ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T → T < c + r →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          (∑ τ ∈ quartet ρ, (zeroMult τ.1 : ℝ) * ‖mellinHat g τ.1‖ ^ 2) < ε ∧
          (∑ τ ∈ quartet ρ, ‖(zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < ε ∧
          |(∑ τ ∈ quartet ρ, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re| < ε ∧
          HasSum (fun τ : CriticalZeros => if τ ∈ quartet ρ then 0 else
            (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1)
            (weilDistribution (conv g (starInv g)) -
              ∑ τ ∈ quartet ρ, (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1) ∧
          Summable (fun τ : CriticalZeros => ‖if τ ∈ quartet ρ then 0 else
            (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
          |(∑' τ : CriticalZeros, if τ ∈ quartet ρ then 0 else
            (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).re +
            ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint
              (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2| < ε ∧
          |(∑' τ : CriticalZeros, ‖if τ ∈ quartet ρ then 0 else
            (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) -
            ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint
              (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2| < ε ∧
          Summable (fun τ : CriticalZeros => ‖(if τ ∈ quartet ρ then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1) + (‖(if τ ∈ quartet ρ then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1)‖ : ℂ)‖) ∧
          (∑' τ : CriticalZeros, ‖(if τ ∈ quartet ρ then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1) + (‖(if τ ∈ quartet ρ then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1)‖ : ℂ)‖) < ε ∧
          Summable (fun τ : CriticalZeros => |(if τ ∈ quartet ρ then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).im|) ∧
          (∑' τ : CriticalZeros, |(if τ ∈ quartet ρ then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1).im|) < ε ∧
          ‖(∑' τ : CriticalZeros, (if τ ∈ quartet ρ then 0 else (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1)) + (‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 : ℂ)‖ < ε ∧
          ‖sourceEmbed (c + 1) (problemOneL g)‖ ^ 2 = 1 ∧
          (0 < ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          (0 ≤ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧ ‖(canonicalPositiveSynthesis (c + 1) (by linarith)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < ε) ∧
          -ε < (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 ∧
          (weilDistribution (conv g (starInv g))).re + ‖(canonicalBackgroundSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2 < -δ * (‖(canonicalSelectedSynthesis (c + 1) (by linarith) (quartet ρ)).adjoint (sourceEmbed (c + 1) (problemOneL g))‖ ^ 2)) := by
  classical
  obtain ⟨c, hc, hrc, hcut, he⟩ := canonical_quartet_escape_absolute_tail_background_tests ρ hoff
  refine ⟨c, hc, hrc, hcut, ?_⟩
  intro hfailure hno
  obtain ⟨δ, hδ, hδ1, hnear⟩ := he hfailure hno
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro ε hε
  have hc1 : 0 < c + 1 := by linarith
  let B := (canonicalBackgroundSynthesis (c + 1) hc1 (quartet ρ)).adjoint
  let K : ℝ := ‖B‖ ^ 2
  have hK : 0 ≤ K := sq_nonneg _
  let η : ℝ := ε / (4 * (K + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηid : η * (K + 1) = ε / 4 := by dsimp [η]; field_simp
  let β : ℝ := min 1 (min (ε / 2) (η * ε / 8))
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ1 : β ≤ 1 := min_le_left _ _
  have hβe : β ≤ ε / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hβd : β ≤ η * ε / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hβε : β < ε := by linarith only [hβe, hε]
  obtain ⟨r, hr, hr1, hb⟩ := hnear β hβ
  refine ⟨r, hr, hr1, ?_⟩
  intro T hT hcT hTr
  obtain ⟨g, hg, hpacket, habs, hsigned, htail, hsum, hcomp, hN, hu,
    ⟨ha0, ha⟩, ⟨hp0, hp⟩, hw0, hw⟩ := hb T hT hcT hTr
  let f : CriticalZeros → ℂ := fun τ => if τ ∈ quartet ρ then 0 else
    (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1
  let x := sourceEmbed (c + 1) (problemOneL g)
  let b : ℝ := ‖B x‖ ^ 2
  let N : ℝ := ∑' τ, ‖f τ‖
  let L : ℝ := (∑' τ, f τ).re
  have hx : ‖x‖ = 1 := by change ‖x‖ ^ 2 = 1 at hu; nlinarith [norm_nonneg x]
  have hbK : b ≤ K := by
    have h := B.le_opNorm x
    rw [hx, mul_one] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hNb : |N - b| < β := hN
  have hLb : |L + b| < β := hcomp
  have hNupper : N < K + 1 := by
    have h := (abs_lt.mp hNb).2
    linarith only [h, hbK, hβ1]
  have hD : N + L < 2 * β := by
    have hn := (abs_lt.mp hNb).2
    have hl := (abs_lt.mp hLb).2
    linarith only [hn, hl]
  have hsmall1 : η * N < ε / 4 := by
    have h := mul_lt_mul_of_pos_left hNupper hη
    rwa [hηid] at h
  have hsmall2 : (N + L) / η < ε / 4 := by
    apply (div_lt_iff₀ hη).mpr
    nlinarith only [hD, hβd]
  obtain ⟨hphaseSum, hphaseBound⟩ := negative_ray_series_bound f hsum η hη
  have hphase : (∑' τ, ‖f τ + (‖f τ‖ : ℂ)‖) < ε / 2 := by
    change _ ≤ η * N + (N + L) / η at hphaseBound
    linarith only [hphaseBound, hsmall1, hsmall2]
  have hcomplex : ‖(∑' τ, f τ) + (b : ℂ)‖ < ε := by
    have h := negative_ray_compensated_norm f hsum b
    change _ ≤ (∑' τ, ‖f τ + (‖f τ‖ : ℂ)‖) + |N - b| at h
    linarith only [h, hphase, hNb, hβe]
  obtain ⟨himSum, himBound⟩ := negative_ray_imaginary_bound f hsum
  have him : (∑' τ, |(f τ).im|) < ε := by
    linarith only [himBound, hphase, hε]
  refine ⟨g, hg, hpacket.trans hβε, habs.trans hβε, hsigned.trans hβε,
    htail, hsum, hcomp.trans hβε, hN.trans hβε, hphaseSum,
    (by linarith only [hphase, hε]), himSum, him, (by simpa only [b, B, x, Complex.ofReal_pow] using hcomplex),
    hu, ⟨ha0, ha.trans hβε⟩, ⟨hp0, hp.trans hβε⟩, ?_, hw⟩
  linarith only [hw0, hβε]
