-- Prove2me | solution 1 for ConnesRZ.mellinHat_conv_starInv
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-06T20:33:21.927585+00:00
-- url     : https://prove2.me/submissions/cb03acbc-c391-47e0-8103-4180c1520754

import Definitions.Def_ConnesRZ_weil_defs

open Complex MeasureTheory ConnesRZ

namespace ConnesRZFullStar

lemma integrable_pair (g : ℝ → ℂ) (hg : IsTest g) (z : ℂ) :
    Integrable (fun p : ℝ × ℝ =>
      g p.2 * (starRingEnd ℂ) (g (p.2 - p.1)) * Complex.exp ((z - 1 / 2) * p.1)) := by
  have hcont : Continuous (fun p : ℝ × ℝ =>
      g p.2 * (starRingEnd ℂ) (g (p.2 - p.1)) * Complex.exp ((z - 1 / 2) * p.1)) := by
    exact ((hg.1.continuous.comp continuous_snd).mul
      (Complex.continuous_conj.comp (hg.1.continuous.comp
        (continuous_snd.sub continuous_fst)))).mul
      (Complex.continuous_exp.comp (by fun_prop))
  have hsupp : HasCompactSupport (fun p : ℝ × ℝ =>
      g p.2 * (starRingEnd ℂ) (g (p.2 - p.1)) * Complex.exp ((z - 1 / 2) * p.1)) := by
    classical
    refine HasCompactSupport.intro
      (K := (fun q : ℝ × ℝ => (q.2 - q.1, q.2)) '' (tsupport g ×ˢ tsupport g))
      ((hg.2.prod hg.2).image (by fun_prop)) ?_
    rintro ⟨t, s⟩ hts
    by_contra hne
    have h1 : g s ≠ 0 := by
      intro h; apply hne; simp [h]
    have h2 : g (s - t) ≠ 0 := by
      intro h; apply hne; simp [h]
    exact hts ⟨(s - t, s), ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩, by simp⟩
  exact hcont.integrable_of_hasCompactSupport hsupp

lemma integral_conj_exp (g : ℝ → ℂ) (z : ℂ) :
    (∫ u : ℝ, (starRingEnd ℂ) (g u) * Complex.exp (-((z - 1 / 2) * u))) =
      (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) z)) := by
  unfold mellinHat
  rw [← integral_conj]
  apply integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_sub, map_one, map_div₀, map_ofNat, Complex.conj_conj,
    Complex.conj_ofReal]
  ring

end ConnesRZFullStar

open ConnesRZFullStar in
/-- The Mellin star-square identity at every complex spectral parameter. -/
theorem solution (g : ℝ → ℂ) (hg : IsTest g) (z : ℂ) :
    mellinHat (conv g (starInv g)) z =
      mellinHat g z * (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) z)) := by
  unfold mellinHat
  have step1 : ∀ t : ℝ, conv g (starInv g) t * Complex.exp ((z - 1 / 2) * t) =
      ∫ s : ℝ, g s * (starRingEnd ℂ) (g (s - t)) * Complex.exp ((z - 1 / 2) * t) := by
    intro t
    show (∫ s : ℝ, g s * starInv g (t - s)) * Complex.exp ((z - 1 / 2) * t) = _
    rw [← integral_mul_const]
    apply integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp [starInv, neg_sub]
  rw [integral_congr_ae (Filter.Eventually.of_forall step1)]
  rw [integral_integral_swap (integrable_pair g hg z)]
  have step2 : ∀ s : ℝ,
      (∫ t : ℝ, g s * (starRingEnd ℂ) (g (s - t)) * Complex.exp ((z - 1 / 2) * t)) =
        (g s * Complex.exp ((z - 1 / 2) * s)) *
          ∫ u : ℝ, (starRingEnd ℂ) (g u) * Complex.exp (-((z - 1 / 2) * u)) := by
    intro s
    rw [← integral_const_mul]
    have hsub := integral_sub_left_eq_self
      (fun u : ℝ => g s * Complex.exp ((z - 1 / 2) * s) *
        ((starRingEnd ℂ) (g u) * Complex.exp (-((z - 1 / 2) * u)))) volume s
    rw [← hsub]
    apply integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have hx : Complex.exp ((z - 1 / 2) * s) *
        Complex.exp (-((z - 1 / 2) * ((s - t : ℝ) : ℂ))) =
        Complex.exp ((z - 1 / 2) * t) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    linear_combination (-(g s * (starRingEnd ℂ) (g (s - t)))) * hx
  rw [integral_congr_ae (Filter.Eventually.of_forall step2)]
  rw [integral_mul_const, integral_conj_exp]
  rfl
