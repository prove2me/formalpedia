-- Prove2me | solution 1 for ConnesRZ.mellinHat_conv_starInv_critical
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-20T02:21:20.308994+00:00
-- url     : https://prove2.me/submissions/806ef0c1-adc6-4dc2-8eae-f9de33353f5f

import Mathlib
import Definitions.Def_ConnesRZ_weil_defs

open Complex

open MeasureTheory ConnesRZ

namespace ConnesRZSol

/-- A test function is continuous. -/
lemma isTest_continuous {g : ℝ → ℂ} (hg : IsTest g) : Continuous g :=
  hg.1.continuous

/-- The two variable integrand of the double integral is compactly supported. -/
lemma hasCompactSupport_pair (g : ℝ → ℂ) (hg : HasCompactSupport g) (r : ℝ) :
    HasCompactSupport (fun p : ℝ × ℝ =>
      g p.2 * (starRingEnd ℂ) (g (p.2 - p.1)) * Complex.exp (I * r * p.1)) := by
  classical
  set K := tsupport g with hK
  have hKc : IsCompact K := hg
  refine HasCompactSupport.intro (K := (fun q : ℝ × ℝ => (q.2 - q.1, q.2)) '' (K ×ˢ K)) ?_ ?_
  · exact (hKc.prod hKc).image (by fun_prop)
  · rintro ⟨t, s⟩ hts
    by_contra hne
    have h1 : g s ≠ 0 := by
      intro h; apply hne; simp [h]
    have h2 : g (s - t) ≠ 0 := by
      intro h; apply hne; simp [h]
    refine hts ⟨(s - t, s), ⟨?_, ?_⟩, ?_⟩
    · exact subset_tsupport _ (by simpa using h2)
    · exact subset_tsupport _ (by simpa using h1)
    · simp

/-- The two variable integrand of the double integral is integrable. -/
lemma integrable_pair (g : ℝ → ℂ) (hg : IsTest g) (r : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      g p.2 * (starRingEnd ℂ) (g (p.2 - p.1)) * Complex.exp (I * r * p.1)) := by
  have hcont : Continuous (fun p : ℝ × ℝ =>
      g p.2 * (starRingEnd ℂ) (g (p.2 - p.1)) * Complex.exp (I * r * p.1)) := by
    have h1 : Continuous fun p : ℝ × ℝ => g p.2 := (isTest_continuous hg).comp continuous_snd
    have h2 : Continuous fun p : ℝ × ℝ => (starRingEnd ℂ) (g (p.2 - p.1)) :=
      Complex.continuous_conj.comp ((isTest_continuous hg).comp (continuous_snd.sub continuous_fst))
    have h3 : Continuous fun p : ℝ × ℝ => Complex.exp (I * r * p.1) :=
      Complex.continuous_exp.comp (by fun_prop)
    exact (h1.mul h2).mul h3
  exact hcont.integrable_of_hasCompactSupport (hasCompactSupport_pair g hg.2 r)

/-- On the critical line the transform is the Fourier transform. -/
lemma mellinHat_critical (g : ℝ → ℂ) (r : ℝ) :
    mellinHat g (1 / 2 + I * r) = ∫ t : ℝ, g t * Complex.exp (I * r * t) := by
  simp [mellinHat]

/-- The conjugate Fourier integral. -/
lemma integral_conj_exp (g : ℝ → ℂ) (r : ℝ) :
    (∫ u : ℝ, (starRingEnd ℂ) (g u) * Complex.exp (-(I * r * u))) =
      (starRingEnd ℂ) (∫ t : ℝ, g t * Complex.exp (I * r * t)) := by
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show (starRingEnd ℂ) (g u) * Complex.exp (-(I * r * u)) =
    (starRingEnd ℂ) (g u * Complex.exp (I * r * u))
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp

end ConnesRZSol

open ConnesRZSol in
theorem solution (g : ℝ → ℂ) (hg : IsTest g) (r : ℝ) :
    mellinHat (conv g (starInv g)) (1 / 2 + I * r) =
      ((‖mellinHat g (1 / 2 + I * r)‖ ^ 2 : ℝ) : ℂ) := by
  have key : mellinHat (conv g (starInv g)) (1 / 2 + I * r) =
      (∫ t : ℝ, g t * Complex.exp (I * r * t)) *
        (starRingEnd ℂ) (∫ t : ℝ, g t * Complex.exp (I * r * t)) := by
    rw [mellinHat_critical]
    have step1 : ∀ t : ℝ, conv g (starInv g) t * Complex.exp (I * r * t) =
        ∫ s : ℝ, g s * (starRingEnd ℂ) (g (s - t)) * Complex.exp (I * r * t) := by
      intro t
      show (∫ s : ℝ, g s * starInv g (t - s)) * Complex.exp (I * r * t) = _
      rw [← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      simp [starInv, neg_sub]
    rw [integral_congr_ae (Filter.Eventually.of_forall step1)]
    rw [integral_integral_swap (integrable_pair g hg r)]
    have step2 : ∀ s : ℝ,
        (∫ t : ℝ, g s * (starRingEnd ℂ) (g (s - t)) * Complex.exp (I * r * t)) =
          (g s * Complex.exp (I * r * s)) *
            ∫ u : ℝ, (starRingEnd ℂ) (g u) * Complex.exp (-(I * r * u)) := by
      intro s
      rw [← integral_const_mul]
      have hsub := integral_sub_left_eq_self
        (fun u : ℝ => g s * Complex.exp (I * r * s) *
          ((starRingEnd ℂ) (g u) * Complex.exp (-(I * r * u)))) volume s
      rw [← hsub]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      show g s * (starRingEnd ℂ) (g (s - t)) * Complex.exp (I * r * t) =
        g s * Complex.exp (I * r * s) *
          ((starRingEnd ℂ) (g (s - t)) * Complex.exp (-(I * r * ((s - t : ℝ) : ℂ))))
      have hx : Complex.exp (I * r * s) * Complex.exp (-(I * r * ((s - t : ℝ) : ℂ))) =
          Complex.exp (I * r * t) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      linear_combination (-(g s * (starRingEnd ℂ) (g (s - t)))) * hx
    rw [integral_congr_ae (Filter.Eventually.of_forall step2)]
    rw [integral_mul_const, integral_conj_exp]
  rw [key, ← mellinHat_critical, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq _
