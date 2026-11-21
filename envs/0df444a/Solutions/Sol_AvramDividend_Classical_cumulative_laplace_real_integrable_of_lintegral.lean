-- Prove2me | solution 1 for AvramDividend.Classical.cumulative_laplace_real_integrable_of_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T19:06:27.220542+00:00
-- url     : https://prove2.me/submissions/ee9bba5b-43f0-4a94-bbfc-8f5cf27324e7

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (ν : Measure ℝ) (hSupp : ν (Iic (0 : ℝ)) = 0)
    (hFin : ∀ x : ℝ, 0 ≤ x → ν (Ioc (0 : ℝ) x) < ⊤)
    (hCum : ∀ y : ℝ, ν (Iic y) = ν (Ioc (0 : ℝ) y))
    (θ : ℝ) (L : ℝ≥0∞) (hLfinite : L ≠ ⊤)
    (hTon : (∫⁻ y : ℝ in Ioi 0,
      ENNReal.ofReal (Real.exp (-(θ * y))) * ν (Iic y)) = L) :
    IntegrableOn
      (fun y : ℝ => Real.exp (-(θ * y)) *
        (if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0))
      (Ioi (0 : ℝ)) ∧
    (∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) *
        (if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0)) =
      L.toReal := by
  classical
  let f : ℝ → ℝ := fun y => Real.exp (-(θ * y)) * (if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0)
  have hFN (y : ℝ) : 0 ≤ f y := by dsimp [f]; positivity
  have hMono : Monotone (fun y : ℝ => ν (Iic y)) :=
    fun a b hab => measure_mono (Iic_subset_Iic.mpr hab)
  have hMeasC : Measurable (fun y : ℝ => (ν (Iic y)).toReal) :=
    hMono.measurable.ennreal_toReal
  have hFGlobal (y : ℝ) : (if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0) = (ν (Iic y)).toReal := by
    by_cases hy : 0 ≤ y
    · simp [hy, ← hCum y]
    · have hz : ν (Iic y) = 0 := by
        apply measure_mono_null _ hSupp
        intro z hz
        exact hz.trans (le_of_lt (lt_of_not_ge hy))
      simp [hy, hz]
  have hFMeas : Measurable f := by
    have hf : f = fun y : ℝ => Real.exp (-(θ * y)) * (ν (Iic y)).toReal := by
      funext y
      simp only [f, hFGlobal y]
    rw [hf]
    exact (by fun_prop : Measurable (fun y : ℝ => Real.exp (-(θ * y)))).mul hMeasC
  have hL : (∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal (f y)) = ∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-(θ * y))) * ν (Iic y) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hypos : 0 < y := by simpa only [mem_Ioi] using hy
    have hμfin : ν (Iic y) < ⊤ := by
      simpa only [hCum y] using hFin y hypos.le
    simp only [f, if_pos hypos.le]
    rw [← hCum y, ENNReal.ofReal_mul (Real.exp_nonneg _),
      ENNReal.ofReal_toReal (ne_of_lt hμfin)]
  have hfinite : (∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal (f y)) ≠ ⊤ := by
    rw [hL, hTon]
    exact hLfinite
  have hIntF : IntegrableOn f (Ioi (0 : ℝ)) := by
    exact (lintegral_ofReal_ne_top_iff_integrable
      (hFMeas.aestronglyMeasurable)
      (Filter.Eventually.of_forall hFN)).mp hfinite
  have hReal : (∫ y in Ioi (0 : ℝ), f y) = (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (f y)).toReal := by
    have h := integral_toReal
      (μ := (volume : Measure ℝ).restrict (Ioi (0 : ℝ)))
      (f := fun y : ℝ => ENNReal.ofReal (f y))
      (hFMeas.ennreal_ofReal.aemeasurable)
      (Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top))
    calc
      (∫ y in Ioi (0 : ℝ), f y) =
          ∫ y in Ioi (0 : ℝ), (ENNReal.ofReal (f y)).toReal := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro y _
            exact (ENNReal.toReal_ofReal (hFN y)).symm
      _ = (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (f y)).toReal := h
  refine ⟨hIntF, ?_⟩
  change (∫ y in Ioi (0 : ℝ), f y) = L.toReal
  rw [hReal, hL, hTon]
