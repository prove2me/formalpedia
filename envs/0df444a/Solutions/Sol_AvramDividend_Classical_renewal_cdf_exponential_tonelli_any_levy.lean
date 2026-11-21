-- Prove2me | solution 1 for AvramDividend.Classical.renewal_cdf_exponential_tonelli_any_levy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T19:06:57.915694+00:00
-- url     : https://prove2.me/submissions/cf6e3661-28cd-41cf-95a0-a50646d99291

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
import Theorems.Thm_AvramDividend_Classical_cumulative_laplace_real_integrable_of_lintegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ν : Measure ℝ)
    (hSupp : ν (Iic (0 : ℝ)) = 0)
    (hFin : ∀ x : ℝ, 0 ≤ x → ν (Ioc (0 : ℝ) x) < ⊤)
    (hLap : ∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ → IntegrableOn (fun y : ℝ => Real.exp (-(θ * y))) (Ioi 0) ν ∧ ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) ∂ν = θ / X.ψ θ) :
    ∀ θ : ℝ, 0 ≤ θ → 0 < X.ψ θ →
      IntegrableOn (fun y : ℝ => Real.exp (-(θ * y)) * (if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0)) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * (if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0) = (X.ψ θ)⁻¹ := by
  classical
  have hSuppIio : ν (Iio (0 : ℝ)) = 0 := by
    apply measure_mono_null _ hSupp
    intro y hy; exact le_of_lt (by simpa only [mem_Iio] using hy)
  have hAEPos : ∀ᵐ y ∂ν, y ∈ Ioi (0 : ℝ) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hSupp] with y hy
    exact lt_of_not_ge (by simpa only [mem_Iic] using hy)
  have hRestrict : ν.restrict (Ioi (0 : ℝ)) = ν :=
    Measure.restrict_eq_self_of_ae_mem hAEPos
  have hCum (y : ℝ) : ν (Iic y) = ν (Ioc (0 : ℝ) y) := by
    calc
      ν (Iic y) = ν.restrict (Ioi (0 : ℝ)) (Iic y) := by rw [hRestrict]
      _ = ν (Iic y ∩ Ioi (0 : ℝ)) := Measure.restrict_apply measurableSet_Iic
      _ = ν (Ioc 0 y) := by
        congr 1; ext z; simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc, and_comm]
  letI : SigmaFinite ν := by
    apply Measure.sigmaFinite_of_countable
      (S := Set.range (fun n : ℕ => Iic (n : ℝ)))
    · exact Set.countable_range _
    · rintro s ⟨n, rfl⟩
      rw [hCum]; exact hFin (n : ℝ) (Nat.cast_nonneg n)
    · ext y
      simp only [mem_sUnion, mem_range, mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_gt y
      exact ⟨Iic (n : ℝ), ⟨n, rfl⟩, hn.le⟩
  letI : SFinite ν := inferInstance
  intro θ hθnonneg hψ
  have hθ : 0 < θ := by
    rcases hθnonneg.eq_or_lt with h0 | hpos
    · have hz : X.ψ θ = 0 := by
        subst θ; simp [SpectrallyNegativeLevy.ψ, laplaceExponent]
      exact False.elim ((ne_of_gt hψ) hz)
    · exact hpos
  have hLapFull : Integrable (fun y : ℝ => Real.exp (-(θ * y))) ν := by
    have h := (hLap θ hθnonneg hψ).1
    change Integrable (fun y : ℝ => Real.exp (-(θ * y))) (ν.restrict (Ioi (0 : ℝ))) at h
    simpa only [hRestrict] using h
  have hLapReal : (∫ y : ℝ, Real.exp (-(θ * y)) ∂ν) = θ / X.ψ θ := by
    simpa only [hRestrict] using (hLap θ hθnonneg hψ).2
  have hLapL : (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-(θ * y))) ∂ν) = ENNReal.ofReal (θ / X.ψ θ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hLapFull
      (Filter.Eventually.of_forall (fun y => Real.exp_nonneg _))]
    exact congrArg ENNReal.ofReal hLapReal
  have hTon : (∫⁻ y : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-(θ * y))) * ν (Iic y)) = ENNReal.ofReal ((X.ψ θ)⁻¹) := by
    calc
      _ = ENNReal.ofReal (1 / θ) * (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(θ * z))) ∂ν) := by
        simpa only [neg_mul] using (positiveLaplace_cumulative_measure ν θ hθ hSuppIio)
      _ = ENNReal.ofReal (1 / θ) * ENNReal.ofReal (θ / X.ψ θ) := by rw [hLapL]
      _ = ENNReal.ofReal ((X.ψ θ)⁻¹) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp [ne_of_gt hθ, ne_of_gt hψ]
  have hA := cumulative_laplace_real_integrable_of_lintegral
    ν hSupp hFin hCum θ (ENNReal.ofReal ((X.ψ θ)⁻¹))
    ENNReal.ofReal_ne_top hTon
  simpa only [ENNReal.toReal_ofReal (inv_nonneg.mpr hψ.le)] using hA
