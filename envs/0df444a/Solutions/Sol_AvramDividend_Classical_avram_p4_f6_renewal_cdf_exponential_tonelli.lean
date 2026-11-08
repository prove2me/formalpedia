-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_renewal_cdf_exponential_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:56:24.863833+00:00
-- url     : https://prove2.me/submissions/4271de3c-ec98-44d9-ae71-5267a2edc224

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hσ : 0 < X.σ)
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
    intro y hy
    exact le_of_lt (by simpa only [mem_Iio] using hy)
  have hAEPos : ∀ᵐ y ∂ν, y ∈ Ioi (0 : ℝ) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hSupp] with y hy
    exact lt_of_not_ge (by simpa only [mem_Iic] using hy)
  have hRestrict : ν.restrict (Ioi (0 : ℝ)) = ν :=
    Measure.restrict_eq_self_of_ae_mem hAEPos
  have hCum (y : ℝ) : ν (Iic y) = ν (Ioc (0 : ℝ) y) := by
    have hs : Iic y ∩ Ioi (0 : ℝ) = Ioc 0 y := by
      ext z
      simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc]
      constructor <;> intro hz <;> exact ⟨hz.2, hz.1⟩
    calc
      ν (Iic y) = ν.restrict (Ioi (0 : ℝ)) (Iic y) := by rw [hRestrict]
      _ = ν (Iic y ∩ Ioi (0 : ℝ)) := Measure.restrict_apply measurableSet_Iic
      _ = ν (Ioc 0 y) := by rw [hs]
  letI : SigmaFinite ν := by
    apply Measure.sigmaFinite_of_countable
      (S := Set.range (fun n : ℕ => Iic (n : ℝ)))
    · exact Set.countable_range _
    · intro s hs
      rcases hs with ⟨n, rfl⟩
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hs : Iic (n : ℝ) = Iic (0 : ℝ) ∪ Ioc (0 : ℝ) (n : ℝ) := by
        ext y
        simp only [mem_Iic, mem_union, mem_Ioc]
        constructor
        · intro hy
          by_cases h0 : y ≤ 0
          · exact Or.inl h0
          · exact Or.inr ⟨lt_of_not_ge h0, hy⟩
        · intro hy
          rcases hy with h0 | hy
          · exact h0.trans hn0
          · exact hy.2
      have hle : ν (Iic (n : ℝ)) ≤ ν (Iic (0 : ℝ)) + ν (Ioc (0 : ℝ) (n : ℝ)) := by
        rw [hs]
        exact measure_union_le _ _
      exact lt_of_le_of_lt hle (by simpa only [hSupp, zero_add] using hFin (n : ℝ) hn0)
    · ext y
      simp only [mem_sUnion, mem_range, mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_gt y
      exact ⟨Iic (n : ℝ), ⟨n, rfl⟩, hn.le⟩
  letI : SFinite ν := inferInstance
  intro θ hθnonneg hψ
  have hθ : 0 < θ := by
    rcases hθnonneg.eq_or_lt with h0 | hpos
    · have hz : X.ψ θ = 0 := by
        subst θ
        simp [SpectrallyNegativeLevy.ψ, laplaceExponent]
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
    exact ENNReal.ofReal_ne_top
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
  change (∫ y in Ioi (0 : ℝ), f y) = (X.ψ θ)⁻¹
  rw [hReal, hL, hTon, ENNReal.toReal_ofReal (inv_nonneg.mpr hψ.le)]
