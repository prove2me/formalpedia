-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_actual_jump_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:46:24.67301+00:00
-- url     : https://prove2.me/submissions/2e6d96ab-5041-4893-9dde-1f1d4939bd51

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_jump_shifted_agreement
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w V ρ : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (δ : ℝ) (hδ : 0 < δ)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hVeq : ∀ y : ℝ, ENNReal.ofReal y ≤ C → V y = w y)
    (hVmono : Monotone V) (hVnonneg : ∀ y, 0 ≤ V y)
    (hVzero : ∀ y < 0, V y = 0)
    (hρI : Integrable ρ) (hρnorm : (∫ r, ρ r) = 1)
    (hρpos : 0 ≤ᵐ[volume] ρ)
    (hρsupport : ∀ᵐ r ∂volume, ρ r ≠ 0 →
      r ∈ Icc (δ / 3) (2 * (δ / 3)))
    (hρsmooth : ContDiff ℝ 2 ρ) (hρcompact : HasCompactSupport ρ)
    (hI : ∀ y : ℝ, Integrable (fun r => ρ r * V (y - r)))
    (hg : ContDiff ℝ 2 (fun y => ∫ r, ρ r * V (y - r)))
    (y : ℝ) (hy : δ ≤ y) (hyC : ENNReal.ofReal y ≤ C)
    (hD1 : Integrable (fun r => ρ r * deriv w (y - r)))
    (hd1 : deriv (fun t => ∫ r, ρ r * V (t - r)) y =
      (∫ r, ρ r * deriv w (y - r))) :
    ∀ z < 0, SpectrallyNegativeLevy.generatorIntegrand
      (fun t => ∫ r, ρ r * V (t - r)) y z =
      ∫ r, ρ r * SpectrallyNegativeLevy.generatorIntegrand w (y - r) z := by 
  intro z hz
  obtain ⟨hVc, hd, hv, he⟩ := avram_locmoll_jump_shifted_agreement
    w V C δ y hδ hy hyC hw_smooth hVeq
  let A : ℝ → ℝ := fun r => ρ r * V (y + z - r)
  let B : ℝ → ℝ := fun r => ρ r * V (y - r)
  let D : ℝ → ℝ := fun r => ρ r * deriv w (y - r)
  let c : ℝ := (Ioo (-1 : ℝ) 1).indicator 1 z
  have hA : Integrable A := hI (y + z)
  have hB : Integrable B := hI y
  have hD : Integrable D := hD1
  have hpoint : (fun r => A r - B r - D r * z * c) =ᵐ[volume]
      (fun r => ρ r * SpectrallyNegativeLevy.generatorIntegrand w (y - r) z) := by
    filter_upwards [hρsupport] with r hr
    by_cases hzero : ρ r = 0
    · simp [A, B, D, hzero]
    · have hval := hv r (hr hzero) z hz.le
      have hbase := hv r (hr hzero) 0 le_rfl
      have hbase' : V (y - r) = w (y - r) := by simpa using hbase
      simp only [A, B, D, c, hval, hbase', SpectrallyNegativeLevy.generatorIntegrand]
      rw [show y - r + z = y + z - r by ring]
      ring
  have hlin : (∫ r, A r - B r - D r * z * c) =
      (∫ r, A r) - (∫ r, B r) - (∫ r, D r) * z * c := by
    calc
      _ = (∫ r, A r - B r) - (∫ r, D r * z * c) :=
        integral_sub (hA.sub hB) ((hD.mul_const z).mul_const c)
      _ = _ := by rw [integral_sub hA hB, integral_mul_const, integral_mul_const]
  change (∫ r, A r) - (∫ r, B r) -
    deriv (fun t => ∫ r, ρ r * V (t - r)) y * z * c = _
  rw [hd1]
  change (∫ r, A r) - (∫ r, B r) - (∫ r, D r) * z * c =
    ∫ r, ρ r * SpectrallyNegativeLevy.generatorIntegrand w (y - r) z
  exact hlin.symm.trans (integral_congr_ae hpoint)
