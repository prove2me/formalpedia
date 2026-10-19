-- Prove2me | solution 1 for CohnElkies.uniformAntiFourierSignRadius_of_poisson_majorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/e544815c-8c59-4e22-8951-ff343294cfe3

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_no_antiFourierWitness_of_interiorMellinL1_lt_half
import Theorems.Thm_CohnElkies_exists_lowerStripPoissonMajorant_integrable_majorant
import Theorems.Thm_CohnElkies_antiFourierWitness_interiorMellinL1_le_of_integrable_majorant

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology
namespace CohnElkies
theorem _root_.solution
    (hpoisson :
      ∀ {d : ℕ} (hd : 0 < d) {R : ℝ} (_hR : 0 < R)
        (w : AntiFourierWitness d R)
        {σ : ℝ} (_hσbelow : -1 < σ) (_hσabove : σ < 1)
        (s : ℝ),
        ‖normalizedRadialMellinStrip hd w.function R
          ((s : ℂ) + Complex.I *
            (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
          Real.exp
            (lowerStripPoissonMajorant ((d : ℝ) / 2) R σ s)) :
    UniformAntiFourierSignRadius := by
  intro c hc hcritical
  have hsharp : c < Real.pi⁻¹ := by
    simpa [criticalRadius] using! hcritical
  obtain ⟨σ, γ, C, hσpos, hσone, hγ, hC, hmajor⟩ :=
    exists_lowerStripPoissonMajorant_integrable_majorant hc hsharp
  let J : ℝ := lowerInverseQuadraticMass
  let Q : ℝ := C * J
  let K : ℝ := (2 * Real.pi)⁻¹ * Q / (1 - σ)
  have hσbelow : -1 < σ := by linarith
  have hsigmapos : 0 < 1 - σ := sub_pos.mpr hσone
  have hscale : Tendsto
      (fun d : ℕ => (d : ℝ) / 2) atTop atTop := by
    have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
    have hmul := hcast.atTop_mul_const
      (by norm_num : (0 : ℝ) < 1 / 2)
    convert! hmul using 1
    ext d
    ring
  have hγscale : Tendsto
      (fun d : ℕ => γ * ((d : ℝ) / 2)) atTop atTop := by
    have h := hscale.atTop_mul_const hγ
    convert! h using 1
    ext d
    ring
  have hnegative : Tendsto
      (fun d : ℕ => -(γ * ((d : ℝ) / 2))) atTop atBot :=
    Filter.tendsto_neg_atTop_atBot.comp hγscale
  have hexp : Tendsto
      (fun d : ℕ => Real.exp (-(γ * ((d : ℝ) / 2))))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hnegative
  have hlimit : Tendsto
      (fun d : ℕ => K *
        Real.exp (-γ * ((d : ℝ) / 2))) atTop (𝓝 0) := by
    have h := hexp.const_mul K
    convert! h using 1
    · ext d
      congr 1
      ring_nf
    · simp
  have hsmall : ∀ᶠ d : ℕ in atTop,
      K * Real.exp (-γ * ((d : ℝ) / 2)) < (1 / 2 : ℝ) :=
    hlimit.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    hmajor, hsmall] with d hd hmaj hsmall_d
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdreal : 0 < (d : ℝ) := Nat.cast_pos.mpr hdpos
  have hR : 0 < c * Real.sqrt (d : ℝ) :=
    mul_pos hc (Real.sqrt_pos.mpr hdreal)
  refine ⟨?_⟩
  intro w
  have hpoint : ∀ s : ℝ,
      ‖normalizedRadialMellinStrip hdpos w.function
        (c * Real.sqrt (d : ℝ))
        ((s : ℂ) + Complex.I *
          (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
        Real.exp
          (lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt (d : ℝ)) σ s) := by
    intro s
    exact hpoisson hdpos hR w hσbelow hσone s
  have hL1 :=
    antiFourierWitness_interiorMellinL1_le_of_integrable_majorant
      hdpos hR hσbelow hσone w hpoint hmaj
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  have hden : 0 < (1 - σ) * ((d : ℝ) / 2) :=
    mul_pos hsigmapos hℓ
  have hpi : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hbound :
      ((2 * Real.pi)⁻¹ *
        ∫ s : ℝ,
          ‖normalizedRadialMellinStrip hdpos w.function
            (c * Real.sqrt (d : ℝ))
            ((s : ℂ) + Complex.I *
              (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖) /
          ((1 - σ) * ((d : ℝ) / 2)) ≤
        K * Real.exp (-γ * ((d : ℝ) / 2)) := by
    calc
      ((2 * Real.pi)⁻¹ *
        ∫ s : ℝ,
          ‖normalizedRadialMellinStrip hdpos w.function
            (c * Real.sqrt (d : ℝ))
            ((s : ℂ) + Complex.I *
              (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖) /
          ((1 - σ) * ((d : ℝ) / 2)) ≤
        ((2 * Real.pi)⁻¹ *
          ((C * lowerInverseQuadraticMass) *
            ((d : ℝ) / 2) *
              Real.exp (-γ * ((d : ℝ) / 2)))) /
          ((1 - σ) * ((d : ℝ) / 2)) := by
        apply (div_le_div_iff_of_pos_right hden).2
        exact mul_le_mul_of_nonneg_left hL1 hpi
      _ = K * Real.exp (-γ * ((d : ℝ) / 2)) := by
        try dsimp [K, Q, J]
        field_simp [hsigmapos.ne', hℓ.ne']
  exact no_antiFourierWitness_of_interiorMellinL1_lt_half
    hdpos hR hσbelow hσone w
      (lt_of_le_of_lt hbound hsmall_d)
end CohnElkies
