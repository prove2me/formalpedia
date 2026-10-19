-- Prove2me | solution 1 for CohnElkies.antiFourierWitness_interiorMellinL1_le_of_integrable_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/284a6eb3-dc20-48fa-9229-8a9932442651

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_antiFourierWitness_normalizedMellinStrip_shifted_integrable
import Theorems.Thm_CohnElkies_inverseQuadraticAbs_integrable

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
    {d : ℕ} (hd : 0 < d) {R σ γ C : ℝ}
    (hR : 0 < R) (hσbelow : -1 < σ) (hσabove : σ < 1)
    (w : AntiFourierWitness d R)
    (hpoint : ∀ s : ℝ,
      ‖normalizedRadialMellinStrip hd w.function R
        ((s : ℂ) + Complex.I *
          (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
        Real.exp
          (lowerStripPoissonMajorant ((d : ℝ) / 2) R σ s))
    (hmajor : ∀ S : ℝ,
      Real.exp
        (lowerStripPoissonMajorant ((d : ℝ) / 2)
          R σ (((d : ℝ) / 2) * S)) ≤
        C * Real.exp (-γ * ((d : ℝ) / 2)) /
          (1 + |S|) ^ 2) :
    (∫ s : ℝ,
      ‖normalizedRadialMellinStrip hd w.function R
        ((s : ℂ) + Complex.I *
          (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖) ≤
      (C * lowerInverseQuadraticMass) *
        ((d : ℝ) / 2) * Real.exp (-γ * ((d : ℝ) / 2)) := by
  let ℓ : ℝ := (d : ℝ) / 2
  have hℓ : 0 < ℓ := by
    try dsimp [ℓ]
    positivity
  let Z : ℝ → ℂ := fun s =>
    normalizedRadialMellinStrip hd w.function R
      ((s : ℂ) + Complex.I * (((σ * ℓ : ℝ) : ℂ)))
  have ha : (1 - σ) * ℓ < (d : ℝ) := by
    have hplus : 0 < (1 + σ) * ℓ :=
      mul_pos (by linarith) hℓ
    have hinner : 0 < (1 - σ) * ℓ :=
      mul_pos (sub_pos.mpr hσabove) hℓ
    apply (mul_lt_mul_iff_right₀ hinner).mp
    try dsimp [ℓ] at hplus hinner ⊢
    nlinarith [mul_pos hplus hinner]
  have hheight : ℓ - (1 - σ) * ℓ = σ * ℓ := by
    ring
  have hZ : Integrable Z := by
    have h :=
      antiFourierWitness_normalizedMellinStrip_shifted_integrable
        hd hR w ha
    convert! h using 1
    ext s
    try dsimp [Z, ℓ] at *
    congr 2
    push_cast
    ring
  let E : ℝ := C * Real.exp (-γ * ℓ)
  have hprofile : Integrable
      (fun S : ℝ => E / (1 + |S|) ^ 2) := by
    have h := inverseQuadraticAbs_integrable.const_mul E
    convert! h using 1
    ext S
    ring
  have hscaled : Integrable (fun S : ℝ => ‖Z (ℓ * S)‖) := by
    have h := hZ.norm.comp_mul_left' hℓ.ne'
    convert! h using 1
  have hbound :
      (∫ S : ℝ, ‖Z (ℓ * S)‖) ≤
        E * lowerInverseQuadraticMass := by
    calc
      (∫ S : ℝ, ‖Z (ℓ * S)‖) ≤
          ∫ S : ℝ, E / (1 + |S|) ^ 2 := by
        apply integral_mono_ae hscaled hprofile
        filter_upwards [] with S
        calc
          ‖Z (ℓ * S)‖ ≤
            Real.exp
              (lowerStripPoissonMajorant ℓ R σ (ℓ * S)) := by
                exact hpoint (ℓ * S)
          _ ≤ E / (1 + |S|) ^ 2 := by
                exact hmajor S
      _ = E * lowerInverseQuadraticMass := by
        unfold lowerInverseQuadraticMass
        calc
          (∫ S : ℝ, E / (1 + |S|) ^ 2) =
              ∫ S : ℝ, E * (1 / (1 + |S|) ^ 2) := by
                apply integral_congr_ae
                filter_upwards [] with S
                ring
          _ = E * (∫ S : ℝ, 1 / (1 + |S|) ^ 2) := by
                rw [integral_const_mul]
  have hchange :
      (∫ s : ℝ, ‖Z s‖) =
        ℓ * (∫ S : ℝ, ‖Z (ℓ * S)‖) := by
    have h := Measure.integral_comp_mul_left
      (fun s : ℝ => ‖Z s‖) ℓ
    rw [abs_of_pos (inv_pos.mpr hℓ), smul_eq_mul] at h
    calc
      (∫ s : ℝ, ‖Z s‖) =
          ℓ * (ℓ⁻¹ * (∫ s : ℝ, ‖Z s‖)) := by
            field_simp [hℓ.ne']
      _ = ℓ * (∫ S : ℝ, ‖Z (ℓ * S)‖) := by
            rw [← h]
  change (∫ s : ℝ, ‖Z s‖) ≤
    (C * lowerInverseQuadraticMass) * ℓ *
      Real.exp (-γ * ℓ)
  rw [hchange]
  calc
    ℓ * (∫ S : ℝ, ‖Z (ℓ * S)‖) ≤
      ℓ * (E * lowerInverseQuadraticMass) :=
        mul_le_mul_of_nonneg_left hbound hℓ.le
    _ = (C * lowerInverseQuadraticMass) * ℓ *
        Real.exp (-γ * ℓ) := by
      try dsimp [E]
      ring
end CohnElkies
