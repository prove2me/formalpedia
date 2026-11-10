-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin_source13_original_annulus_offtime_lintegral_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:06:09.55706+00:00
-- url     : https://prove2.me/submissions/163a93d9-5023-4349-8e8a-872edf1d597f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_offtime_product_mean
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin_source13_original_annulus_count_finite_every_path
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_negative_band_rate_finite_n
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original past/future negative-annulus ENNReal cell product has the exact source mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let A : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ B)
    let F : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    (∫⁻ ω, A ω * F ω ∂P) =
      ((s : ℝ≥0∞) * X.ν B) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
  let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let J : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc a b ×ˢ B)
  let A : Ω → ℝ≥0∞ := J 0 s
  let F : Ω → ℝ≥0∞ := J s t
  let r : ℝ := ((s : ℝ≥0∞) * X.ν B).toReal
  let q : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
  change (∫⁻ ω, A ω * F ω ∂P) =
    ((s : ℝ≥0∞) * X.ν B) *
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
  have hReal :=
    avram_mix_fin_source13_original_annulus_offtime_product_mean
      X s t hst n m hnm
  change Integrable (fun ω => (A ω).toReal * (F ω).toReal) P ∧
    (∫ ω, (A ω).toReal * (F ω).toReal ∂P) = r * q at hReal
  have hA (ω : Ω) : A ω ≠ ⊤ := by
    have h := avram_mix_fin_source13_original_annulus_count_finite_every_path
      X s n m hnm ω
    change A ω ≠ ⊤ at h
    exact h
  have hF (ω : Ω) : F ω ≠ ⊤ := by
    have hT := avram_mix_fin_source13_original_annulus_count_finite_every_path
      X t n m hnm ω
    change J 0 t ω ≠ ⊤ at hT
    have hsub : Ioc s t ×ˢ B ⊆ Ioc 0 t ×ˢ B := by
      rintro ⟨u, z⟩ ⟨hu, hz⟩
      exact ⟨⟨lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hu.1, hu.2⟩, hz⟩
    have hle : F ω ≤ J 0 t ω := by
      exact measure_mono hsub
    intro htop
    apply hT
    exact top_unique (by simpa only [htop] using hle)
  have hνm : X.ν (Iic (-(1 / ((m : ℝ) + 1)))) < ⊤ :=
    avram_p2_e_compensator_original_negative_band_rate_finite_n X m
  have hν : X.ν B < ⊤ := by
    exact lt_of_le_of_lt (measure_mono (by
      intro x hx
      exact hx.2)) hνm
  have hr : ((s : ℝ≥0∞) * X.ν B) ≠ ⊤ :=
    ne_of_lt (ENNReal.mul_lt_top (by simp) hν)
  have hq : (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) ≠ ⊤ :=
    ne_of_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hν)
  have hnn : 0 ≤ᵐ[P] (fun ω => (A ω).toReal * (F ω).toReal) :=
    Filter.Eventually.of_forall (fun ω =>
      mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  have hEq (ω : Ω) :
      ENNReal.ofReal ((A ω).toReal * (F ω).toReal) = A ω * F ω := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (hA ω),
        ENNReal.ofReal_toReal (hF ω)]
  have hFun : (fun ω => A ω * F ω) =
      (fun ω => ENNReal.ofReal ((A ω).toReal * (F ω).toReal)) := by
    funext ω
    exact (hEq ω).symm
  rw [hFun]
  calc
    (∫⁻ ω, ENNReal.ofReal ((A ω).toReal * (F ω).toReal) ∂P) =
        ENNReal.ofReal (∫ ω, (A ω).toReal * (F ω).toReal ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hReal.1 hnn).symm
    _ = ENNReal.ofReal (r * q) := by rw [hReal.2]
    _ = ((s : ℝ≥0∞) * X.ν B) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
              ENNReal.ofReal_toReal hr, ENNReal.ofReal_toReal hq]