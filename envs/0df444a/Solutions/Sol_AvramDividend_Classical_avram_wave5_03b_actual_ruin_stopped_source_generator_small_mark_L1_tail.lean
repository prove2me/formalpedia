-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_source_generator_small_mark_L1_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:40:57.253801+00:00
-- url     : https://prove2.me/submissions/64e7b6d1-0035-4e51-81bc-e3b60b32a2b3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_near_C2_L1_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_integrable_mark_energy_tail_iInf_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine stopped controlled Taylor-generator correction loses no
absolute compensator drift on shrinking sufficiently small Lévy mark sets. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hu : 0 < u + δ) (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    ∃ r : ℝ, 0 < r ∧
      ∀ (B : ℕ → Set ℝ)
        (hBm : ∀ n, MeasurableSet (B n))
        (hBnear : ∀ n, B n ⊆ Ioo (-r) 0)
        (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅),
      (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) = 0 := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then
      p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
      else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  change ∃ r : ℝ, 0 < r ∧
      ∀ (B : ℕ → Set ℝ)
        (hBm : ∀ n, MeasurableSet (B n))
        (hBnear : ∀ n, B n ⊆ Ioo (-r) 0)
        (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅),
      (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) = 0
  obtain ⟨r, M, hr, hrle, hM, hnear⟩ :=
    avram_wave5_03b_actual_ruin_stopped_source_generator_near_C2_L1_envelope
      X x D hD w C u v δ hw hu huv hv
  refine ⟨r, hr, ?_⟩
  intro B hBm hBnear hBanti hBempty
  let f : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (min 1 (z ^ 2))
  let S (n : ℕ) : ℝ≥0∞ := ∫⁻ z in B n, f z ∂X.ν
  let A (n : ℕ) : ℝ≥0∞ :=
    ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ
  have hfmeas : Measurable f := by fun_prop
  have hfint : (∫⁻ z, f z ∂X.ν) ≠ ⊤ := ne_of_lt X.ν_integrable
  have hSzero : (⨅ n : ℕ, S n) = 0 := by
    exact avram_wave4_p1_integrable_mark_energy_tail_iInf_zero
      X.ν f hfmeas hfint B hBm hBanti hBempty
  have hνmeas : Measurable (fun z : ℝ =>
      ENNReal.ofReal (min 1 (z ^ 2))) := by fun_prop
  have hmin (z : ℝ) : 0 ≤ min (1 : ℝ) (z ^ 2) :=
    le_min (by norm_num) (sq_nonneg z)
  have hpoint (p : ℝ≥0 × Ω) (z : ℝ) (hz : z ∈ Ioo (-r) 0) :
      |HS (p,z)| ≤ M * min 1 (z ^ 2) := by
    have hrone : r ≤ 1 := le_trans hrle (min_le_right _ _)
    have hzleft : -1 < z := by have := hz.1; linarith
    have hzsq : z ^ 2 ≤ 1 := by
      have hleft : 0 ≤ z + 1 := by linarith
      have hright : 0 ≤ 1 - z := by linarith [hz.2]
      nlinarith [mul_nonneg hleft hright]
    have hminsq : min (1 : ℝ) (z ^ 2) = z ^ 2 := min_eq_right hzsq
    by_cases hb : Y p ∈ Icc (u + δ) v
    · rw [hminsq]
      exact hnear p hb z hz
    · have hb' : ¬ (u + δ ≤ Y p ∧ Y p ≤ v) := hb
      have hH : H (p,z) = 0 := by simp [H, Set.mem_Icc, hb']
      have hHS : HS (p,z) = 0 := by simp [HS, hH]
      simpa [hHS] using (mul_nonneg hM (hmin z))
  have hbound (n : ℕ) :
      A n ≤ (μ Set.univ * ENNReal.ofReal M) * S n := by
    have hpoint' (p : ℝ≥0 × Ω) (z : ℝ) (hz : z ∈ B n) :
        ENNReal.ofReal (|HS (p,z)|) ≤
        ENNReal.ofReal M * ENNReal.ofReal (min 1 (z ^ 2)) := by
      rw [← ENNReal.ofReal_mul hM]
      exact ENNReal.ofReal_le_ofReal (hpoint p z (hBnear n hz))
    have hinner (p : ℝ≥0 × Ω) :
        (∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν) ≤
          ENNReal.ofReal M *
            (∫⁻ z in B n, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν) := by
      calc
        (∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν) ≤
          ∫⁻ z in B n, ENNReal.ofReal M *
            ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν := by
              apply setLIntegral_mono (by fun_prop)
              intro z hz
              exact hpoint' p z hz
        _ = _ := lintegral_const_mul _ hνmeas
    calc
      A n ≤
          ∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal M *
            (∫⁻ z in B n, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν) ∂μ :=
        lintegral_mono hinner
      _ = μ Set.univ * (ENNReal.ofReal M * S n) := by
        simp [S, f, mul_comm]
      _ = (μ Set.univ * ENNReal.ofReal M) * S n := by
        rw [mul_assoc]
  change (⨅ n : ℕ, A n) = 0
  apply le_antisymm _ bot_le
  calc
    (⨅ n : ℕ, A n) ≤
        (⨅ n : ℕ, (μ Set.univ * ENNReal.ofReal M) * S n) :=
      iInf_mono hbound
    _ = (μ Set.univ * ENNReal.ofReal M) * (⨅ n : ℕ, S n) := by
      by_cases hc : μ Set.univ * ENNReal.ofReal M = 0
      · simp [hc]
      · rw [ENNReal.mul_iInf_of_ne hc
          (ne_of_lt (ENNReal.mul_lt_top hμ ENNReal.ofReal_lt_top))]
    _ = 0 := by simp [hSzero]
