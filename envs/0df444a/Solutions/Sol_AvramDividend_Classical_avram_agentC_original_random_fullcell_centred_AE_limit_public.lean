-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentC_original_random_fullcell_centred_AE_limit_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:36:41.337183+00:00
-- url     : https://prove2.me/submissions/c29f6818-701f-46d0-84f3-3411e99ca17b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (i : ℕ → Ω → ℕ)
    (hEnd : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ + Δ ≤ (n : ℝ≥0))
    (Z : ℕ → Ω → ℝ)
    (hZeq : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
      Z m ω = X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) :
    ∀ᵐ ω ∂P, Tendsto (fun m => Z m ω) atTop (nhds (0 : ℝ)) := by
  have hCont := avram_ubv_top11_original_zero_nu_global_continuous_ae X hν
  have hΔ : Tendsto (fun m : ℕ => (n : ℝ) / ((m : ℝ) + 1))
      atTop (nhds (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, Nat.cast_add, Nat.cast_one, mul_zero, one_mul] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (n : ℝ))
  have hDrift : Tendsto
      (fun m : ℕ => ((n : ℝ) / ((m : ℝ) + 1)) * X.c)
      atTop (nhds (0 : ℝ)) := by
    simpa using hΔ.mul_const X.c
  filter_upwards [hCont] with ω hPath
  have hUC : UniformContinuousOn (fun t : ℝ≥0 => X.X t ω)
      (Icc (0 : ℝ≥0) (n : ℝ≥0)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hPath.continuousOn
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨δ, hδ, hmod⟩ :=
    (Metric.uniformContinuousOn_iff.mp hUC) (ε / 2) hε2
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hΔ) δ hδ
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hDrift) (ε / 2) hε2
  refine ⟨max N₁ N₂, ?_⟩
  intro m hm
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
  have hlast : s + Δ ≤ (n : ℝ≥0) := hEnd m ω
  have hfirst : s ∈ Icc (0 : ℝ≥0) (n : ℝ≥0) :=
    ⟨by positivity, le_trans (le_add_of_nonneg_right (by positivity)) hlast⟩
  have hsecond : s + Δ ∈ Icc (0 : ℝ≥0) (n : ℝ≥0) :=
    ⟨by positivity, hlast⟩
  have hDeltaReal : (Δ : ℝ) = (n : ℝ) / ((m : ℝ) + 1) := by
    simp [Δ, NNReal.coe_div, NNReal.coe_add]
  have hDsmall : (Δ : ℝ) < δ := by
    have hraw := hN₁ m (le_trans (le_max_left _ _) hm)
    have hle : (n : ℝ) / ((m : ℝ) + 1) ≤
        |(n : ℝ) / ((m : ℝ) + 1)| := le_abs_self _
    rw [Real.dist_eq, sub_zero] at hraw
    rw [hDeltaReal]
    exact lt_of_le_of_lt hle hraw
  have hdist : dist s (s + Δ) < δ := by
    rw [NNReal.dist_eq, NNReal.coe_add]
    have hnΔ : 0 ≤ (Δ : ℝ) := NNReal.coe_nonneg _
    simpa [abs_of_nonneg hnΔ] using hDsmall
  have hXsmall : |X.X (s + Δ) ω - X.X s ω| < ε / 2 := by
    have hh := hmod s hfirst (s + Δ) hsecond hdist
    rw [Real.dist_eq] at hh
    simpa only [abs_sub_comm] using hh
  have hCsmall : |(Δ : ℝ) * X.c| < ε / 2 := by
    have hraw := hN₂ m (le_trans (le_max_right _ _) hm)
    simpa only [Real.dist_eq, sub_zero, hDeltaReal] using hraw
  have hZvalue : Z m ω =
      X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c := hZeq m ω
  rw [Real.dist_eq, sub_zero, hZvalue]
  have htr : |(X.X (s + Δ) ω - X.X s ω) - (Δ : ℝ) * X.c| ≤
      |X.X (s + Δ) ω - X.X s ω| + |(Δ : ℝ) * X.c| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      (abs_add_le (X.X (s + Δ) ω - X.X s ω) (-((Δ : ℝ) * X.c)))
  linarith
