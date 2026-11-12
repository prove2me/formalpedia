-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18x_original_J_integrable_horizon_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:21:39.889016+00:00
-- url     : https://prove2.me/submissions/70e79635-7837-47ee-a527-6ce44b7f5649

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_smallband_physical_path_envelopes
import Theorems.Thm_AvramDividend_Classical_avram_ja18t_original_J_physical_jump_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_ja18v_original_largejump_integrable_horizon_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original pathwise compensated-J envelope from two actual jump bands. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (n : ℕ) (hn : 0 < n) :
    let μ : ℝ := ∫ η, X.X 1 η ∂P
    let J : ℝ≥0 → Ω → ℝ :=
      fun t ω => X.X t ω - (t : ℝ) * μ - R t ω
    ∃ B : Ω → ℝ,
      Integrable B P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
        ‖J t ω‖ ≤ B ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let μ : ℝ := ∫ η, X.X 1 η ∂P
  let J : ℝ≥0 → Ω → ℝ :=
    fun t ω => X.X t ω - (t : ℝ) * μ - R t ω
  let L : ℝ≥0 → Ω → ℝ := fun t ω =>
    avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω
  let drift : ℝ := X.c - μ
  change ∃ B : Ω → ℝ,
    Integrable B P ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
      ‖J t ω‖ ≤ B ω)
  obtain ⟨Jsmall, hJlim, _, _, _, hBnd⟩ :=
    avram_ja18_original_smallband_physical_path_envelopes X hX hFinite
  obtain ⟨Bsm, hBsmInt, hSmDom, _⟩ := hBnd (n : ℝ≥0)
  obtain ⟨hLInt, hLDom⟩ :=
    avram_ja18v_original_largejump_integrable_horizon_envelope
      X hX hFinite n
  have hPhysical :=
    avram_ja18t_original_J_physical_jump_decomposition
      X R Jsmall hRsource hJlim
  let B : Ω → ℝ :=
    fun ω => Bsm ω + ‖L (n : ℝ≥0) ω‖ +
      (n : ℝ) * ‖drift‖
  have hBInt : Integrable B P := by
    exact (hBsmInt.add hLInt).add (integrable_const _)
  refine ⟨B, hBInt, ?_⟩
  filter_upwards [hSmDom, hPhysical] with ω hSm hJ
  intro t ht
  have hSmT := hSm t ht
  have hLT := hLDom ω t ht
  have hJt := hJ t
  have hTime : (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast ht
  have hNonneg : 0 ≤ (t : ℝ) := NNReal.coe_nonneg t
  have hMul : (t : ℝ) * ‖drift‖ ≤ (n : ℝ) * ‖drift‖ :=
    mul_le_mul_of_nonneg_right hTime (norm_nonneg _)
  have hTriangle :
      ‖Jsmall t ω + L t ω + (t : ℝ) * drift‖ ≤
        ‖Jsmall t ω‖ + ‖L t ω‖ +
          (t : ℝ) * ‖drift‖ := by
    calc
      _ ≤ ‖Jsmall t ω + L t ω‖ +
          ‖(t : ℝ) * drift‖ := norm_add_le _ _
      _ ≤ ‖Jsmall t ω‖ + ‖L t ω‖ +
          (t : ℝ) * ‖drift‖ := by
        have hnorm : ‖(t : ℝ) * drift‖ =
            (t : ℝ) * ‖drift‖ := by
          rw [norm_mul]
          simp only [Real.norm_eq_abs, abs_of_nonneg hNonneg]
        rw [hnorm]
        linarith only [norm_add_le (Jsmall t ω) (L t ω)]
  calc
    ‖J t ω‖ =
        ‖Jsmall t ω + L t ω + (t : ℝ) * drift‖ := by
      exact congrArg norm hJt
    _ ≤ ‖Jsmall t ω‖ + ‖L t ω‖ +
        (t : ℝ) * ‖drift‖ := hTriangle
    _ ≤ B ω := by
      dsimp only [B]
      exact add_le_add (add_le_add hSmT hLT) hMul
