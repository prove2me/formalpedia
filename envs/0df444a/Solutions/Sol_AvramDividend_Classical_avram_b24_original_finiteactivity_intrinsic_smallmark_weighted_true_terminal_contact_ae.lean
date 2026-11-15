-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_finiteactivity_intrinsic_smallmark_weighted_true_terminal_contact_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:31:12.607581+00:00
-- url     : https://prove2.me/submissions/39710a3b-7254-4cd3-afe1-a76464d34e9d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_compensated_smallmark_single_finite_horizon_path_representation_ae
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_arbitrary_intrinsic_smallmark_source_right_continuous_ae
import Theorems.Thm_AvramDividend_Classical_avram_b24_finite_actual_marked_source_weighted_terminal_contact_mesh_jump_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (T : ℝ≥0) (σ : Ω → ℝ≥0) (hσ : ∀ ω, σ ω ≤ T)
    (a b : ℕ → Ω → ℝ≥0)
    (W : ℕ → Ω → ℝ) (Wleft : Ω → ℝ)
    (ha : ∀ᵐ ω ∂P, 0 < σ ω →
      Tendsto (fun k => a k ω) atTop (𝓝[<] (σ ω)))
    (hb : ∀ᵐ ω ∂P, 0 < σ ω →
      Tendsto (fun k => b k ω) atTop (𝓝[Ici (σ ω)] (σ ω)))
    (hW : ∀ᵐ ω ∂P, 0 < σ ω →
      Tendsto (fun k => W k ω) atTop (𝓝 (Wleft ω))) :
    ∀ᵐ ω ∂P, 0 < σ ω →
      Tendsto (fun k => W k ω *
        (Jsmall (b k ω) ω - Jsmall (a k ω) ω)) atTop
      (𝓝 (Wleft ω *
        (if -1 < X.X (σ ω) ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) (σ ω) ∧
             X.X (σ ω) ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) (σ ω) < 0
         then X.X (σ ω) ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) (σ ω)
         else 0))) := by
  have hHorizon :=
    AvramDividend.Classical.avram_b24_original_compensated_smallmark_single_finite_horizon_path_representation_ae
      X hFinite Jsmall hJsource
  have hRight :=
    AvramDividend.Classical.avram_b24_original_arbitrary_intrinsic_smallmark_source_right_continuous_ae
      X hX hFinite Jsmall hJsource
  filter_upwards [hHorizon, hRight, ha, hb, hW] with
    ω hHω hRω haω hbω hWω
  intro hpos
  obtain ⟨S, hS, hPath⟩ := hHω T
  let z : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let d : ℝ := ∫ v in Ioo (-1 : ℝ) 0, v ∂X.ν
  have hPath' (v : ℝ≥0) (hv : v ≤ T) :
      Jsmall v ω =
        (∑ u ∈ S, if u ≤ v then
          (if -1 < z u ∧ z u < 0 then z u else 0) else 0) -
        (v : ℝ) * d := by
    simpa only [z, d] using hPath v hv
  have hLim :=
    AvramDividend.Classical.avram_b24_finite_actual_marked_source_weighted_terminal_contact_mesh_jump_limit
      S z d (fun u => Jsmall u ω) T (σ ω) hpos (hσ ω)
      hPath' (hRω (σ ω))
      (fun k => a k ω) (fun k => b k ω)
      (fun k => W k ω) (Wleft ω)
      (haω hpos) (hbω hpos) (hWω hpos)
  change Tendsto (fun k => W k ω *
    (Jsmall (b k ω) ω - Jsmall (a k ω) ω)) atTop
      (𝓝 (Wleft ω *
        (if -1 < z (σ ω) ∧ z (σ ω) < 0
          then z (σ ω) else 0)))
  by_cases hMark : -1 < z (σ ω) ∧ z (σ ω) < 0
  · have hmem : σ ω ∈ S :=
      (hS (σ ω)).2 ⟨hpos, hσ ω, ne_of_lt hMark.2⟩
    simpa [hmem, hMark] using hLim
  · simpa [hMark] using hLim
