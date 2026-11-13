-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_original_stopped_negative_mark_kernel_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T10:11:56.232693+00:00
-- url     : https://prove2.me/submissions/aaf1bde7-52d3-443c-952d-80c96628b310

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_prejump_reserve_uniform_horizon_upper
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_compact_negative_mark_loss_abs_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (T : ℝ≥0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      let b : ℝ := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      0 ≤ b → ∀ z : ℝ, z < 0 →
        |Real.exp (-(q * (t : ℝ))) * (w (b + z) - w b)| ≤ K := by
  let B : ℝ := max (x + max ((T : ℝ) * X.drift) 0) 0
  have hB : 0 ≤ B := le_max_right _ _
  obtain ⟨K, hK0, hK⟩ :=
    AvramDividend.Classical.avram_bvb_topcap_compact_negative_mark_loss_abs_bound
      w hw_cont hw_neg B hB
  have hpath :=
    AvramDividend.Classical.avram_bvb_topcap_original_prejump_reserve_uniform_horizon_upper
      X hBV x D hD T
  refine ⟨K, hK0, ?_⟩
  filter_upwards [hpath] with ω hω
  intro t ht
  dsimp only
  intro hb0 z hz
  let b : ℝ := Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  have hbB : b ≤ B := hω t ht
  have hLoss : |w (b + z) - w b| ≤ K := hK b z hb0 hbB hz
  have hqt : 0 ≤ q * (t : ℝ) := mul_nonneg hq t.property
  have hnegqt : -(q * (t : ℝ)) ≤ 0 := neg_nonpos.mpr hqt
  have he : Real.exp (-(q * (t : ℝ))) ≤ 1 := by
    calc
      Real.exp (-(q * (t : ℝ))) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr hnegqt
      _ = 1 := Real.exp_zero
  have hepos : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
    (Real.exp_pos _).le
  have heabs : |Real.exp (-(q * (t : ℝ)))| ≤ 1 := by
    simpa only [abs_of_nonneg hepos] using he
  calc
    |Real.exp (-(q * (t : ℝ))) * (w (b + z) - w b)| =
        |Real.exp (-(q * (t : ℝ)))| * |w (b + z) - w b| :=
          abs_mul _ _
    _ ≤ |Real.exp (-(q * (t : ℝ)))| * K :=
      mul_le_mul_of_nonneg_left hLoss (abs_nonneg _)
    _ ≤ 1 * K := mul_le_mul_of_nonneg_right heabs hK0
    _ = K := one_mul K
