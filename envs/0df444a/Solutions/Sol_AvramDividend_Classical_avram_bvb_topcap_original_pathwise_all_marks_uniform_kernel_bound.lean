-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_original_pathwise_all_marks_uniform_kernel_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:44:08.307173+00:00
-- url     : https://prove2.me/submissions/05e0b522-fe20-4436-b0ea-8fa1368ad3e1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_original_stopped_negative_mark_kernel_uniform_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCapTop : C = ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t : ℝ≥0, ∀ z : ℝ,
        |H n ((t, ω), z)| ≤ K := by
  intro δ U H
  let Tnn : ℝ≥0 := ⟨T, hT.le⟩
  obtain ⟨K, hK, hPath⟩ :=
    AvramDividend.Classical.avram_bvb_topcap_original_stopped_negative_mark_kernel_uniform_bound
      X hBV q hq w hw_cont hw_neg x D hD.1.1 Tnn
  refine ⟨K, hK, ?_⟩
  filter_upwards [hPath] with ω hω
  intro n t z
  by_cases hmask :
      0 < t ∧ (t : ℝ) < T - δ n ∧
      (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      0 ≤ U t ω ∧ ENNReal.ofReal (U t ω) ≤ C ∧ z < 0
  · have hδ : 0 ≤ δ n := div_nonneg hT.le (by positivity)
    have htime : (t : ℝ) < T :=
      lt_of_lt_of_le hmask.2.1 (sub_le_self T hδ)
    have ht : t ≤ Tnn := by
      exact_mod_cast (le_of_lt htime)
    have hpoint := hω t ht hmask.2.2.2.1 z hmask.2.2.2.2.2
    simpa only [U, H, if_pos hmask] using hpoint
  · simpa only [H, if_neg hmask, abs_zero] using hK
