-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_topcap_canonical_stopped_mesh_all_payment_drops_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T21:00:41.240872+00:00
-- url     : https://prove2.me/submissions/3ec0b827-5ca1-44e0-ab5d-0512dc6cbaeb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_previsible_payment_drop_nonnegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω)
    (j i : ℕ) :
    let v : ℕ → ℝ≥0 := fun k =>
      min ((k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    0 ≤ w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
      w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) := by
  intro v
  have hbase :
      ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) ≤
      (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) := by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast Nat.le_succ i
    · exact Nat.cast_nonneg _
  have hmono : v i ≤ v (i + 1) := by
    exact min_le_min_right t hbase
  have hstop : v (i + 1) ≤ t := min_le_right _ _
  have hStopInf : (v (i + 1) : ℝ≥0∞) ≤ (t : ℝ≥0∞) := by
    exact_mod_cast hstop
  exact avram_jump6_B_original_topcap_previsible_payment_drop_nonnegative
    X x C hC hTop w hw_cont hw_smooth hw_grad D hD
    ω (v i) (v (i + 1)) hmono
    (Or.inr (lt_of_le_of_lt hStopInf hStrict))
