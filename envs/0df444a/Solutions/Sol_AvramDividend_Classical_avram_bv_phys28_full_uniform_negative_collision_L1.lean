-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_phys28_full_uniform_negative_collision_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:45:20.616914+00:00
-- url     : https://prove2.me/submissions/d8c81266-c571-4c8c-80a0-db2151fd3fb5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess27_original_measurable_drift_count_collision_L1_vanish
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_grid_exact_cell_width
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_delta_profile
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = (T : ℝ) * (i : ℝ) / ((n : ℝ) + 2)) :
    Filter.Tendsto (fun n => ∫⁻ ω,
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t, X.X t ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) -
      (∑ i ∈ Finset.range (n + 2),
        if X.X (u n (i + 1)) ω - X.X (u n i) ω <
           X.drift * (((u n (i + 1) - u n i : ℝ≥0) : ℝ))
        then (1 : ℝ≥0∞) else 0) ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  have hTr : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hStrict : ∀ n, StrictMono (u n) := by
    intro n i j hij
    have hreal : (u n i : ℝ) < (u n j : ℝ) := by
      rw [huniform n i, huniform n j]
      have hd : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      apply div_lt_div_of_pos_right _ hd
      exact mul_lt_mul_of_pos_left (by exact_mod_cast hij) hTr
    exact_mod_cast hreal
  have hZero : ∀ n, u n 0 = 0 := by
    intro n
    apply Subtype.ext
    simpa [huniform n 0]
  have hEnd : ∀ n, u n (n + 2) = T := by
    intro n
    apply Subtype.ext
    change (u n (n + 2) : ℝ) = (T : ℝ)
    rw [huniform]
    have hd : (n : ℝ) + 2 ≠ 0 := by positivity
    have hc : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    rw [hc]
    field_simp [hd]
  have hp := avram_a19_uniform_delta_profile (T : ℝ) hTr
  have hlim : Tendsto (fun n : ℕ => (T : ℝ) / ((n : ℝ) + 2))
      atTop (nhds (0 : ℝ)) := hp.2.2.2
  have hMesh : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in (atTop : Filter ℕ), ∀ i : ℕ, i < n + 2 →
        dist (u n i) (u n (i + 1)) < ε := by
    intro ε hε
    have hevent : Filter.Eventually
        (fun n : ℕ => (T : ℝ) / ((n : ℝ) + 2) < ε)
        (atTop : Filter ℕ) := hlim.eventually (Iio_mem_nhds hε)
    filter_upwards [hevent] with n hn i hi
    have hw := avram_a19_uniform_grid_exact_cell_width
      (T : ℝ) hTr u huniform n i
    have hnonneg : 0 ≤ (u n (i + 1) : ℝ) - (u n i : ℝ) := by
      rw [hw]
      exact (hp.1 n).le
    rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg hnonneg, hw]
    exact hn
  exact avram_bv_excess27_original_measurable_drift_count_collision_L1_vanish
    X hBV hFinite T hT u (fun n => n + 2) hStrict hZero hEnd hMesh

