-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:14:04.99164+00:00
-- url     : https://prove2.me/submissions/b62dd5d2-fccd-418a-a846-afc78ca286cd

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_bounded_stop_uniform_reserve_band_C2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_countable_clock_preexit_left_limit_uniform_band_bound_C2

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (r : ℕ → ℝ≥0) (lower upper : ℝ)
    (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hdense : DenseRange r)
    (B : ℝ≥0) :
    IsStoppingTime 𝓕.rightCont (fun ω : Ω =>
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0)) ∧
    ∀ (ω : Ω) (T : ℝ≥0),
      (T : WithTop ℝ≥0) ≤ min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0) →
      T ≤ B ∧
      (∀ s : ℝ≥0, s < T →
        (lower ≤ x + X.X s ω - rightLimit D s ω ∧
          x + X.X s ω - rightLimit D s ω ≤ upper) ∧
        (0 < x + X.X s ω - rightLimit D s ω ∧
          ENNReal.ofReal (x + X.X s ω - rightLimit D s ω) < C) ∧
        ContDiffWithinAt ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}
          (x + X.X s ω - rightLimit D s ω)) ∧
      ∀ t : ℝ≥0, 0 < t → t < T →
        ∃ l : ℝ,
          Tendsto (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
            (𝓝[<] t) (𝓝 l) ∧
          (lower ≤ l ∧ l ≤ upper) ∧
          (0 < l ∧ ENNReal.ofReal l < C) ∧
          ContDiffWithinAt ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} l := by
  have hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U := by
    intro s t hst U hU
    obtain ⟨u, hu, hsub⟩ :=
      (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hst).mp hU
    obtain ⟨v, hsv, hvu⟩ := exists_between hu.1
    have hopen : IsOpen (Set.Ioo s u) := isOpen_Ioo
    have hnonempty : (Set.Ioo s u).Nonempty := ⟨v, ⟨hsv, hvu⟩⟩
    obtain ⟨k, hk⟩ := hdense.exists_mem_open hopen hnonempty
    refine ⟨k, lt_of_lt_of_le hk.2 hu.2, ?_⟩
    exact hsub ⟨le_of_lt hk.1, hk.2⟩
  have hright :=
    avram_wave7_18_original_bounded_stop_uniform_reserve_band_C2
      X x D hD C w hw r lower upper hlower hcap hgrid B
  refine ⟨hright.1, ?_⟩
  intro ω T hT
  obtain ⟨hB, hstay⟩ := hright.2 ω T hT
  refine ⟨hB, hstay, ?_⟩
  intro t ht htT
  have hclock : (T : WithTop ℝ≥0) ≤ (⨅ k : ℕ,
      if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
          upper < x + X.X (r k) ω - rightLimit D (r k) ω
      then (r k : WithTop ℝ≥0) else ⊤) :=
    le_trans hT (min_le_left _ _)
  exact avram_wave7_18_original_countable_clock_preexit_left_limit_uniform_band_bound_C2
    X x D hD C w hw r lower upper hlower hcap hgrid ω T hclock t ht htT
