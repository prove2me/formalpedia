-- Prove2me | solution 1 for AvramDividend.Classical.avram_f17_original_dense_bounded_stop_exact_gaussian_C2_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:55:45.312135+00:00
-- url     : https://prove2.me/submissions/5c94ded4-3fc9-4fc8-ba2b-5b5535b09d4b

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2
import Theorems.Thm_AvramDividend_Classical_avram_f17_original_preexit_exact_leftLim_gaussian_uniform_C2_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hdense : DenseRange r) (B : ℝ≥0) :
    IsStoppingTime 𝓕.rightCont (fun ω : Ω =>
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0)) ∧
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        (T : WithTop ℝ≥0) ≤ min (⨅ k : ℕ,
          if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
              upper < x + X.X (r k) ω - rightLimit D (r k) ω
          then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0) →
        ∀ t : ℝ≥0, 0 < t → t < T →
          let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
          y ∈ Set.Icc lower upper ∧
            |Real.exp (-(q * (t : ℝ))) * deriv w y| ≤ KG ∧
            |Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w y| ≤ KH := by
  classical
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
  have hstop := avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2
    X x D hD C w hw r lower upper hlower hcap hdense B
  obtain ⟨KG, KH, hKG, hKH, hsource⟩ :=
    avram_f17_original_preexit_exact_leftLim_gaussian_uniform_C2_bound
      X hBV hν q hq C w hw x D hD r lower upper hlower hcap hgrid
  refine ⟨hstop.1, KG, KH, hKG, hKH, ?_⟩
  intro ω T hT t ht htT
  have hclock : (T : WithTop ℝ≥0) ≤ (⨅ k : ℕ,
      if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
          upper < x + X.X (r k) ω - rightLimit D (r k) ω
      then (r k : WithTop ℝ≥0) else ⊤) :=
    le_trans hT (min_le_left _ _)
  exact hsource ω T hclock t ht htT
