-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_countable_clock_preexit_C2_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:27:44.950534+00:00
-- url     : https://prove2.me/submissions/864be30c-ebf2-44a6-95f1-f59c5f7bfa27

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_countable_exterior_observation_inf_stopping
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_countable_exterior_exit_iff_prefix_interior_of_detection
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
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
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U) :
    IsStoppingTime 𝓕.rightCont (fun ω : Ω => ⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) ∧
    ∀ (ω : Ω) (T : ℝ≥0),
      (T : WithTop ℝ≥0) ≤ (fun ω : Ω => ⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) ω →
      ∀ s : ℝ≥0, s < T →
        (0 < x + X.X s ω - rightLimit D s ω ∧
          ENNReal.ofReal (x + X.X s ω - rightLimit D s ω) < C) ∧
        ContDiffWithinAt ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}
          (x + X.X s ω - rightLimit D s ω) := by
  have hstop := avram_wave7_18_original_countable_exterior_observation_inf_stopping
    X x D hD r lower upper
  have hdetect : ∀ ω (s t : ℝ≥0), s < t →
      (x + X.X s ω - rightLimit D s ω < lower ∨ upper < x + X.X s ω - rightLimit D s ω) →
      ∃ k, r k < t ∧ (x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
        upper < x + X.X (r k) ω - rightLimit D (r k) ω) := by
    intro ω s t hst hex
    have hcont : ContinuousWithinAt (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω)
        (Set.Ici s) s := (postPaymentReserve_cadlag_adapted X x D hD).1 ω s
    have hopen : IsOpen (Set.Iio lower ∪ Set.Ioi upper) := isOpen_Iio.union isOpen_Ioi
    have hmem : x + X.X s ω - rightLimit D s ω ∈ Set.Iio lower ∪ Set.Ioi upper := by
      simpa [Set.mem_union, Set.mem_Iio, Set.mem_Ioi] using hex
    have hlocal :
        {u : ℝ≥0 | x + X.X u ω - rightLimit D u ω < lower ∨
            upper < x + X.X u ω - rightLimit D u ω} ∈
        𝓝[Set.Ici s] s := by
      have he : ∀ᶠ u : ℝ≥0 in 𝓝[Set.Ici s] s,
          x + X.X u ω - rightLimit D u ω ∈
            Set.Iio lower ∪ Set.Ioi upper :=
        hcont.eventually (hopen.mem_nhds hmem)
      change ∀ᶠ u : ℝ≥0 in 𝓝[Set.Ici s] s,
        x + X.X u ω - rightLimit D u ω < lower ∨
          upper < x + X.X u ω - rightLimit D u ω
      filter_upwards [he] with u hu
      exact hu
    obtain ⟨k, hk, hku⟩ := hgrid s t hst _ hlocal
    exact ⟨k, hk, hku⟩
  have hprefix := avram_wave7_18_original_countable_exterior_exit_iff_prefix_interior_of_detection
    X x D hD r lower upper hdetect
  refine ⟨hstop, ?_⟩
  intro ω T hclock s hsT
  have hsband : lower ≤ x + X.X s ω - rightLimit D s ω ∧
      x + X.X s ω - rightLimit D s ω ≤ upper :=
    ((hprefix ω T).2 hclock) s hsT
  have hpos : 0 < x + X.X s ω - rightLimit D s ω :=
    lt_of_lt_of_le hlower hsband.1
  have hcap_s : ENNReal.ofReal (x + X.X s ω - rightLimit D s ω) < C :=
    hcap _ hsband
  exact ⟨⟨hpos, hcap_s⟩, hw _ ⟨hpos, hcap_s⟩⟩