-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_grid_band_clock_family
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:10:32.92234+00:00
-- url     : https://prove2.me/submissions/f861a02c-7f9c-4077-9898-4b167cabe522

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_grid_band_bound_prefix
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_grid_band_stop
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_grid_band_nested_cover
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (H : ℝ≥0) (δ R : ℕ → ℝ)
    (hδ : Antitone δ) (hR : Monotone R) :
    ∃ θ : ℕ → Ω → ℝ≥0,
      (∀ k ω, θ k ω ≤ H) ∧
      (∀ k ω t, t < θ k ω → x + X.X t ω - rightLimit D t ω ∈ Icc (δ k) (R k)) ∧
      (∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (θ k ω : WithTop ℝ≥0))) ∧
      (∀ ω, Monotone (fun k => θ k ω)) ∧
      (∀ k ω t, t ≤ H →
        (∀ s : ℝ≥0, s ≤ t → x + X.X s ω - rightLimit D s ω ∈ Icc (δ k) (R k)) →
        t ≤ θ k ω) := by 
  let r : ℕ → ℝ≥0 := fun j => ((Nat.unpair j).2 : ℝ≥0) *
    (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  have hr : DenseRange r := chat05_cantor_rational_schedule_dense
  let Y : ℝ≥0 → Ω → ℝ := fun t ω => x + X.X t ω - rightLimit D t ω
  let E : ℕ → Ω → ℕ → ℝ≥0 := fun k ω j =>
    if Y (r j) ω < δ k ∨ R k < Y (r j) ω then min (r j) H else H
  let θ : ℕ → Ω → ℝ≥0 := fun k ω => ⨅ j, E k ω j
  obtain ⟨hb, hp⟩ := avram_locmoll_grid_band_bound_prefix X x D hD H δ R hδ hR r hr
  obtain ⟨hm, hc⟩ := avram_locmoll_grid_band_nested_cover X x D hD H δ R hδ hR r hr
  exact ⟨θ, hb, hp, avram_locmoll_grid_band_stop X x D hD H δ R hδ hR r hr, hm, hc⟩
