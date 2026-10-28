-- Prove2me | solution 1 for AvramDividend.Classical.levy_capped_two_sided_first_exit_stopped_reserve_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T09:51:52.636666+00:00
-- url     : https://prove2.me/submissions/efd720ad-ffd9-4e16-a345-4fd0e480ccbd

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_stopped_path_open_eventually
import Mathlib.Topology.Order.LeftRightNhds

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Genuine first-grid exits preserve the stopped reserve on vanishing meshes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (first : ℕ → ℕ)
    (hfirst : ∀ᶠ n in atTop,
      (X.X ((first n : ℝ≥0) * mesh n) ω < lower ∨
       upper < X.X ((first n : ℝ≥0) * mesh n) ω) ∧
      (∀ j : ℕ, j < first n →
        ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
           upper < X.X ((j : ℝ≥0) * mesh n) ω))) :
    Tendsto (fun n =>
      X.X (min ((first n : ℝ≥0) * mesh n) T) ω) atTop
      (𝓝 (X.X (min τ T) ω)) := by
  refine Filter.tendsto_def.2 ?_
  intro U hU
  obtain ⟨V, hVsub, hVopen, hVmem⟩ := mem_nhds_iff.1 hU
  obtain ⟨δ, hδ, hfine⟩ :=
    chat03_capped_grid_stopped_path_open_eventually
      X ω lower upper τ T hτ V hVopen hVmem
  have hIio : Set.Iio δ ∈ 𝓝 (0 : ℝ≥0) :=
    isOpen_Iio.mem_nhds hδ
  filter_upwards [hmesh.eventually hIio, hfirst] with n hn hfn
  obtain ⟨k, hk, hkfirst, hpath⟩ := hfine (mesh n) (hpos n) hn
  have hle : first n ≤ k := by
    by_contra h
    exact hfn.2 k (Nat.lt_of_not_ge h) hk
  have hge : k ≤ first n := by
    by_contra h
    exact hkfirst (first n) (Nat.lt_of_not_ge h) hfn.1
  have heq : first n = k := le_antisymm hle hge
  apply hVsub
  simpa only [heq] using hpath
