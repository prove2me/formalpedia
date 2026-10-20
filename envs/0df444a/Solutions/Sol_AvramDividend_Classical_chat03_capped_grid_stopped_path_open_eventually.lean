-- Prove2me | solution 1 for AvramDividend.Classical.chat03_capped_grid_stopped_path_open_eventually
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:48:24.714098+00:00
-- url     : https://prove2.me/submissions/e49ad3f7-77aa-4758-8c33-c8c459f68846

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_capped_time_convergence
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

/-!
Right continuity transfers capped first-grid time convergence to the
actual sample-path value at the capped continuous strict-exit infimum.
The limit assertion is deliberately phrased for arbitrary open sets U.
It does not assume global continuity of the q-scale function W at zero.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (U : Set ℝ) (hU : IsOpen U)
    (hmem : X.X (min τ T) ω ∈ U) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
        ∃ k : ℕ,
          (X.X ((k : ℝ≥0) * h) ω < lower ∨
           upper < X.X ((k : ℝ≥0) * h) ω) ∧
          (∀ j : ℕ, j < k →
            ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
               upper < X.X ((j : ℝ≥0) * h) ω)) ∧
          X.X (min ((k : ℝ≥0) * h) T) ω ∈ U := by
  let t : ℝ≥0 := min τ T
  have hright : ∀ᶠ s in 𝓝[Set.Ici t] t, X.X s ω ∈ U :=
    (X.rightCont ω t).eventually (hU.mem_nhds hmem)
  have hnhds : ∀ᶠ s in 𝓝 t,
      s ∈ Set.Ici t → X.X s ω ∈ U :=
    eventually_nhdsWithin_iff.mp hright
  have hset :
      {s : ℝ≥0 | s ∈ Set.Ici t → X.X s ω ∈ U} ∈ 𝓝 t := hnhds
  have htlt : t < t + 1 := lt_add_of_pos_right t zero_lt_one
  obtain ⟨u, hu, hsub⟩ := exists_Ico_subset_of_mem_nhds' hset htlt
  let ε : ℝ≥0 := u - t
  have hε : 0 < ε := tsub_pos_iff_lt.mpr hu.1
  have hteq : t + ε = u := add_tsub_cancel_of_le hu.1.le
  obtain ⟨δ, hδ, hmesh⟩ :=
    chat03_first_grid_capped_time_convergence
      X ω lower upper τ T hτ ε hε
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhd
  obtain ⟨k, hkExit, hkfirst, hklo, hkhi⟩ := hmesh h hh hhd
  refine ⟨k, hkExit, hkfirst, ?_⟩
  have hku : min ((k : ℝ≥0) * h) T < u := by
    simpa only [t, hteq] using hkhi
  exact (hsub ⟨hklo, hku⟩) hklo
