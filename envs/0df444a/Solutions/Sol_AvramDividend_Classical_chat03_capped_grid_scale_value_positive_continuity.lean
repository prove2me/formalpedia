-- Prove2me | solution 1 for AvramDividend.Classical.chat03_capped_grid_scale_value_positive_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:55:30.895212+00:00
-- url     : https://prove2.me/submissions/6eede9e5-1056-449e-8f34-f58ec67ded53

import Definitions.Def_AvramDividend_Classical_ScaleFunction
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
At a strictly positive limiting reserve, continuity of the q-scale
function on the nonnegative axis transports right-continuous stopped-path
convergence to stopped scale values. The W(0)>0 boundary is excluded.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hpos : 0 < x + X.X (min τ T) ω)
    (U : Set ℝ) (hU : IsOpen U)
    (hmem : W (x + X.X (min τ T) ω) ∈ U) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
        ∃ k : ℕ,
          (X.X ((k : ℝ≥0) * h) ω < lower ∨
           upper < X.X ((k : ℝ≥0) * h) ω) ∧
          (∀ j : ℕ, j < k →
            ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
               upper < X.X ((j : ℝ≥0) * h) ω)) ∧
          W (x + X.X (min ((k : ℝ≥0) * h) T) ω) ∈ U := by
  let t : ℝ≥0 := min τ T
  have hIci : Set.Ici (0 : ℝ) ∈ 𝓝 (x + X.X t ω) := by
    apply Filter.mem_of_superset (isOpen_Ioi.mem_nhds hpos)
    intro y hy
    change (0 : ℝ) < y at hy
    exact le_of_lt hy
  have hContW : ContinuousAt W (x + X.X t ω) :=
    hW.2.2.1.continuousAt hIci
  have hadd : ContinuousAt (fun z : ℝ => x + z) (X.X t ω) :=
    continuousAt_const.add continuousAt_id
  have hcomp : ContinuousAt (fun z : ℝ => W (x + z)) (X.X t ω) :=
    hContW.comp hadd
  have hright : ∀ᶠ s in 𝓝[Set.Ici t] t,
      W (x + X.X s ω) ∈ U :=
    (hcomp.tendsto.comp (X.rightCont ω t)).eventually
      (hU.mem_nhds hmem)
  have hnhds : ∀ᶠ s in 𝓝 t,
      s ∈ Set.Ici t → W (x + X.X s ω) ∈ U :=
    eventually_nhdsWithin_iff.mp hright
  have hset :
      {s : ℝ≥0 | s ∈ Set.Ici t → W (x + X.X s ω) ∈ U} ∈ 𝓝 t := hnhds
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
