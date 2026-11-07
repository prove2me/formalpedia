-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:58:20.645349+00:00
-- url     : https://prove2.me/submissions/75727b89-b0c1-4dd7-9392-4944b7f0ae87

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

/-- A finite-cap slope-one secant defect vanishes at the cap by continuity;
no cap derivative (let alone smooth fit) is needed. -/
theorem solution
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (b : ℕ → ℝ) (hb : Tendsto b atTop (𝓝 c)) :
    Tendsto (fun n => (w c - w (b n)) - (c - b n))
      atTop (𝓝 (0 : ℝ)) := by
  have hs : Ici (0 : ℝ) ∈ 𝓝 c := by
    apply Filter.mem_of_superset (Ioi_mem_nhds hc)
    intro z hz
    change (0 : ℝ) < z at hz
    exact le_of_lt hz
  have hwAt : ContinuousAt w c := hw_cont.continuousAt hs
  have hwb : Tendsto (fun n => w (b n)) atTop (𝓝 (w c)) :=
    hwAt.tendsto.comp hb
  have h₁ : Tendsto (fun n => w c - w (b n))
      atTop (𝓝 (w c - w c)) :=
    tendsto_const_nhds.sub hwb
  have h₂ : Tendsto (fun n => c - b n)
      atTop (𝓝 (c - c)) :=
    tendsto_const_nhds.sub hb
  simpa only [sub_self, sub_zero] using h₁.sub h₂
