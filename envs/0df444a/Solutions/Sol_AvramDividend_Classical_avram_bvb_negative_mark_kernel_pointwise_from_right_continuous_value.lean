-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_negative_mark_kernel_pointwise_from_right_continuous_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:51:07.594246+00:00
-- url     : https://prove2.me/submissions/230cd11e-3fda-4ed3-b1af-c4f12d213cf9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped Topology
theorem solution
    (w : ℝ → ℝ) (y : ℕ → ℝ)
    (hy : Tendsto y atTop (𝓝 (0 : ℝ)))
    (hyPos : ∀ n, 0 ≤ y n)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ z : ℝ, z < 0 → w z = 0)
    (z : ℝ) (hz : z < 0) :
    Tendsto (fun n => w (y n + z) - w (y n))
      atTop (𝓝 (w z - w 0)) := by
  have hyWithin : Tendsto y atTop (𝓝[ Ici (0 : ℝ)] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hy, Filter.Eventually.of_forall (fun n => hyPos n)⟩
  have hwY : Tendsto (fun n => w (y n)) atTop (𝓝 (w 0)) :=
    (hwCont.continuousWithinAt (by simp)).tendsto.comp hyWithin
  have hyShift : Tendsto (fun n => y n + z) atTop (𝓝 z) := by
    simpa using hy.add tendsto_const_nhds
  have hNegEventually : ∀ᶠ n in atTop, y n + z < 0 :=
    hyShift.eventually (eventually_lt_nhds hz)
  have hZeroEventually : (fun n => w (y n + z)) =ᶠ[atTop]
      (fun _ => (0 : ℝ)) :=
    hNegEventually.mono (fun n hn => hwNeg _ hn)
  have hwShift : Tendsto (fun n => w (y n + z)) atTop (𝓝 (w z)) := by
    rw [hwNeg z hz]
    exact tendsto_const_nhds.congr' hZeroEventually.symm
  exact hwShift.sub hwY
