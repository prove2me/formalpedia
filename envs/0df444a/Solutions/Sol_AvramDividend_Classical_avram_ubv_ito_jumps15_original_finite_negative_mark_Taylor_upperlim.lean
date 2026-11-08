-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps15_original_finite_negative_mark_Taylor_upperlim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:43:21.816513+00:00
-- url     : https://prove2.me/submissions/fada5a9d-0280-44d0-96d2-b8600350b667

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! A single original compact-cap mesh controls every mark in a finite negative set. -/
theorem solution
    (w : ℝ → ℝ) (cap : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcCap : ENNReal.ofReal c ≤ cap)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cap})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) c)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds y)) :
    let R : ℝ → ℝ → ℝ := fun a z =>
      w (a + z) - w a -
        (if -1 < z then z * deriv w a else 0)
    ∀ S : Finset ℝ, (∀ z ∈ S, z < 0) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        S.sum (fun z => R (u n) z) ≤ S.sum (fun z => R y z) + ε := by
  intro R S
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro hneg ε hε
      refine Filter.Eventually.of_forall ?_
      intro n
      simpa using le_of_lt hε
  | @insert z S hz ih =>
      intro hneg ε hε
      have hzneg : z < 0 := hneg z (Finset.mem_insert_self z S)
      have hSneg : ∀ t ∈ S, t < 0 := by
        intro t ht
        exact hneg t (Finset.mem_insert_of_mem ht)
      have hhalf : 0 < ε / 2 := by linarith
      have hhead :=
        avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
          w cap c hc hcCap hw_smooth hw0 hwcont hwneg
          y z hy hzneg u hu (ε / 2) hhalf
      have htail := ih hSneg (ε / 2) hhalf
      filter_upwards [hhead, htail] with n hnhead hntail
      change (insert z S).sum (fun t => R (u n) t) ≤
        (insert z S).sum (fun t => R y t) + ε
      simp only [Finset.sum_insert hz]
      change R (u n) z ≤ R y z + ε / 2 at hnhead
      linarith
