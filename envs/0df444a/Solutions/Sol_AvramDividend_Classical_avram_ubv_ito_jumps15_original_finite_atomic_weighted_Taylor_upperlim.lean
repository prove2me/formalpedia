-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps15_original_finite_atomic_weighted_Taylor_upperlim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:48:35.557689+00:00
-- url     : https://prove2.me/submissions/2016d431-e974-458c-8442-2a3e4cd65c27

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original negative-mark Taylor upper limit is stable under any finite
nonnegative intensity measure, including positive atoms at ruin contact. -/
theorem solution
    (w : ℝ → ℝ) (cap : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcCap : ENNReal.ofReal c ≤ cap)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cap})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) c)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (nhds y))
    (a : ℝ → ℝ) (ha : ∀ z : ℝ, 0 ≤ a z) :
    let R : ℝ → ℝ → ℝ := fun x z =>
      w (x + z) - w x -
        (if -1 < z then z * deriv w x else 0)
    ∀ S : Finset ℝ, (∀ z ∈ S, z < 0) →
      ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
        S.sum (fun z => a z * R (u n) z) ≤
          S.sum (fun z => a z * R y z) + δ * S.sum a := by
  intro R S
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro hneg δ hδ
      exact Filter.Eventually.of_forall (fun n => by simp)
  | @insert z S hz ih =>
      intro hneg δ hδ
      have hzneg : z < 0 := hneg z (Finset.mem_insert_self z S)
      have hSneg : ∀ t ∈ S, t < 0 := by
        intro t ht
        exact hneg t (Finset.mem_insert_of_mem ht)
      have hhead :=
        avram_ubv_ito_jumps14_original_capped_C2_fixed_negative_mark_upperlim
          w cap c hc hcCap hw_smooth hw0 hwcont hwneg
          y z hy hzneg u hu δ hδ
      have htail := ih hSneg δ hδ
      filter_upwards [hhead, htail] with n hnhead hntail
      change R (u n) z ≤ R y z + δ at hnhead
      change S.sum (fun t => a t * R (u n) t) ≤
        S.sum (fun t => a t * R y t) + δ * S.sum a at hntail
      have hwhead := mul_le_mul_of_nonneg_left hnhead (ha z)
      change (insert z S).sum (fun t => a t * R (u n) t) ≤
        (insert z S).sum (fun t => a t * R y t) + δ * (insert z S).sum a
      simp only [Finset.sum_insert hz]
      nlinarith
