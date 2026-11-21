-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_true_all_right_payment_atoms_signed_tsum_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:38:08.476126+00:00
-- url     : https://prove2.me/submissions/6fdba576-912a-4e4a-a634-490ef1574415

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib
open MeasureTheory Filter
noncomputable section
theorem solution
    {ι : Type*} (V : ℝ → ℝ) (Y J E : ι → ℝ)
    (hSec : ∀ a b : ℝ, a ≤ b → b - a ≤ V b - V a)
    (hJ : ∀ i, 0 ≤ J i) (hE : ∀ i, 0 ≤ E i)
    (hSummable : Summable
      (fun i => E i * (V (Y i - J i) - V (Y i) + J i))) :
    (∑' i, E i * (V (Y i - J i) - V (Y i) + J i)) ≤ 0  := by
  have hbound (i : ι) :
      E i * (V (Y i - J i) - V (Y i) + J i) ≤ 0 := by
    have h := hSec (Y i - J i) (Y i) (by linarith [hJ i])
    have hg : V (Y i - J i) - V (Y i) + J i ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos (hE i) hg
  exact tsum_nonpos hbound
