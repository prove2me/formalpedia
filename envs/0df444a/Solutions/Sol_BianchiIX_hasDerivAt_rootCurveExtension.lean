-- Prove2me | solution 1 for BianchiIX.hasDerivAt_rootCurveExtension
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:42:15.635223+00:00
-- url     : https://prove2.me/submissions/96bc6f87-6035-42b0-8512-6edb91cc527f

import Definitions.Def_BianchiIX_Analysis_RootCurveExtension
import Theorems.Thm_BianchiIX_hasDerivAt_rootExtension
import Theorems.Thm_BianchiIX_rootCurveExtension_left
import Theorems.Thm_BianchiIX_rootCurveExtension_middle
import Theorems.Thm_BianchiIX_rootCurveExtension_right
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology
open BianchiIX
noncomputable section

private theorem BianchiIX.hasDerivAt_rootExtension_shift {s e : ℝ} (hs : 0 < s) (he : |e| = 1)
    (d c x : ℝ) : HasDerivAt (fun z => rootExtension s d e (z - c))
      (d * rootCutoff (e * (x - c) / s)) x := by
  simpa only [Function.comp_def, id_eq, mul_one] using
    (hasDerivAt_rootExtension hs he d (x - c)).comp x ((hasDerivAt_id x).sub_const c)

theorem solution {l r : ℝ} (hlr : l < r) {f df : ℝ → ℝ}
    (hfl : 0 < f l) (hfr : 0 < f r)
    (hf : ∀ x ∈ Icc l r, HasDerivWithinAt f (df x) (Icc l r) x) (x : ℝ) :
    HasDerivAt (rootCurveExtension l r f df) (rootCurveDerivative l r f df x) x := by
  have hL (z : ℝ) : HasDerivAt (fun u => rootExtension (f l) (df l) (-1) (u - l))
      (df l * rootCutoff (-(z - l) / f l)) z := by
    simpa only [neg_mul, one_mul] using
      hasDerivAt_rootExtension_shift (e := -1) hfl (by norm_num) (df l) l z
  have hR (z : ℝ) : HasDerivAt (fun u => rootExtension (f r) (df r) 1 (u - r))
      (df r * rootCutoff ((z - r) / f r)) z := by
    simpa only [one_mul] using hasDerivAt_rootExtension_shift (e := 1) hfr (by norm_num) (df r) r z
  by_cases hxl : x < l
  · rw [(rootCurveExtension_left f df hlr.le hxl.le).2]
    apply (hL x).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hxl] with z hz
    exact (rootCurveExtension_left f df hlr.le hz.le).1
  by_cases hrx : r < x
  · rw [(rootCurveExtension_right f df hlr.le hrx.le).2]
    apply (hR x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hrx] with z hz
    exact (rootCurveExtension_right f df hlr.le hz.le).1
  have hx : x ∈ Icc l r := ⟨le_of_not_gt hxl, le_of_not_gt hrx⟩
  rw [(rootCurveExtension_middle f df hx).2]
  have hM := (hf x hx).congr_of_mem (fun z hz => (rootCurveExtension_middle f df hz).1) hx
  rcases hx.1.eq_or_lt with h | hleft
  · subst x
    have htail : HasDerivWithinAt (rootCurveExtension l r f df) (df l) (Iic l) l := by
      have h := hL l
      norm_num [rootCutoff] at h
      exact h.hasDerivWithinAt.congr_of_mem
        (fun z hz => (rootCurveExtension_left f df hlr.le hz).1) self_mem_Iic
    have hu : Iic l ∪ Icc l r = Iic r := by
      ext z
      simp only [mem_union, mem_Iic, mem_Icc]
      constructor
      · rintro (h | h)
        · exact h.trans hlr.le
        · exact h.2
      · intro h
        exact (le_total z l).elim Or.inl (fun hz => Or.inr ⟨hz, h⟩)
    have h := htail.union hM
    rw [hu] at h
    exact h.hasDerivAt (Iic_mem_nhds hlr)
  rcases hx.2.eq_or_lt with h | hright
  · subst x
    have htail : HasDerivWithinAt (rootCurveExtension l r f df) (df r) (Ici r) r := by
      have h := hR r
      norm_num [rootCutoff] at h
      exact h.hasDerivWithinAt.congr_of_mem
        (fun z hz => (rootCurveExtension_right f df hlr.le hz).1) self_mem_Ici
    have hu : Icc l r ∪ Ici r = Ici l := by
      ext z
      simp only [mem_union, mem_Icc, mem_Ici]
      constructor
      · rintro (h | h)
        · exact h.1
        · exact hlr.le.trans h
      · intro h
        exact (le_total z r).elim (fun hz => Or.inl ⟨h, hz⟩) Or.inr
    have h := hM.union htail
    rw [hu] at h
    exact h.hasDerivAt (Ici_mem_nhds hlr)
  exact hM.hasDerivAt (Icc_mem_nhds hleft hright)
