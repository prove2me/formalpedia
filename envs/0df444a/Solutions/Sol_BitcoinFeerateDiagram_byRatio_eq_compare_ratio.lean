-- Prove2me | solution 1 for BitcoinFeerateDiagram.byRatio_eq_compare_ratio
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T01:14:33.113738+00:00
-- url     : https://prove2.me/submissions/33715d50-efca-48cb-95d3-aa1f2a96fa73

import Definitions.Def_BitcoinFeerateDiagram

open BitcoinFeerateDiagram BitcoinReplacement

private theorem add_fee (a b : FeeFrac) : (a + b).fee = a.fee + b.fee := rfl

private theorem add_size (a b : FeeFrac) : (a + b).size = a.size + b.size := rfl

private theorem sub_fee (a b : FeeFrac) : (a - b).fee = a.fee - b.fee := rfl

private theorem sub_size (a b : FeeFrac) : (a - b).size = a.size - b.size := rfl

private theorem zero_fee : (0 : FeeFrac).fee = 0 := rfl

private theorem zero_size : (0 : FeeFrac).size = 0 := rfl

private theorem ff_ext {x y : FeeFrac} (h1 : x.fee = y.fee) (h2 : x.size = y.size) : x = y := by
  cases x; cases y; simp_all

private theorem add_sub_cancel_ff (c a : FeeFrac) : c + a - a = c :=
  ff_ext (by rw [sub_fee, add_fee]; ring) (by rw [sub_size, add_size]; ring)

/-- `ByRatio` cross-multiplication is the comparison of the exact rational feerates: for positive
sizes, `byRatioCmp a b = compare (a.fee / a.size) (b.fee / b.size)`. -/
theorem solution (a b : FeeFrac)
    (ha : 0 < a.size) (hb : 0 < b.size) :
    FeeFrac.byRatioCmp a b = compare a.ratio b.ratio := by
  have ha' : (0 : ℚ) < a.size := by exact_mod_cast ha
  have hb' : (0 : ℚ) < b.size := by exact_mod_cast hb
  unfold FeeFrac.byRatioCmp FeeFrac.mul FeeFrac.ratio
  rcases h : compare (a.fee * b.size) (b.fee * a.size) with _ | _ | _
  · rw [compare_lt_iff_lt] at h
    symm; rw [compare_lt_iff_lt, div_lt_div_iff₀ ha' hb']; exact_mod_cast h
  · rw [compare_eq_iff_eq] at h
    symm; rw [compare_eq_iff_eq, div_eq_div_iff ha'.ne' hb'.ne']; exact_mod_cast h
  · rw [compare_gt_iff_gt] at h
    symm; rw [compare_gt_iff_gt, div_lt_div_iff₀ hb' ha']; exact_mod_cast h
