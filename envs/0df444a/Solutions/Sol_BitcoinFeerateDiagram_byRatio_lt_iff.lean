-- Prove2me | solution 1 for BitcoinFeerateDiagram.byRatio_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T01:16:27.776464+00:00
-- url     : https://prove2.me/submissions/c1580dd6-c579-47c3-a015-8156e9fc3a34

import Definitions.Def_BitcoinFeerateDiagram
import Theorems.Thm_BitcoinFeerateDiagram_byRatio_eq_compare_ratio

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

/-- `ByRatio{a} < ByRatio{b}` iff the exact feerate of `a` is below that of `b`. -/
theorem solution (a b : FeeFrac) (ha : 0 < a.size) (hb : 0 < b.size) :
    FeeFrac.byRatioCmp a b = .lt ↔ a.ratio < b.ratio := by
  rw [BitcoinFeerateDiagram.byRatio_eq_compare_ratio a b ha hb, compare_lt_iff_lt]
