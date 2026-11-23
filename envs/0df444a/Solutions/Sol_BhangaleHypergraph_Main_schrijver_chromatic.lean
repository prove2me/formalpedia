-- Prove2me | solution 1 for BhangaleHypergraph.Main.schrijver_chromatic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T08:32:37.250736+00:00
-- url     : https://prove2.me/submissions/1967c56c-d4d7-483c-98da-7e703d8d3cc9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BhangaleHypergraph_Main_schrijver_colorable_upper
import Theorems.Thm_BhangaleHypergraph_Main_schrijver_chromatic_lower

open BhangaleHypergraph.Main

theorem solution (m h : ℕ) (hh : 1 ≤ h) (hm : 2 * h ≤ m) :
    (Schrijver m h).chromaticNumber = ↑(m - 2 * h + 2) := by
  apply le_antisymm
  · exact (schrijver_colorable_upper m h hh hm).chromaticNumber_le
  · exact schrijver_chromatic_lower m h hh hm
