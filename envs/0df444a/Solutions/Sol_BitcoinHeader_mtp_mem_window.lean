-- Prove2me | solution 1 for BitcoinHeader.mtp_mem_window
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:10.570228+00:00
-- url     : https://prove2.me/submissions/5a0fc060-2e00-4064-9a41-1984a221151a

import Definitions.Def_BitcoinHeader

open BitcoinHeader

theorem solution (times : List Int) (h : times ≠ []) :
    BitcoinHeader.medianTimePast times ∈ BitcoinHeader.timeWindow times := by
  unfold medianTimePast
  simp only []
  generalize hw : timeWindow times = w
  have hwne : w ≠ [] := by
    intro hnil
    unfold timeWindow at hw
    rw [hnil] at hw
    have := congrArg List.length hw
    simp only [List.length_take, List.length_nil] at this
    have hpos : 0 < times.length := List.length_pos_iff.2 h
    unfold nMedianTimeSpan at this
    omega
  have hpos : 0 < w.length := List.length_pos_iff.2 hwne
  generalize hs : (w.mergeSort fun a b => decide (a ≤ b)) = s
  have hperm : s.Perm w := hs ▸ List.mergeSort_perm w _
  have hlen : s.length = w.length := hperm.length_eq
  have hk : w.length / 2 < s.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact hperm.mem_iff.1 (List.getElem_mem hk)
