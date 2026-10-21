-- Prove2me | solution 1 for FlexGroupBuy.REE.Nbar_order
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:09:15.960026+00:00
-- url     : https://prove2.me/submissions/e176fca1-2c78-4f54-ae81-bbc62a891b39

import Mathlib
import Definitions.Def_FlexGroupBuy_REE_Model

open FlexGroupBuy.REE

theorem solution (P : Params) (hP : P.Standing) :
    Nbar1 P < Nbar2 P ↔ 1 / P.gam < P.H / P.L := by
  obtain ⟨hL, hLH, hg0, hg1, hl, hc, ht⟩ := hP
  have key : Nbar2 P - Nbar1 P = (P.theta - 1) * P.lam * (P.gam * P.H - P.L) / P.c := by
    unfold Nbar1 Nbar2; field_simp; ring
  rw [div_lt_div_iff₀ hg0 hL, one_mul, ← sub_pos, key]
  have hA : 0 < (P.theta - 1) * P.lam := mul_pos (by linarith) hl
  constructor
  · intro h
    have h2 : 0 < (P.theta - 1) * P.lam * (P.gam * P.H - P.L) := by
      have := (div_pos_iff_of_pos_right hc).mp h; exact this
    have := (mul_pos_iff_of_pos_left hA).mp h2
    linarith
  · intro h
    apply div_pos _ hc
    exact mul_pos hA (by linarith)
