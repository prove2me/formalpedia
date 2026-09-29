-- Prove2me | solution 1 for Freiman.form_root_coordinate_algebra
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:08:48.360718+00:00
-- url     : https://prove2.me/submissions/66d2e199-d24c-49fd-871b-74ef580c24ad

import Definitions.Def_Freiman_reducedForms
import Definitions.Def_Freiman_rootConvergentData
import Mathlib.Tactic.FieldSimp

open Freiman

set_option autoImplicit false

theorem solution (r s : ℝ) (hs : Irrational s) (D : RootConvergentData r) (n : ℕ)
    (h : secondRootCoordinate D s n ∈ Set.Ioo (-1 : ℝ) 0) :
    ∃ a b c d : ℤ, ∃ α β : ℝ, formUnimodular a b c d ∧
      1 < α ∧ 0 < β ∧ β < 1 ∧ Irrational α ∧ Irrational β ∧
      (c : ℝ) * α + (d : ℝ) ≠ 0 ∧ -(c : ℝ) * β + (d : ℝ) ≠ 0 ∧
      r = ((a : ℝ) * α + (b : ℝ)) / ((c : ℝ) * α + (d : ℝ)) ∧
      s = (-(a : ℝ) * β + (b : ℝ)) / (-(c : ℝ) * β + (d : ℝ)) := by
  let x : ℝ := secondRootCoordinate D s n
  have hq : (0 : ℝ) < D.q (n + 1) := by exact_mod_cast D.q_pos (n + 1)
  have hq' : (0 : ℝ) < D.q n := by exact_mod_cast D.q_pos n
  have hsrat : s ≠ (D.p (n + 1) : ℝ) / (D.q (n + 1) : ℝ) := by
    simpa only [Int.cast_natCast] using hs.ne_rational (D.p (n + 1)) (D.q (n + 1))
  have hd : s * (D.q (n + 1) : ℝ) - D.p (n + 1) ≠ 0 := by
    intro hz
    apply hsrat
    apply (eq_div_iff (ne_of_gt hq)).2
    linarith
  have hmul : x * (s * (D.q (n + 1) : ℝ) - D.p (n + 1)) =
      (D.p n : ℝ) - s * (D.q n : ℝ) := by
    exact div_mul_cancel₀ _ hd
  have hdet : (D.p (n + 1) : ℝ) * (D.q n : ℝ) -
      (D.p n : ℝ) * (D.q (n + 1) : ℝ) ≠ 0 := by
    rcases D.det n with hdet | hdet
    · have hh : (D.p (n + 1) : ℝ) * (D.q n : ℝ) -
          (D.p n : ℝ) * (D.q (n + 1) : ℝ) = 1 := by exact_mod_cast hdet
      linarith
    · have hh : (D.p (n + 1) : ℝ) * (D.q n : ℝ) -
          (D.p n : ℝ) * (D.q (n + 1) : ℝ) = -1 := by exact_mod_cast hdet
      linarith
  have hcross : ((D.q (n + 1) : ℝ) * x + D.q n) *
      (s * (D.q (n + 1) : ℝ) - D.p (n + 1)) =
      (D.q (n + 1) : ℝ) * D.p n - (D.p (n + 1) : ℝ) * D.q n := by
    calc
      _ = (D.q (n + 1) : ℝ) *
          (x * (s * (D.q (n + 1) : ℝ) - D.p (n + 1))) +
          (D.q n : ℝ) * (s * (D.q (n + 1) : ℝ) - D.p (n + 1)) := by ring
      _ = _ := by rw [hmul]; ring
  have hden : (D.q (n + 1) : ℝ) * x + D.q n ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hcross
    apply hdet
    nlinarith
  have hsId : s = ((D.p (n + 1) : ℝ) * x + D.p n) /
      ((D.q (n + 1) : ℝ) * x + D.q n) := by
    apply (eq_div_iff hden).2
    nlinarith [hmul]
  have hxirr : Irrational x := by
    rintro ⟨u, hu⟩
    apply hs
    refine ⟨(((D.p (n + 1) : ℚ) * u + D.p n) /
      ((D.q (n + 1) : ℚ) * u + D.q n)), ?_⟩
    push_cast
    rw [hu]
    exact hsId.symm
  have hx0 : x < 0 := h.2
  have hx1 : -1 < x := h.1
  refine ⟨D.p (n + 1), D.p n, D.q (n + 1), D.q n,
    D.complete n, -x, D.det n, D.complete_gt n, by linarith, by linarith,
    D.complete_irr n, hxirr.neg, ?_, ?_, ?_, ?_⟩
  · simp only [Int.cast_natCast]
    have hc : 0 < D.complete n := lt_trans (by norm_num) (D.complete_gt n)
    exact ne_of_gt (add_pos (mul_pos hq hc) hq')
  · simpa only [Int.cast_natCast, neg_mul_neg] using hden
  · simpa only [Int.cast_natCast] using D.root_identity n
  · simpa only [Int.cast_natCast, neg_mul_neg] using hsId
