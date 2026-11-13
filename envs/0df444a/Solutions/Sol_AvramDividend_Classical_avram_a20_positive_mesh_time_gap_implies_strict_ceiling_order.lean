-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_positive_mesh_time_gap_implies_strict_ceiling_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:29:04.196104+00:00
-- url     : https://prove2.me/submissions/420aaa2c-3a73-4f28-807d-379e9a1eb006

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section

theorem solution
    (u v T : ℝ≥0) (hT : 0 < T) (k : ℕ)
    (hGap : (T : ℝ) < (k : ℝ) * ((v : ℝ) - (u : ℝ))) :
    Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) <
      Nat.ceil ((v : ℝ) * (k : ℝ) / (T : ℝ)) := by
  have hTreal : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hmid : (u : ℝ) * (k : ℝ) + (T : ℝ) <
      (v : ℝ) * (k : ℝ) := by nlinarith
  have hdiv : ((u : ℝ) * (k : ℝ) + (T : ℝ)) / (T : ℝ) <
      ((v : ℝ) * (k : ℝ)) / (T : ℝ) :=
    div_lt_div_of_pos_right hmid hTreal
  have hscaled : ((u : ℝ) * (k : ℝ)) / (T : ℝ) + 1 <
      ((v : ℝ) * (k : ℝ)) / (T : ℝ) := by
    convert hdiv using 1 <;> field_simp <;> ring
  have ha : (0 : ℝ) ≤ ((u : ℝ) * (k : ℝ)) / (T : ℝ) := by positivity
  have huceil : ((Nat.ceil (((u : ℝ) * (k : ℝ)) / (T : ℝ))) : ℝ) <
      ((u : ℝ) * (k : ℝ)) / (T : ℝ) + 1 :=
    Nat.ceil_lt_add_one ha
  have hvceil : ((v : ℝ) * (k : ℝ)) / (T : ℝ) ≤
      ((Nat.ceil (((v : ℝ) * (k : ℝ)) / (T : ℝ))) : ℝ) :=
    Nat.le_ceil _
  exact_mod_cast lt_trans huceil (lt_of_lt_of_le hscaled hvceil)
