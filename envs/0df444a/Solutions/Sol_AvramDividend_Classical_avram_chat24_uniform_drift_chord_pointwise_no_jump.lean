-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_uniform_drift_chord_pointwise_no_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:49:10.12352+00:00
-- url     : https://prove2.me/submissions/d67eeaf6-783e-4fb0-9930-275ed75c7b2f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_cell_path_increment_limits
import Theorems.Thm_AvramDividend_Classical_avram_chat24_C1_moving_drift_chord_limit
import Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_mesh_cell_geometry
import Theorems.Thm_AvramDividend_Classical_avram_chat24_strict_mono_cell_selector
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    (f P Y : ℝ≥0 → ℝ) (d a b q : ℝ) (ha : 0 < a)
    (B : ℝ≥0) (hB : 0 < B)
    (hf_right : ∀ t, ContinuousWithinAt f (Ici t) t)
    (hf_left : ∀ t : ℝ≥0, 0 < t → ∃ l, Tendsto f (𝓝[<] t) (nhds l))
    (hpre : ∀ t : ℝ≥0, 0 < t → t ≤ B →
      Y t ∈ Icc a b ∧ Tendsto P (𝓝[<] t) (nhds (Y t)))
    (w : ℝ → ℝ) (hw : ContDiffOn ℝ 1 w (Ioi 0))
    (n0 : ℕ) (t : ℝ≥0) (ht : 0 < t)
    (hzero : (if 0 < t ∧ t ≤ B then Function.leftLim f t - f t else 0) = 0) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let h : ℕ → ℝ := fun n => (B : ℝ) / ((n + 1 : ℕ) : ℝ)
    let m : ℕ → ℕ → ℝ := fun n i =>
      d * h n - (f (u n (i + 1)) - f (u n i))
    let G : ℕ → ℝ≥0 → ℝ := fun n t => if n0 ≤ n then
      ∑ i ∈ Finset.range (n + 1),
        if u n i < t ∧ t ≤ u n (i + 1) then
          Real.exp (-(q * (u n (i + 1) : ℝ))) *
            ((w (P (u n i) + d * h n - m n i) - w (P (u n i) - m n i)) / h n)
        else 0
      else 0
    let A : ℝ≥0 → ℝ := fun t =>
      if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y t ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) * (d * deriv w (Y t)) else 0
    Tendsto (fun n => G n t) atTop (nhds (A t)) := by
  classical
  let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
  let h : ℕ → ℝ := fun n => (B : ℝ) / ((n + 1 : ℕ) : ℝ)
  let m : ℕ → ℕ → ℝ := fun n i => d * h n - (f (u n (i + 1)) - f (u n i))
  let C : ℕ → ℕ → ℝ := fun n i =>
    Real.exp (-(q * (u n (i + 1) : ℝ))) *
      ((w (P (u n i) + d * h n - m n i) - w (P (u n i) - m n i)) / h n)
  let G : ℕ → ℝ := fun n => if n0 ≤ n then
    ∑ i ∈ Finset.range (n + 1), if u n i < t ∧ t ≤ u n (i + 1) then C n i else 0
    else 0
  change Tendsto G atTop (nhds (if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y t ∈ Icc a b
    then Real.exp (-(q * (t : ℝ))) * (d * deriv w (Y t)) else 0))
  have hgeo := AvramDividend.Classical.avram_chat24_uniform_mesh_cell_geometry B hB
  by_cases htB : t ≤ B
  · have hend (n : ℕ) : u n (n + 1) = B := by
      dsimp only [u]
      exact mul_div_cancel_right₀ _ (by positivity)
    have hs (n : ℕ) :=
      AvramDividend.Classical.avram_chat24_strict_mono_cell_selector
        (u n) (hgeo.1 n) (n + 1) t
        (by simpa only [u, Nat.cast_zero, mul_zero, zero_div] using ht)
        (by simpa only [hend] using htB)
    choose k hk using hs
    have hkr (n : ℕ) : k n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (hk n).1
    have hcell (n : ℕ) : u n (k n) < t ∧ t ≤ u n (k n + 1) :=
      ⟨(hk n).2.1, (hk n).2.2.1⟩
    have hp := AvramDividend.Classical.avram_chat24_uniform_cell_path_increment_limits
      f P d (Y t) B t hB ht k hkr hcell (hf_right t) (hf_left t ht) (hpre t ht htB).2
    have hj : Function.leftLim f t - f t = 0 := by
      simpa only [if_pos (show 0 < t ∧ t ≤ B from ⟨ht, htB⟩)] using hzero
    have hm : Tendsto (fun n => m n (k n)) atTop (nhds 0) := by
      simpa only [hj] using hp.2.2.2
    have hy := (hpre t ht htB).1
    have hwAt : ContDiffAt ℝ 1 w (Y t) :=
      ContDiffOn.contDiffAt hw (Ioi_mem_nhds (lt_of_lt_of_le ha hy.1))
    have hquot := AvramDividend.Classical.avram_chat24_C1_moving_drift_chord_limit
      w (Y t) d (fun n => P (u n (k n))) (fun n => m n (k n)) h
      hwAt hp.2.2.1 hm hp.2.1 (fun n => (hgeo.2.1 n).ne')
    have hupp : Tendsto (fun n => (u n (k n + 1) : ℝ)) atTop (nhds (t : ℝ)) :=
      continuous_subtype_val.continuousAt.tendsto.comp (hp.1.mono_right nhdsWithin_le_nhds)
    have hexp := Real.continuous_exp.continuousAt.tendsto.comp (hupp.const_mul q).neg
    have heq : G =ᶠ[atTop] (fun n => C n (k n)) := by
      filter_upwards [eventually_ge_atTop n0] with n hn
      dsimp only [G]
      rw [if_pos hn, Finset.sum_eq_single (k n)]
      · rw [if_pos (hcell n)]
      · intro j hj hjne
        exact if_neg (fun hc => hjne ((hk n).2.2.2 j hc.1 hc.2))
      · intro hnot
        exact (hnot (hkr n)).elim
    rw [if_pos (show (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y t ∈ Icc a b from
      ⟨by exact_mod_cast htB, hy⟩)]
    exact (tendsto_congr' heq).2 (hexp.mul hquot)
  · have hG : G = fun _ => 0 := by
      funext n
      dsimp only [G]
      split_ifs with hn
      · apply Finset.sum_eq_zero
        intro i hi
        exact if_neg (fun hc => htB (hc.2.trans (hgeo.2.2 n i hi).2.1))
      · rfl
    have hnot : ¬ ((t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y t ∈ Icc a b) := by
      intro hc
      apply htB
      exact_mod_cast hc.1
    rw [if_neg hnot, hG]
    exact tendsto_const_nhds
