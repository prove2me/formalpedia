-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_finitecap_caplinear_j_envelope_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:21:06.672204+00:00
-- url     : https://prove2.me/submissions/32e920f7-3ed0-4880-a965-659f84d9b4af

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution (C : ℝ) (hC : 0 < C) (w : ℝ → ℝ)
    (hw : ContinuousOn w (Set.Ici 0)) :
    Tendsto (fun j : ℕ =>
      (w C - w (C * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))) -
        (C - C * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))))
      atTop (nhds (0 : ℝ)) := by
  have hRatio :
      Tendsto (fun j : ℕ => (((j + 1 : ℕ) : ℝ) /
        ((j + 2 : ℕ) : ℝ))) atTop (nhds (1 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      one_mul, add_comm, div_one] using
      (tendsto_add_mul_div_add_mul_atTop_nhds
        (1 : ℝ) (2 : ℝ) (1 : ℝ) (d := 1) one_ne_zero)
  have hB : Tendsto (fun j : ℕ =>
      C * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))
        atTop (nhds C) := by
    convert tendsto_const_nhds.mul hRatio using 1 <;> simp
  have hwAt : ContinuousAt w C := hw.continuousAt (Ici_mem_nhds hC)
  have hW : Tendsto (fun j : ℕ =>
      w (C * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))))
      atTop (nhds (w C)) := hwAt.tendsto.comp hB
  have hDiff : Tendsto (fun j : ℕ =>
      (w C - w (C * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)))) -
        (C - C * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))))
      atTop (nhds ((w C - w C) - (C - C))) := by
    exact (tendsto_const_nhds.sub hW).sub (tendsto_const_nhds.sub hB)
  simpa only [sub_self] using hDiff
