-- Prove2me | solution 1 for CompOT.Metric.prop_2_2_offdiag_mass
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:20:23.578769+00:00
-- url     : https://prove2.me/submissions/c0ab709c-9a81-4400-897a-5a1122f10bfd

import Mathlib
import Definitions.Def_CompOT_Metric_Defs

set_option autoImplicit false
open Matrix CompOT.Metric

theorem solution {n : ℕ} (a b : Fin n → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin n)) (hab : a ≠ b)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P ∈ CompOT.Assignment.couplings a b) :
    ∃ i j, i ≠ j ∧ P i j ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply hab
  funext i
  obtain ⟨_, hr, hc⟩ := hP
  have h1 : a i = P i i := by
    rw [← hr i]
    exact Finset.sum_eq_single i (fun j _ hj => hcon i j (Ne.symm hj)) (by simp)
  have h2 : b i = P i i := by
    rw [← hc i]
    exact Finset.sum_eq_single i (fun j _ hj => hcon j i hj) (by simp)
  exact h1.trans h2.symm
