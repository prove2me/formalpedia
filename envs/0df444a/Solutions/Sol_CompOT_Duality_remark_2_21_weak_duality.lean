-- Prove2me | solution 1 for CompOT.Duality.remark_2_21_weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:12:34.906694+00:00
-- url     : https://prove2.me/submissions/111afc31-0684-4e3a-9124-b861be02d569

import Mathlib
import Definitions.Def_CompOT_Duality_Defs
set_option autoImplicit false
open CompOT.Duality

theorem solution {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (C P : Matrix (Fin n) (Fin m) ℝ) (hP : P ∈ CompOT.Assignment.couplings a b)
    (f : Fin n → ℝ) (g : Fin m → ℝ) (hfg : dualFeasible C f g) :
    ∑ i, ∑ j, P i j * (f i + g j) ≤ ∑ i, ∑ j, P i j * C i j ∧
      ∑ i, ∑ j, P i j * (f i + g j) = (∑ i, f i * ∑ j, P i j) + (∑ j, g j * ∑ i, P i j) ∧
      (∑ i, f i * ∑ j, P i j) + (∑ j, g j * ∑ i, P i j) = dualObj a b f g := by
  obtain ⟨hP0, hrow, hcol⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_left (hfg i j) (hP0 i j)
  · simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  · unfold dualObj
    simp only [hrow, hcol]

