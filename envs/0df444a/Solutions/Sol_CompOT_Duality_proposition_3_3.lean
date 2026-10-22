-- Prove2me | solution 1 for CompOT.Duality.proposition_3_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:10:07.30271+00:00
-- url     : https://prove2.me/submissions/2f56003a-c770-47cb-b7b7-a5fc64d93cdc

import Mathlib
import Definitions.Def_CompOT_Duality_Defs

namespace CompOT.Duality.Sol33

open CompOT.Assignment CompOT.Duality

lemma dualObj_eq_sum {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) (Q : Matrix (Fin n) (Fin m) ℝ)
    (hQ : Q ∈ couplings a b) (f : Fin n → ℝ) (g : Fin m → ℝ) :
    dualObj a b f g = ∑ i, ∑ j, (f i + g j) * Q i j := by
  obtain ⟨-, hr, hc⟩ := hQ
  unfold dualObj
  have h1 : ∑ i, f i * a i = ∑ i, ∑ j, f i * Q i j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hr i, Finset.mul_sum]
  have h2 : ∑ j, g j * b j = ∑ i, ∑ j, g j * Q i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hc j, Finset.mul_sum]
  rw [h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma weak_duality {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (Q : Matrix (Fin n) (Fin m) ℝ) (hQ : Q ∈ couplings a b) (f : Fin n → ℝ) (g : Fin m → ℝ)
    (hfg : dualFeasible C f g) : dualObj a b f g ≤ frob C Q := by
  rw [dualObj_eq_sum a b Q hQ]
  unfold frob
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  exact mul_le_mul_of_nonneg_right (hfg i j) (hQ.1 i j)

lemma frob_eq_dualObj {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) (hP : P ∈ couplings a b) (f : Fin n → ℝ) (g : Fin m → ℝ)
    (hcomp : Complementary C P f g) : frob C P = dualObj a b f g := by
  rw [dualObj_eq_sum a b P hP]
  unfold frob
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rcases (hP.1 i j).eq_or_lt with h | h
  · rw [← h]; ring
  · rw [hcomp i j h]

end CompOT.Duality.Sol33

theorem solution {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (C P : Matrix (Fin n) (Fin m) ℝ) (hP : P ∈ CompOT.Assignment.couplings a b)
    (f : Fin n → ℝ) (g : Fin m → ℝ) (hfg : CompOT.Duality.dualFeasible C f g)
    (hcomp : CompOT.Duality.Complementary C P f g) :
    CompOT.Assignment.IsOptimalCoupling C a b P ∧ CompOT.Duality.IsDualOptimal C a b f g := by
  have heq := CompOT.Duality.Sol33.frob_eq_dualObj C a b P hP f g hcomp
  refine ⟨⟨hP, fun Q hQ => ?_⟩, ⟨hfg, fun f' g' hf' => ?_⟩⟩
  · rw [heq]; exact CompOT.Duality.Sol33.weak_duality C a b Q hQ f g hfg
  · rw [← heq]; exact CompOT.Duality.Sol33.weak_duality C a b P hP f' g' hf'
