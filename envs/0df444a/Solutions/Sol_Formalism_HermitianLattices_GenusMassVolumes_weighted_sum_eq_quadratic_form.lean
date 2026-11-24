-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.weighted_sum_eq_quadratic_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:58.268156+00:00
-- url     : https://prove2.me/submissions/f1d5a2da-374d-4e52-be61-ee1f5e6a1394

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightShiftProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
private lemma sum_ico_telescoping_plus_one (L : ℕ → ℝ) (b a : ℕ) (h : b ≤ a) :
    ∑ i ∈ Ico b a, (L i - L (i + 1) + 1) = L b - L a + ((a : ℝ) - b) := by
  induction a, h using Nat.le_induction with
  | base => simp
  | succ a h ih =>
    rw [Finset.sum_Ico_succ_top h, ih]
    push_cast
    ring
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : WeightedSumEqQuadraticForm := by
  intro N lam sg X hX P V
  have hent : ∀ (i : ℕ) (a b : Fin N), ((1 - P i) * X * P i) a b =
      if i ≤ a.val ∧ b.val < i then X a b else 0 := by
    intro i a b
    have h1 : (1 - P i) = Matrix.diagonal (fun a : Fin N => if a.val < i then (0 : ℂ) else 1) := by
      ext c d
      by_cases hcd : c = d
      · subst hcd
        by_cases hc : c.val < i <;> simp [P, hc]
      · simp [P, hcd]
    rw [h1]
    simp only [P]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases ha : a.val < i <;> by_cases hb : b.val < i <;> simp [ha, hb, not_le.mpr, not_lt.mp]
  have hV : ∀ i, V i = ∑ a, ∑ b, if i ≤ a.val ∧ b.val < i then ‖X a b‖ ^ 2 else 0 := by
    intro i
    simp only [V]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hent]
    split_ifs <;> simp
  set L : ℕ → ℝ := fun n => if h : n < N then lam ⟨n, h⟩ else 0 with hL
  have hLv : ∀ a : Fin N, L a.val = lam a := fun a => by simp [hL]
  have hterm : ∀ i : Fin N,
      (if h : i.val + 1 < N then (lam i - lam ⟨i.val + 1, h⟩ + 1) * V (i.val + 1) else 0) =
      ∑ a : Fin N, ∑ b : Fin N, (if i.val ∈ Ico b.val a.val then (L i.val - L (i.val + 1) + 1) else 0)
        * ‖X a b‖ ^ 2 := by
    intro i
    split_ifs with h
    · rw [hV, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have e1 : L (i.val + 1) = lam ⟨i.val + 1, h⟩ := by simp [hL, h]
      rw [hLv, e1]
      by_cases hc : i.val + 1 ≤ a.val ∧ b.val < i.val + 1
      · have : i.val ∈ Ico b.val a.val := by rw [mem_Ico]; omega
        rw [if_pos hc, if_pos this]
      · have : i.val ∉ Ico b.val a.val := by rw [mem_Ico]; omega
        rw [if_neg hc, if_neg this]; ring
    · symm
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      have : i.val ∉ Ico b.val a.val := by
        rw [mem_Ico]; have := a.isLt; omega
      rw [if_neg this, zero_mul]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ i : Fin N, (if i.val ∈ Ico b.val a.val then (L i.val - L (i.val + 1) + 1) else 0) =
      ∑ i ∈ Ico b.val a.val, (L i - L (i + 1) + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i ∈ Ico b.val a.val then (L i - L (i + 1) + 1) else 0) N,
      ← Finset.sum_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    have := a.isLt
    omega
  rw [hsum]
  by_cases hba : b < a
  · rw [sum_ico_telescoping_plus_one L _ _ (Fin.le_def.mp hba.le), hLv, hLv]
    by_cases hs : sg a = sg b
    · rw [hX a b hs]; simp [hs]
    · rw [if_pos ⟨hba, hs⟩]
  · have : Ico b.val a.val = ∅ := Finset.Ico_eq_empty (fun h => hba (Fin.lt_def.mpr h))
    rw [this, if_neg (fun h => hba h.1)]
    simp
end Formalism.HermitianLattices.GenusMassVolumes
