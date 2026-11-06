-- Prove2me | solution 1 for BianchiIX.finite_gauss_branch_loss
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:28:16.471131+00:00
-- url     : https://prove2.me/submissions/f2e8752e-adcf-4116-a206-ccd9857f1fd9

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_EraReturnData
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

section
noncomputable section
open BianchiIX
open Finset

private theorem BianchiIX.gaussInv_lipschitz_weighted {n x y : ℝ} (hn : 0 < n) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussInv n x - gaussInv n y| ≤ |x - y| / n ^ 2 := by
  have hnx : 0 < n + x := by linarith
  have hny : 0 < n + y := by linarith
  have hden : n ^ 2 ≤ (n + x) * (n + y) := by nlinarith [mul_nonneg hx hy]
  have hid : gaussInv n x - gaussInv n y = (y - x) / ((n + x) * (n + y)) := by
    unfold gaussInv
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hnx hny), abs_sub_comm y x]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hn) hden

end
end

section
noncomputable section
open BianchiIX
open Finset

private theorem BianchiIX.gauss_branch_length_of_endpoint_error {n β E L R : ℝ}
    (hn : 0 < n) (hβ : 0 ≤ β) (hβmax : β ≤ 1 / 2)
    (hL : |L - gaussInv n (2 * β)| ≤ E / n ^ 2)
    (hR : |R - gaussInv n (1 - 2 * β)| ≤ E / n ^ 2) :
    1 / n - 1 / (n + 1) - (4 * β + 2 * E) / n ^ 2 ≤ L - R := by
  have hleft := gaussInv_lipschitz_weighted hn (by positivity : 0 ≤ 2 * β) (le_refl (0 : ℝ))
  have hright := gaussInv_lipschitz_weighted hn (by linarith : 0 ≤ 1 - 2 * β) (by norm_num : (0 : ℝ) ≤ 1)
  rw [sub_zero, abs_of_nonneg (by positivity : 0 ≤ 2 * β)] at hleft
  rw [show 1 - 2 * β - 1 = -(2 * β) by ring, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 2 * β)] at hright
  have H1 := (abs_le.mp hleft).1
  have H2 := (abs_le.mp hright).2
  have H3 := (abs_le.mp hL).1
  have H4 := (abs_le.mp hR).2
  simp only [gaussInv, add_zero] at H1 H2 H3 H4
  have hid : (4 * β + 2 * E) / n ^ 2 = 2 * (2 * β / n ^ 2) + 2 * (E / n ^ 2) := by ring
  rw [hid]
  linarith

end
end

section
noncomputable section
open BianchiIX
open Finset

private theorem BianchiIX.sum_gauss_digit_lengths (N : ℕ) :
    (∑ m ∈ range N, (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2))) = 1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ, ih, Nat.cast_succ]
    ring

end
end

section
noncomputable section
open BianchiIX
open Finset

private theorem BianchiIX.sum_inverse_square_digits_le_two (N : ℕ) :
    (∑ m ∈ range N, 1 / ((m : ℝ) + 1) ^ 2) ≤ 2 := by
  have H (m : ℕ) : 1 / ((m : ℝ) + 1) ^ 2 ≤
      2 * (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2)) := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hm1 : 0 < (m : ℝ) + 1 := by positivity
    have hm2 : 0 < (m : ℝ) + 2 := by positivity
    field_simp
    nlinarith
  calc
    _ ≤ ∑ m ∈ range N, 2 * (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2)) :=
      sum_le_sum (fun m _ => H m)
    _ = 2 * (1 - 1 / ((N : ℝ) + 1)) := by rw [← mul_sum, sum_gauss_digit_lengths]
    _ ≤ 2 := by
      have hn : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
      linarith

end
end


/-- Summable endpoint errors give a finite-digit loss bound, including all removed endpoints. -/
theorem solution {N : ℕ} {β E : ℝ} {L R : ℕ → ℝ}
    (hβ : 0 ≤ β) (hβmax : β ≤ 1 / 2) (hE : 0 ≤ E)
    (horder : ∀ m ∈ Finset.range N, R m < L m)
    (hlower : ∀ m ∈ Finset.range N, 1 / ((m : ℝ) + 2) < R m)
    (hupper : ∀ m ∈ Finset.range N, L m < 1 / ((m : ℝ) + 1))
    (hL : ∀ m ∈ Finset.range N,
      |L m - gaussInv ((m : ℝ) + 1) (2 * β)| ≤ E / ((m : ℝ) + 1) ^ 2)
    (hR : ∀ m ∈ Finset.range N,
      |R m - gaussInv ((m : ℝ) + 1) (1 - 2 * β)| ≤ E / ((m : ℝ) + 1) ^ 2) :
    (↑(Finset.range N) : Set ℕ).PairwiseDisjoint (fun m => Ioo (R m) (L m)) ∧
    MeasurableSet (Ioo (0 : ℝ) 1 \ retainedBranchPhases N L R) ∧
    volume (Ioo (0 : ℝ) 1 \ retainedBranchPhases N L R) ≤
      ENNReal.ofReal (1 / ((N : ℝ) + 1) + 8 * β + 4 * E) := by
  have hdisjlt (i j : ℕ) (hi : i ∈ Finset.range N) (hj : j ∈ Finset.range N) (hij : i < j) :
      Disjoint (Ioo (R i) (L i)) (Ioo (R j) (L j)) := by
    apply disjoint_left.mpr
    intro x hxi hxj
    have hcast : (i : ℝ) + 2 ≤ (j : ℝ) + 1 := by exact_mod_cast (show i + 2 ≤ j + 1 by omega)
    have hrec : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) hcast
    linarith [hlower i hi, hupper j hj, hxi.1, hxj.2]
  have hdisj : (↑(Finset.range N) : Set ℕ).PairwiseDisjoint (fun m => Ioo (R m) (L m)) := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact hdisjlt i j hi hj hij
    · exact (hdisjlt j i hj hi hji).symm
  have hmeas : MeasurableSet (retainedBranchPhases N L R) :=
    (Finset.finite_toSet _).measurableSet_biUnion (fun _ _ => measurableSet_Ioo)
  have hsub : retainedBranchPhases N L R ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    obtain ⟨m, hm, hxm⟩ := mem_iUnion₂.mp hx
    have hrec : 1 / ((m : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
    exact ⟨(by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 2)).trans
      ((hlower m hm).trans hxm.1), (hxm.2.trans (hupper m hm)).trans_le hrec⟩
  let S := ∑ m ∈ Finset.range N, (L m - R m)
  have hnonneg (m : ℕ) (hm : m ∈ Finset.range N) : 0 ≤ L m - R m := sub_nonneg.mpr (horder m hm).le
  have hS : 0 ≤ S := Finset.sum_nonneg hnonneg
  have hvol : volume (retainedBranchPhases N L R) = ENNReal.ofReal S := by
    rw [retainedBranchPhases, measure_biUnion_finset hdisj (fun _ _ => measurableSet_Ioo)]
    simp_rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_sum_of_nonneg hnonneg).symm
  have hwidth (m : ℕ) (hm : m ∈ Finset.range N) :
      1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2) -
        (4 * β + 2 * E) / ((m : ℝ) + 1) ^ 2 ≤ L m - R m := by
    simpa only [show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring] using
      gauss_branch_length_of_endpoint_error (by positivity : 0 < (m : ℝ) + 1)
        hβ hβmax (hL m hm) (hR m hm)
  have hsum := Finset.sum_le_sum hwidth
  have hcoeff : 0 ≤ 4 * β + 2 * E := by positivity
  have hweights := mul_le_mul_of_nonneg_left (sum_inverse_square_digits_le_two N) hcoeff
  have hformula : (∑ m ∈ Finset.range N,
      (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2) - (4 * β + 2 * E) / ((m : ℝ) + 1) ^ 2)) =
      1 - 1 / ((N : ℝ) + 1) - (4 * β + 2 * E) *
        (∑ m ∈ Finset.range N, 1 / ((m : ℝ) + 1) ^ 2) := by
    rw [Finset.sum_sub_distrib, sum_gauss_digit_lengths, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hformula] at hsum
  have htotal : 1 ≤ S + (1 / ((N : ℝ) + 1) + 8 * β + 4 * E) := by
    change _ ≤ S at hsum
    linarith
  have hfinite : volume (retainedBranchPhases N L R) ≠ ∞ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  refine ⟨hdisj, measurableSet_Ioo.diff hmeas, ?_⟩
  apply (measure_sdiff_le_iff_le_add hmeas.nullMeasurableSet hsub hfinite).mpr
  rw [hvol, ← ENNReal.ofReal_add hS (by positivity), Real.volume_Ioo]
  exact ENNReal.ofReal_le_ofReal (by simpa using htotal)
