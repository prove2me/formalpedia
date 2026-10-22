-- Prove2me | solution 1 for CustAssort.Value.thm31_second_term
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:49:24.292719+00:00
-- url     : https://prove2.me/submissions/f1755d90-ddc2-4d3a-9153-51acc04bf374

import Mathlib
import Definitions.Def_CustAssort_Value_Setting

set_option autoImplicit false
open CustAssort.Value

theorem solution (m : ℕ) (a b : ℝ) (hb : 1 ≤ b) (ha : 0 < a)
    (S : Finset (Fin m)) (hS : S.Nonempty) (j : Fin m) (hj : j ∈ S) :
    secondTerm a b S j ≤ alpha a m / b ^ (j.val - (S.min' hS).val) := by
  have hb0 : 0 < b := by linarith
  have hα : 0 ≤ alpha a m := by
    unfold alpha
    apply inv_nonneg.mpr
    exact Finset.sum_nonneg (fun i _ => by positivity)
  set i0 := S.min' hS with hi0
  have hi0S : i0 ∈ S := Finset.min'_mem S hS
  have hi0j : i0 ≤ j := Finset.min'_le S j hj
  have hi0j' : i0.val ≤ j.val := hi0j
  have hjm : j.val < m := j.isLt
  have hvnn : ∀ i : Fin m, 0 ≤ vI b m i j := by
    intro i; unfold vI; split_ifs <;> positivity
  have hD : b ^ (m - i0.val) ≤ 1 + ∑ i ∈ S, vI b m i j := by
    have h1 : vI b m i0 j ≤ ∑ i ∈ S, vI b m i j :=
      Finset.single_le_sum (f := fun i => vI b m i j) (fun i _ => hvnn i) hi0S
    have h2 : vI b m i0 j = b ^ (m - i0.val) := by
      unfold vI; simp [hi0j]
    linarith
  have hpos : 0 < b ^ (m - i0.val) := by positivity
  have hpow : b ^ (m - i0.val) = b ^ (m - j.val) * b ^ (j.val - i0.val) := by
    rw [← pow_add]; congr 1; omega
  unfold secondTerm
  simp only [hj, if_true]
  calc alpha a m * b ^ (m - j.val) / (1 + ∑ i ∈ S, vI b m i j)
      ≤ alpha a m * b ^ (m - j.val) / b ^ (m - i0.val) :=
        div_le_div_of_nonneg_left (by positivity) hpos hD
    _ = alpha a m / b ^ (j.val - i0.val) := by
        rw [hpow]
        have : b ^ (m - j.val) ≠ 0 := by positivity
        have : b ^ (j.val - i0.val) ≠ 0 := by positivity
        field_simp

