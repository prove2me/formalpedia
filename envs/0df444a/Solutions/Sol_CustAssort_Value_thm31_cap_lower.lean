-- Prove2me | solution 1 for CustAssort.Value.thm31_cap_lower
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:49:55.067526+00:00
-- url     : https://prove2.me/submissions/a329b4cc-e0dd-4944-bc10-a8fd4614bf3e

import Mathlib
import Definitions.Def_CustAssort_Value_Setting

set_option autoImplicit false
open CustAssort.Value

theorem solution (m : ℕ) (a b : ℝ)
    (hm : 1 ≤ m) (ha : 0 < a) (hb : 1 ≤ b) :
    alpha a m * (m : ℝ) / 2 ≤ zCAP (thetaI a m) (vI b m) (revI a m) m := by
  have hb0 : 0 < b := by linarith
  have hα : 0 ≤ alpha a m := by
    unfold alpha
    apply inv_nonneg.mpr
    exact Finset.sum_nonneg (fun i _ => by positivity)
  have hθ : ∀ j : Fin m, 0 ≤ thetaI a m j := by
    intro j; unfold thetaI; positivity
  have hθa : ∀ j : Fin m, thetaI a m j * a ^ (j.val + 1) = alpha a m := by
    intro j
    unfold thetaI
    have : a ^ (j.val + 1) ≠ 0 := by positivity
    field_simp
  have hper : ∀ j : Fin m, alpha a m / 2 ≤
      thetaI a m j * CustAssort.AugGreedy.fj (vI b m) (revI a m) j Finset.univ := by
    intro j
    have hfj : CustAssort.AugGreedy.rev (vI b m) (revI a m) j {j} ≤
        CustAssort.AugGreedy.fj (vI b m) (revI a m) j Finset.univ := by
      unfold CustAssort.AugGreedy.fj
      exact Finset.le_sup' (CustAssort.AugGreedy.rev (vI b m) (revI a m) j)
        (by simp : ({j} : Finset (Fin m)) ∈ (Finset.univ : Finset (Fin m)).powerset)
    have hx : 1 ≤ b ^ (m - j.val) := one_le_pow₀ hb
    have hrev : a ^ (j.val + 1) / 2 ≤ CustAssort.AugGreedy.rev (vI b m) (revI a m) j {j} := by
      unfold CustAssort.AugGreedy.rev ChoiceCDLP.MNL.mnlObjective
      have hv : vI b m j j = b ^ (m - j.val) := by unfold vI; simp
      simp only [Finset.sum_singleton, hv]
      unfold revI
      rw [le_div_iff₀ (by positivity)]
      have : 0 < a ^ (j.val + 1) := by positivity
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left (hrev.trans hfj) (hθ j)
    have : thetaI a m j * (a ^ (j.val + 1) / 2) = alpha a m / 2 := by
      rw [← hθa j]; ring
    linarith
  calc alpha a m * (m : ℝ) / 2 = ∑ j : Fin m, alpha a m / 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
    _ ≤ ∑ j : Fin m, thetaI a m j *
          CustAssort.AugGreedy.fj (vI b m) (revI a m) j Finset.univ :=
        Finset.sum_le_sum (fun j _ => hper j)
    _ = CustAssort.AugGreedy.fC (thetaI a m) (vI b m) (revI a m) Finset.univ Finset.univ := rfl
    _ ≤ zCAP (thetaI a m) (vI b m) (revI a m) m := by
        unfold zCAP
        apply Finset.le_sup' (CustAssort.AugGreedy.fC (thetaI a m) (vI b m) (revI a m) Finset.univ)
        simp [feasible]

