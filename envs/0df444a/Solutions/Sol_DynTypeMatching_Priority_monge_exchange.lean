-- Prove2me | solution 1 for DynTypeMatching.Priority.monge_exchange
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:47:40.090735+00:00
-- url     : https://prove2.me/submissions/413950a7-33fb-4802-9e78-dcdaf0cc72e5

import Mathlib
import Definitions.Def_DynTypeMatching_Priority_Model
import Definitions.Def_DynTypeMatching_Priority_Relations

open DynTypeMatching.Priority in
theorem solution {m n : ℕ} (M : Model m n) (hM : M.WellPosed) (t : ℕ) (ht1 : 1 ≤ t)
    (htT : t ≤ M.T) (x : Fin m → ℝ) (y : Fin n → ℝ) (Q : Fin m → Fin n → ℝ)
    (hQ : Feasible x y Q) (hMonge : MongeCondition M) (i i' : Fin m) (j j' : Fin n)
    (hCol : DomCol M i i' j) (hRow : DomRow M i j j')
    (ε : ℝ) (hε : ε = min (Q i' j) (Q i j')) :
    Feasible x y (Q + ε • unitMat i j + ε • unitMat i' j' - ε • unitMat i' j - ε • unitMat i j') ∧
      H M t Q x y ≤
        H M t (Q + ε • unitMat i j + ε • unitMat i' j' - ε • unitMat i' j - ε • unitMat i j') x y := by
  have hii : i' ≠ i := hCol.1
  have hjj : j' ≠ j := hRow.1
  have hε0 : 0 ≤ ε := by rw [hε]; exact le_min (hQ.1 _ _) (hQ.1 _ _)
  have hε1 : ε ≤ Q i' j := by rw [hε]; exact min_le_left _ _
  have hε2 : ε ≤ Q i j' := by rw [hε]; exact min_le_right _ _
  set Q' := Q + ε • unitMat i j + ε • unitMat i' j' - ε • unitMat i' j - ε • unitMat i j' with hQ'
  have hent : ∀ a b, Q' a b = Q a b + ε * (unitMat i j a b + unitMat i' j' a b
      - unitMat i' j a b - unitMat i j' a b) := by
    intro a b
    simp only [hQ', Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hrow : ∀ (p : Fin m) (q : Fin n) a, ∑ b, unitMat p q a b = if a = p then 1 else 0 := by
    intro p q a
    by_cases ha : a = p
    · simp [unitMat, ha]
    · simp [unitMat, ha]
  have hcol : ∀ (p : Fin m) (q : Fin n) b, ∑ a, unitMat p q a b = if b = q then 1 else 0 := by
    intro p q b
    by_cases hb : b = q
    · simp [unitMat, hb]
    · simp [unitMat, hb]
  have hD : postD x Q' = postD x Q := by
    funext a
    simp only [postD, hent, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hrow]
    ring
  have hS : postS y Q' = postS y Q := by
    funext b
    simp only [postS, hent, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hcol]
    ring
  have hfeas : Feasible x y Q' := by
    refine ⟨fun a b => ?_, by rw [hD]; exact hQ.2.1, by rw [hS]; exact hQ.2.2⟩
    rw [hent]
    by_cases h3 : a = i' ∧ b = j
    · obtain ⟨rfl, rfl⟩ := h3
      simp [unitMat, hii, hjj, hii.symm, hjj.symm]
      linarith
    · by_cases h4 : a = i ∧ b = j'
      · obtain ⟨rfl, rfl⟩ := h4
        simp [unitMat, hii, hjj, hii.symm, hjj.symm]
        linarith
      · have e3 : unitMat i' j a b = 0 := if_neg h3
        have e4 : unitMat i j' a b = 0 := if_neg h4
        rw [e3, e4]
        have h1 : 0 ≤ unitMat i j a b := by unfold unitMat; split_ifs <;> norm_num
        have h2 : 0 ≤ unitMat i' j' a b := by unfold unitMat; split_ifs <;> norm_num
        have := hQ.1 a b
        nlinarith
  refine ⟨hfeas, ?_⟩
  have hsumE : ∀ (f : Fin m → Fin n → ℝ) (p : Fin m) (q : Fin n),
      ∑ a, ∑ b, f a b * unitMat p q a b = f p q := by
    intro f p q
    rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
    · simp [unitMat]
    · intro b _ hb; simp [unitMat, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [unitMat, ha]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hmr : matchReward M t Q' = matchReward M t Q
      + ε * (M.r t i j + M.r t i' j' - M.r t i' j - M.r t i j') := by
    unfold matchReward
    have e : ∀ a b, M.r t a b * Q' a b = M.r t a b * Q a b + ε * (M.r t a b * unitMat i j a b
        + M.r t a b * unitMat i' j' a b - M.r t a b * unitMat i' j a b
        - M.r t a b * unitMat i j' a b) := by
      intro a b; rw [hent]; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hsumE]
  unfold H
  rw [hD, hS, hmr]
  have hm := hMonge i i' j j' hCol hRow t ht1 htT
  have : 0 ≤ ε * (M.r t i j + M.r t i' j' - M.r t i' j - M.r t i j') :=
    mul_nonneg hε0 (by linarith)
  linarith
