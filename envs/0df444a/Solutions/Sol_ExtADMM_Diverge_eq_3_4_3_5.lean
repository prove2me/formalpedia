-- Prove2me | solution 1 for ExtADMM.Diverge.eq_3_4_3_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:55:17.120523+00:00
-- url     : https://prove2.me/submissions/8066599e-8912-45b4-8c19-4db8981aaaaa

import Mathlib
import Definitions.Def_ExtADMM_Diverge_Setting
set_option autoImplicit false
open Matrix ExtADMM.Diverge

lemma ss_aug31 (a1 a2 a3 : Fin 3 → ℝ) (β : ℝ) (y1 y2 y3 : Fin 1 → ℝ) (lam : Fin 3 → ℝ) :
    (instance31 a1 a2 a3).augLag β y1 y2 y3 lam =
      -(lam ⬝ᵥ (y1 0 • a1 + y2 0 • a2 + y3 0 • a3)) +
        β / 2 * ((y1 0 • a1 + y2 0 • a2 + y3 0 • a3) ⬝ᵥ (y1 0 • a1 + y2 0 • a2 + y3 0 • a3)) := by
  have hr : (instance31 a1 a2 a3).residual y1 y2 y3 = y1 0 • a1 + y2 0 • a2 + y3 0 • a3 := by
    ext i
    simp [Problem.residual, instance31, ExtADMM.Diverge.col, Matrix.mulVec, dotProduct]
    ring
  unfold Problem.augLag
  rw [hr]
  simp [Problem.objective, instance31]

lemma ss_quad_stat (a v lam : Fin 3 → ℝ) (β : ℝ) (hβ : 0 < β) (ha : 0 < a ⬝ᵥ a)
    (W : ℝ → Fin 3 → ℝ) (hW : ∀ y, W y = y • a + v) (u : ℝ)
    (h : ∀ y, -(lam ⬝ᵥ W u) + β / 2 * (W u ⬝ᵥ W u) ≤ -(lam ⬝ᵥ W y) + β / 2 * (W y ⬝ᵥ W y)) :
    (a ⬝ᵥ a) * u = a ⬝ᵥ (β⁻¹ • lam) - a ⬝ᵥ v := by
  set S := a ⬝ᵥ a with hS
  have hSne : S ≠ 0 := ha.ne'
  set ystar : ℝ := (a ⬝ᵥ (β⁻¹ • lam) - a ⬝ᵥ v) / S with hy
  have h1 := h ystar
  have key : (-(lam ⬝ᵥ W u) + β / 2 * (W u ⬝ᵥ W u)) - (-(lam ⬝ᵥ W ystar) + β / 2 * (W ystar ⬝ᵥ W ystar))
      = β / 2 * S * (u - ystar) ^ 2 := by
    rw [hW, hW]
    simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      dotProduct_comm v a, dotProduct_comm lam a, hy]
    generalize a ⬝ᵥ lam = p1
    generalize a ⬝ᵥ v = p2
    generalize lam ⬝ᵥ v = p3
    generalize v ⬝ᵥ v = p4
    rw [← hS]
    field_simp
    ring
  have h2 : β / 2 * S * (u - ystar) ^ 2 ≤ 0 := by linarith
  have h3 : (u - ystar) ^ 2 ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    have : 0 < β / 2 * S * (u - ystar) ^ 2 := by positivity
    linarith
  have h4 : u = ystar := by nlinarith [sq_nonneg (u - ystar)]
  rw [h4, hy]
  field_simp

lemma ss_res31 (a1 a2 a3 : Fin 3 → ℝ) (y1 y2 y3 : Fin 1 → ℝ) :
    (instance31 a1 a2 a3).residual y1 y2 y3 = y1 0 • a1 + y2 0 • a2 + y3 0 • a3 := by
  ext i
  simp [Problem.residual, instance31, ExtADMM.Diverge.col, Matrix.mulVec, dotProduct]
  ring

lemma ss_dot_pos (a : Fin 3 → ℝ) (h : a ≠ 0) : 0 < a ⬝ᵥ a := by
  have h0 : 0 ≤ a ⬝ᵥ a := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rcases h0.lt_or_eq with h1 | h1
  · exact h1
  · exact absurd (dotProduct_self_eq_zero.mp h1.symm) h

theorem solution (a1 a2 a3 : Fin 3 → ℝ) (hA : (colMat a1 a2 a3).det ≠ 0)
    (β : ℝ) (hβ : 0 < β)
    (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ)
    (hrun : (instance31 a1 a2 a3).IsRun15 β x1 x2 x3 lam) (k : ℕ) :
    x1 (k+1) 0 = (1 / (a1 ⬝ᵥ a1)) *
        (-(a1 ⬝ᵥ a2) * x2 k 0 - (a1 ⬝ᵥ a3) * x3 k 0 + a1 ⬝ᵥ (β⁻¹ • lam k)) ∧
      Lmat a2 a3 *ᵥ stateVec β (x2 (k+1)) (x3 (k+1)) (lam (k+1)) =
        Rmat a1 a2 a3 *ᵥ stateVec β (x2 k) (x3 k) (lam k) := by
  have ha1 : 0 < a1 ⬝ᵥ a1 := by
    apply ss_dot_pos; rintro rfl; apply hA
    exact Matrix.det_eq_zero_of_column_eq_zero 0 (fun i => by simp [colMat])
  have ha2 : 0 < a2 ⬝ᵥ a2 := by
    apply ss_dot_pos; rintro rfl; apply hA
    exact Matrix.det_eq_zero_of_column_eq_zero 1 (fun i => by simp [colMat])
  have ha3 : 0 < a3 ⬝ᵥ a3 := by
    apply ss_dot_pos; rintro rfl; apply hA
    exact Matrix.det_eq_zero_of_column_eq_zero 2 (fun i => by simp [colMat])
  obtain ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩, hl⟩ := hrun k
  have E1 := ss_quad_stat a1 (x2 k 0 • a2 + x3 k 0 • a3) (lam k) β hβ ha1
    (fun y => y • a1 + x2 k 0 • a2 + x3 k 0 • a3) (fun y => by rw [add_assoc]) (x1 (k+1) 0)
    (fun y => by
      have := h1 (fun _ => y) (Set.mem_univ _)
      rw [ss_aug31, ss_aug31] at this
      exact this)
  have E2 := ss_quad_stat a2 (x1 (k+1) 0 • a1 + x3 k 0 • a3) (lam k) β hβ ha2
    (fun y => x1 (k+1) 0 • a1 + y • a2 + x3 k 0 • a3) (fun y => by abel) (x2 (k+1) 0)
    (fun y => by
      have := h2 (fun _ => y) (Set.mem_univ _)
      rw [ss_aug31, ss_aug31] at this
      exact this)
  have E3 := ss_quad_stat a3 (x1 (k+1) 0 • a1 + x2 (k+1) 0 • a2) (lam k) β hβ ha3
    (fun y => x1 (k+1) 0 • a1 + x2 (k+1) 0 • a2 + y • a3) (fun y => by abel) (x3 (k+1) 0)
    (fun y => by
      have := h3 (fun _ => y) (Set.mem_univ _)
      rw [ss_aug31, ss_aug31] at this
      exact this)
  rw [ss_res31] at hl
  have hlam : ∀ i, lam (k+1) i / β = lam k i / β -
      (x1 (k+1) 0 * a1 i + x2 (k+1) 0 * a2 i + x3 (k+1) 0 * a3 i) := by
    intro i
    rw [hl]
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    field_simp
  have h34 : x1 (k+1) 0 = (1 / (a1 ⬝ᵥ a1)) *
        (-(a1 ⬝ᵥ a2) * x2 k 0 - (a1 ⬝ᵥ a3) * x3 k 0 + a1 ⬝ᵥ (β⁻¹ • lam k)) := by
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at E1
    rw [one_div, inv_mul_eq_div, eq_div_iff ha1.ne']
    simp only [dotProduct_smul, smul_eq_mul]
    linarith
  refine ⟨h34, ?_⟩
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at E2 E3
  simp only [dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul] at h34 E2 E3
  ext i
  fin_cases i
  all_goals
    simp [Lmat, Rmat, stateVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hlam]
  · linear_combination E2 - (a2 0 * a1 0 + a2 1 * a1 1 + a2 2 * a1 2) * h34
  · linear_combination E3 - (a3 0 * a1 0 + a3 1 * a1 1 + a3 2 * a1 2) * h34
  · linear_combination (-(a1 0)) * h34
  · linear_combination (-(a1 1)) * h34
  · linear_combination (-(a1 2)) * h34
