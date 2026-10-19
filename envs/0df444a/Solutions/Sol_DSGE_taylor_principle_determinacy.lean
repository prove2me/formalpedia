-- Prove2me | solution 1 for DSGE.taylor_principle_determinacy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T13:47:09.567725+00:00
-- url     : https://prove2.me/submissions/ee148677-fa4a-4946-8be2-2fd89c7a507d

import Theorems.Thm_DSGE_bounded_orbits_zero_iff_eigenvalues_outside
import Theorems.Thm_DSGE_quadratic_roots_outside_unit_disk_iff
import Theorems.Thm_DSGE_nk_equilibrium_iff_forward

open Matrix

private noncomputable def forwardMatrix (σ β κ φπ φy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + φy / σ + κ / (σ * β), (φπ - 1 / β) / σ; -κ / β, 1 / β]

private lemma forward_recurrence (σ β κ φπ φy : ℝ) (hσ : σ ≠ 0) (hβ : β ≠ 0)
    (y π : ℕ → ℝ) :
    (∀ t, (![y (t+1), π (t+1)] : Fin 2 → ℝ) =
      (forwardMatrix σ β κ φπ φy).mulVec ![y t, π t]) ↔
    DSGE.IsNKEquilibrium σ β κ φπ φy y π (fun t => φπ * π t + φy * y t) := by
  rw [DSGE.nk_equilibrium_iff_forward σ β κ φπ φy hσ hβ]
  simp only [forwardMatrix, Matrix.mulVec_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.vecCons_inj, and_true, true_and]
  constructor
  · intro h t
    obtain ⟨hy, hp⟩ := h t
    exact ⟨by rw [hp]; ring, hy⟩
  · intro h t
    obtain ⟨hp, hy⟩ := h t
    exact ⟨hy, by rw [hp]; ring⟩

private lemma determinate_iff_orbits (σ β κ φπ φy : ℝ) (hσ : σ ≠ 0) (hβ : β ≠ 0) :
    DSGE.IsDeterminate σ β κ φπ φy ↔
      ∀ x : ℕ → Fin 2 → ℝ,
        (∀ t, x (t+1) = (forwardMatrix σ β κ φπ φy).mulVec (x t)) →
        (∃ C : ℝ, ∀ t j, |x t j| ≤ C) → ∀ t, x t = 0 := by
  constructor
  · intro h x hx ⟨C, hC⟩
    let y := fun t => x t 0
    let π := fun t => x t 1
    have heq : ∀ t, (![y (t+1), π (t+1)] : Fin 2 → ℝ) =
        (forwardMatrix σ β κ φπ φy).mulVec ![y t, π t] := by
      intro t
      have heta (k : ℕ) : x k = ![y k, π k] := by
        ext j
        fin_cases j <;> rfl
      rw [← heta (t+1), ← heta t]
      exact hx t
    have hi : DSGE.IsBoundedSeq (fun t => φπ * π t + φy * y t) := by
      refine ⟨|φπ| * C + |φy| * C, fun t => ?_⟩
      exact (abs_add_le _ _).trans (add_le_add
        (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC t 1) (abs_nonneg _))
        (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC t 0) (abs_nonneg _)))
    have hz := h y π _ ((forward_recurrence σ β κ φπ φy hσ hβ y π).mp heq)
      ⟨C, fun t => hC t 0⟩ ⟨C, fun t => hC t 1⟩ hi
    intro t
    ext j
    fin_cases j
    · exact (hz t).1
    · exact (hz t).2.1
  · intro h y π i heq ⟨Cy, hCy⟩ ⟨Cp, hCp⟩ _
    have hf := (DSGE.nk_equilibrium_iff_forward σ β κ φπ φy hσ hβ y π i).mp heq
    have heq' : DSGE.IsNKEquilibrium σ β κ φπ φy y π
        (fun t => φπ * π t + φy * y t) := by
      apply (DSGE.nk_equilibrium_iff_forward σ β κ φπ φy hσ hβ _ _ _).mpr
      intro t
      exact ⟨rfl, (hf t).2⟩
    have hz := h (fun t => ![y t, π t])
      ((forward_recurrence σ β κ φπ φy hσ hβ y π).mpr heq')
      ⟨max Cy Cp, fun t j => by
        fin_cases j
        · exact (hCy t).trans (le_max_left _ _)
        · exact (hCp t).trans (le_max_right _ _)⟩
    intro t
    have hy : y t = 0 := congrFun (hz t) 0
    have hp : π t = 0 := congrFun (hz t) 1
    exact ⟨hy, hp, by rw [(hf t).1, hy, hp]; ring⟩

private lemma matrix_invariants (σ β κ φπ φy : ℝ) (hσ : σ ≠ 0) (hβ : β ≠ 0) :
    (forwardMatrix σ β κ φπ φy).trace = 1 + φy / σ + κ / (σ * β) + 1 / β ∧
    (forwardMatrix σ β κ φπ φy).det = (σ + φy + κ * φπ) / (σ * β) := by
  constructor
  · simp [forwardMatrix, Matrix.trace_fin_two]
  · simp only [forwardMatrix, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp [hσ, hβ]
    ring

theorem solution (σ β κ φπ φy : ℝ)
    (hσ : 0 < σ) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hφπ : 0 ≤ φπ) (hφy : 0 ≤ φy) :
    DSGE.IsDeterminate σ β κ φπ φy ↔ 0 < κ * (φπ - 1) + (1 - β) * φy := by
  let M := forwardMatrix σ β κ φπ φy
  let T := 1 + φy / σ + κ / (σ * β) + 1 / β
  let D := (σ + φy + κ * φπ) / (σ * β)
  have hinv := matrix_invariants σ β κ φπ φy (ne_of_gt hσ) (ne_of_gt hβ0)
  have hD : 0 < D := by dsimp [D]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hc (z : ℂ) : (M.map (algebraMap ℝ ℂ)).charpoly.IsRoot z ↔
      z^2 - (T : ℂ) * z + (D : ℂ) = 0 := by
    rw [Polynomial.IsRoot, Matrix.charpoly_fin_two]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
    have ht : (M.map (algebraMap ℝ ℂ)).trace = (T : ℂ) := by
      exact (AddMonoidHom.map_trace (algebraMap ℝ ℂ) M).symm.trans (congrArg (algebraMap ℝ ℂ) hinv.1)
    have hd : (M.map (algebraMap ℝ ℂ)).det = (D : ℂ) := by
      exact ((algebraMap ℝ ℂ).map_det M).symm.trans (congrArg (algebraMap ℝ ℂ) hinv.2)
    rw [ht, hd]
  rw [determinate_iff_orbits σ β κ φπ φy (ne_of_gt hσ) (ne_of_gt hβ0),
    DSGE.bounded_orbits_zero_iff_eigenvalues_outside]
  change (∀ z : ℂ, (M.map (algebraMap ℝ ℂ)).charpoly.IsRoot z → 1 < ‖z‖) ↔ _
  simp_rw [hc]
  rw [DSGE.quadratic_roots_outside_unit_disk_iff T D hD, abs_of_nonneg hT]
  have hden : 0 < σ * β := mul_pos hσ hβ0
  have hdiff : (1 + D - T) * (σ * β) = κ * (φπ - 1) + (1 - β) * φy := by
    dsimp [D, T]
    field_simp
    ring
  have hD1 : 1 < D := by
    apply (lt_div_iff₀ hden).mpr
    nlinarith [mul_nonneg hκ.le hφπ, mul_pos hσ (sub_pos.mpr hβ1)]
  constructor
  · rintro ⟨_, hlt⟩
    rw [← hdiff]
    exact mul_pos (by linarith) hden
  · intro h
    refine ⟨hD1, ?_⟩
    have : 0 < 1 + D - T := (mul_pos_iff_of_pos_right hden).mp (hdiff ▸ h)
    linarith
