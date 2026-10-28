-- Prove2me | solution 1 for ExtADMM.StrongCvx.fixed_matrix_mapping
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:57:34.464692+00:00
-- url     : https://prove2.me/submissions/394e263e-5e3d-4dad-965e-5f6a8db440cb

import Mathlib
import Definitions.Def_ExtADMM_StrongCvx_Setting
import Definitions.Def_ExtADMM_StrongCvx_Example41

open Matrix

namespace Aux_EA_fm

open ExtADMM.StrongCvx

noncomputable def AL (y1 y2 y3 l0 l1 l2 : ℝ) : ℝ :=
  (1 / 20 : ℝ) * (y1 ^ 2 + y2 ^ 2 + y3 ^ 2)
    - (l0 * (y1 + y2 + y3) + l1 * (y1 + y2 + 2 * y3) + l2 * (y1 + 2 * y2 + 2 * y3))
    + 1 / 2 * ((y1 + y2 + y3) ^ 2 + (y1 + y2 + 2 * y3) ^ 2 + (y1 + 2 * y2 + 2 * y3) ^ 2)

lemma hAL (y1 y2 y3 : Fin 1 → ℝ) (l : Fin 3 → ℝ) :
    example41.augLag 1 y1 y2 y3 l = AL (y1 0) (y2 0) (y3 0) (l 0) (l 1) (l 2) := by
  simp only [Problem.augLag, Problem.objective, Problem.residual, example41,
    ExtADMM.Diverge.col, AL]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

lemma quad_stat (F : ℝ → ℝ) (u A g : ℝ) (hA : 0 < A)
    (hF : ∀ t, F (u + t) - F u = g * t + A * t ^ 2) (hmin : ∀ t, F u ≤ F (u + t)) : g = 0 := by
  have h1 := hmin (-g / (2 * A))
  have h2 := hF (-g / (2 * A))
  have h3 : g * (-g / (2 * A)) + A * (-g / (2 * A)) ^ 2 = -(g ^ 2 / (4 * A)) := by
    field_simp; ring
  have h4 : g ^ 2 / (4 * A) ≤ 0 := by linarith
  have h5 : g ^ 2 ≤ 0 := by
    have := div_nonpos_iff.mp h4
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · nlinarith
    · exact h
  nlinarith [sq_nonneg g]

end Aux_EA_fm

open ExtADMM.StrongCvx Aux_EA_fm in
theorem solution (x1 x2 x3 : ℕ → Fin 1 → ℝ)
    (lam : ℕ → Fin 3 → ℝ) (hrun : example41.IsRun15 1 x1 x2 x3 lam) (k : ℕ) :
    stateVec (x2 (k+1)) (x3 (k+1)) (lam (k+1)) = M41 *ᵥ stateVec (x2 k) (x3 k) (lam k) := by
  obtain ⟨⟨_, h1⟩, ⟨_, h2⟩, ⟨_, h3⟩, h4⟩ := hrun k
  set u := x1 (k + 1) 0
  set w2 := x2 (k + 1) 0
  set w3 := x3 (k + 1) 0
  set v2 := x2 k 0
  set v3 := x3 k 0
  set l0 := lam k 0
  set l1 := lam k 1
  set l2 := lam k 2
  -- stationarity for x1
  have E1 : (1 / 10 : ℝ) * u - (l0 + l1 + l2) +
      ((u + v2 + v3) + (u + v2 + 2 * v3) + (u + 2 * v2 + 2 * v3)) = 0 := by
    apply quad_stat (fun t => AL t v2 v3 l0 l1 l2) u (1 / 20 + 3 / 2) _ (by norm_num)
    · intro t; simp only [AL]; ring
    · intro t
      have := h1 (fun _ => u + t) (Set.mem_univ _)
      rw [hAL, hAL] at this
      exact this
  have E2 : (1 / 10 : ℝ) * w2 - (l0 + l1 + 2 * l2) +
      ((u + w2 + v3) + (u + w2 + 2 * v3) + 2 * (u + 2 * w2 + 2 * v3)) = 0 := by
    apply quad_stat (fun t => AL u t v3 l0 l1 l2) w2 (1 / 20 + 3) _ (by norm_num)
    · intro t; simp only [AL]; ring
    · intro t
      have := h2 (fun _ => w2 + t) (Set.mem_univ _)
      rw [hAL, hAL] at this
      exact this
  have E3 : (1 / 10 : ℝ) * w3 - (l0 + 2 * l1 + 2 * l2) +
      ((u + w2 + w3) + 2 * (u + w2 + 2 * w3) + 2 * (u + 2 * w2 + 2 * w3)) = 0 := by
    apply quad_stat (fun t => AL u w2 t l0 l1 l2) w3 (1 / 20 + 9 / 2) _ (by norm_num)
    · intro t; simp only [AL]; ring
    · intro t
      have := h3 (fun _ => w3 + t) (Set.mem_univ _)
      rw [hAL, hAL] at this
      exact this
  have hl : ∀ i, lam (k + 1) i = lam k i - Problem.residual example41 (x1 (k + 1)) (x2 (k + 1))
      (x3 (k + 1)) i := by
    intro i; rw [h4]; simp
  have hres : ∀ i, Problem.residual example41 (x1 (k + 1)) (x2 (k + 1)) (x3 (k + 1)) i =
      ![u + w2 + w3, u + w2 + 2 * w3, u + 2 * w2 + 2 * w3] i := by
    intro i
    simp only [Problem.residual, example41, ExtADMM.Diverge.col]
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, u, w2, w3] <;> ring
  have hl0 := hl 0
  have hl1 := hl 1
  have hl2 := hl 2
  rw [hres] at hl0 hl1 hl2
  simp at hl0 hl1 hl2
  funext i
  fin_cases i <;>
    simp [stateVec, M41, mulVec, dotProduct, Fin.sum_univ_succ] <;>
    linarith
