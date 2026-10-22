-- Prove2me | solution 1 for ConicQuadIPM.NTScaling.eq_63
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:34:33.31932+00:00
-- url     : https://prove2.me/submissions/b89ae1cc-ca0a-4b48-a5b1-09805e61ffe7

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
set_option autoImplicit false
open Matrix
open ConicQuadIPM.NTScaling

theorem gg_T_left (d : ℕ) (i k : Fin d) (hi : ¬ i.val < 2) :
    Tmat .rot d i k = if i = k then 1 else 0 := by
  simp only [Tmat, Matrix.of_apply]
  rw [if_neg (fun h => hi h.1)]

theorem gg_T_right (d : ℕ) (k j : Fin d) (hj : ¬ j.val < 2) :
    Tmat .rot d k j = if k = j then 1 else 0 := by
  simp only [Tmat, Matrix.of_apply]
  rw [if_neg (fun h => hj h.2)]

theorem gg_T_small (d : ℕ) (i j : Fin d) (hi : i.val < 2) (hj : j.val < 2) :
    Tmat .rot d i j = if i.val = 1 ∧ j.val = 1 then -(1 / Real.sqrt 2) else 1 / Real.sqrt 2 := by
  simp only [Tmat, Matrix.of_apply]
  rw [if_pos ⟨hi, hj⟩]

theorem gg_TT (d : ℕ) (hd : 2 ≤ d) : Tmat .rot d * Tmat .rot d = 1 := by
  have hs : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1 / 2 := by
    rw [← mul_div_mul_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
  have hs' : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by rw [← one_div, hs]
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i.val < 2
  · by_cases hj : j.val < 2
    · have h0 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
      rw [Finset.sum_eq_add_of_mem (⟨0, by omega⟩ : Fin d) ⟨1, by omega⟩ (Finset.mem_univ _)
        (Finset.mem_univ _) h0]
      · have hi' : i.val = 0 ∨ i.val = 1 := by omega
        have hj' : j.val = 0 ∨ j.val = 1 := by omega
        rw [gg_T_small d i ⟨0, by omega⟩ hi (by simp), gg_T_small d i ⟨1, by omega⟩ hi (by simp),
          gg_T_small d ⟨0, by omega⟩ j (by simp) hj, gg_T_small d ⟨1, by omega⟩ j (by simp) hj]
        rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj' <;>
          simp [Matrix.one_apply, Fin.ext_iff, hi', hj'] <;> nlinarith [hs, hs']
      · intro c _ hc
        have hc0 : c.val ≠ 0 := fun h => hc.1 (Fin.ext h)
        have hc1 : c.val ≠ 1 := fun h => hc.2 (Fin.ext h)
        have hc2 : ¬ c.val < 2 := by omega
        rw [gg_T_right d i c hc2, if_neg (by intro h; rw [h] at hi; exact hc2 hi), zero_mul]
    · have hj' : ¬ j.val < 2 := hj
      simp only [gg_T_right d _ j hj', mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ j, if_pos (Finset.mem_univ _), gg_T_right d i j hj',
        Matrix.one_apply]
  · rw [Finset.sum_congr rfl (fun k _ => by rw [gg_T_left d i k hi])]
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ i, if_pos (Finset.mem_univ _), Matrix.one_apply]
    rw [gg_T_left d i j hi]

theorem solution (d : ℕ) (hd : 2 ≤ d) (W : Matrix (Fin d) (Fin d) ℝ) (θ : ℝ)
    (x s : Fin d → ℝ) :
    (W * Qmat .rot d * W = Qmat .rot d →
      (Tmat .rot d * W * Tmat .rot d) * (Tmat .rot d * Qmat .rot d * Tmat .rot d) *
          (Tmat .rot d * W * Tmat .rot d) =
        Tmat .rot d * Qmat .rot d * Tmat .rot d) ∧
    (s = θ ^ 2 • ((W * W) *ᵥ x) →
      Tmat .rot d *ᵥ s =
        θ ^ 2 • (((Tmat .rot d * W * Tmat .rot d) * (Tmat .rot d * W * Tmat .rot d)) *ᵥ
          (Tmat .rot d *ᵥ x))) := by
  have TT := gg_TT d hd
  have TTx : ∀ X : Matrix (Fin d) (Fin d) ℝ, Tmat .rot d * (Tmat .rot d * X) = X := by
    intro X; rw [← Matrix.mul_assoc, TT, Matrix.one_mul]
  constructor
  · intro h
    have e : (Tmat .rot d * W * Tmat .rot d) * (Tmat .rot d * Qmat .rot d * Tmat .rot d) *
          (Tmat .rot d * W * Tmat .rot d) = Tmat .rot d * (W * Qmat .rot d * W) * Tmat .rot d := by
      simp only [Matrix.mul_assoc, TTx, TT, Matrix.mul_one]
    rw [e, h]
  · intro hs
    subst hs
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 2
    simp only [Matrix.mul_assoc, TTx, TT, Matrix.mul_one]
