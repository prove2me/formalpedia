-- Prove2me | solution 1 for CloudMWU.Bicriteria.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T12:37:31.329635+00:00
-- url     : https://prove2.me/submissions/ba8af3d0-d29c-46a8-bc0e-7583148bfac3

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model
import Theorems.Thm_CloudMWU_Bicriteria_theorem_3
import Theorems.Thm_CloudMWU_Bicriteria_theorem_4
import Theorems.Thm_CloudMWU_Bicriteria_scaling_step

open Finset CloudMWU.Bicriteria

theorem solution (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3)
    (β : Fin N → ℝ) (hβ : ∀ i, 2 * ε / (N : ℝ) ≤ β i) (hβsum : ∑ i, β i ≤ 1)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h) :
    (∀ hstar : ℕ → Fin N → ℝ, IsAllocSeq 1 hstar → ∀ t : ℕ,
      (1 - 4 * ε) * totalWork hstar L t
          - 2000 * (N : ℝ) / (ε ^ 2 * η) * Real.log ((N : ℝ) / ε)
        ≤ totalWork h L t) ∧
    (∀ (i : Fin N) (a : ℕ → ℝ), (∀ t, 0 ≤ a t ∧ a t ≤ β i) → ∀ t : ℕ,
      (1 - 2 * ε) * cumWork a (fun τ => L τ i) t - β i * pTilde N ε η
        ≤ cumWork (fun τ => h τ i) (fun τ => L τ i) t) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  constructor
  · intro hstar hstar_alloc t
    set hbar : ℕ → Fin N → ℝ := fun τ j => (1 - 4 * ε) * hstar τ j with hbar_def
    have hbar_alloc : IsAllocSeq (1 - 4 * ε) hbar := by
      intro τ
      obtain ⟨h1, h2⟩ := hstar_alloc τ
      refine ⟨fun j => mul_nonneg (by linarith) (h1 j), ?_⟩
      simp only [hbar_def, ← Finset.mul_sum]
      nlinarith
    have h3 := theorem_3 N hN ε η hε hε' hη hη' β L hL h hrun hbar hbar_alloc t
    have hscale : (1 - 4 * ε) * totalWork hstar L t ≤ totalWork hbar L t := by
      unfold totalWork
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      exact (scaling_step (fun τ => L τ j) (fun τ => hL τ j)).1 (1 - 4 * ε) (by linarith)
        (by linarith) (fun τ => hstar τ j) t
    -- the constant bound
    set X : ℝ := (N : ℝ) / (ε ^ 2 * η) * Real.log ((N : ℝ) / ε) with hX
    have hlog : 1 ≤ Real.log ((N : ℝ) / ε) := by
      have h20 : (20 : ℝ) ≤ (N : ℝ) / ε := by
        rw [le_div_iff₀ hε]; nlinarith
      have he : Real.exp 1 ≤ (N : ℝ) / ε := by
        have := Real.exp_one_lt_d9; linarith
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ _ := Real.log_le_log (Real.exp_pos 1) he
    have hcoef : 1 ≤ (N : ℝ) / (ε ^ 2 * η) := by
      have hpos : 0 < ε ^ 2 * η := by positivity
      rw [le_div_iff₀ hpos]
      have : ε ^ 2 ≤ 1 / 100 := by nlinarith
      nlinarith
    have hX1 : 1 ≤ X := by
      rw [hX]; nlinarith
    have e1 : 2000 * (N : ℝ) / (ε ^ 2 * η) * Real.log ((N : ℝ) / ε) = 2000 * X := by
      rw [hX]; ring
    have e2 : 8 * (N : ℝ) / (ε ^ 2 * η) * Real.log ((N : ℝ) / ε) = 8 * X := by
      rw [hX]; ring
    rw [e1]
    rw [e2] at h3
    linarith
  · intro i a ha t
    have hexp : Real.exp (η * (1 + lam N ε)) * ε / (N : ℝ) < 2 * ε / (N : ℝ) := by
      apply div_lt_div_of_pos_right _ hNpos
      have hlam : lam N ε ≤ 1 / 100 := by
        unfold lam
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have hlam0 : 0 ≤ lam N ε := by unfold lam; positivity
      have hx : η * (1 + lam N ε) < Real.log 2 := by
        have := Real.log_two_gt_d9
        nlinarith
      have : Real.exp (η * (1 + lam N ε)) < 2 := by
        calc Real.exp (η * (1 + lam N ε)) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hx
          _ = 2 := Real.exp_log (by norm_num)
      nlinarith
    have hβ4 : ∀ j, Real.exp (η * (1 + lam N ε)) * ε / (N : ℝ) < β j :=
      fun j => lt_of_lt_of_le hexp (hβ j)
    have h4 := (theorem_4 N hN ε η hε hε' hη hη' β hβ4 hβsum L hL h hrun i t).2
    have hs := scaling_step (fun τ => L τ i) (fun τ => hL τ i)
    have s1 := hs.1 (1 - 2 * ε) (by linarith) (by linarith) a t
    have s2 := hs.2 (fun τ => (1 - 2 * ε) * a τ) (fun _ => (1 - 2 * ε) * β i)
      (fun τ => mul_le_mul_of_nonneg_left (ha τ).2 (by linarith)) t
    linarith
