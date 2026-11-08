-- Prove2me | solution 1 for CosDensity.perturbation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:09:56.13729+00:00
-- url     : https://prove2.me/submissions/e4966b7f-aab6-4881-b7c4-63f4dd2ee40d

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_Perturb

open scoped RealInnerProductSpace

namespace Aux_CosDensity_pert
open CosDensity

theorem ip {ι : Type*} [Fintype ι] (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (x y : EuclideanSpace ℝ ι) :
    ⟪perturb ξ x, perturb ξ y⟫ = (1 - ξ ^ 2) * ⟪x, y⟫ + ξ ^ 2 := by
  have hs0 : Real.sqrt (1 - ξ ^ 2) * Real.sqrt (1 - ξ ^ 2) = 1 - ξ ^ 2 :=
    Real.mul_self_sqrt (by nlinarith)
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (1 - ξ ^ 2) := ⟨_, rfl⟩
  rw [← hs] at hs0
  rw [PiLp.inner_apply, PiLp.inner_apply x y, Fintype.sum_option, Finset.mul_sum]
  simp only [perturb, PiLp.toLp_apply, ← hs, RCLike.inner_apply, conj_trivial]
  rw [← hs0, add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    ring
  · ring

theorem unitize_of_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) (h : ‖x‖ = 1) : unitize x = x := by
  simp [unitize, h]

end Aux_CosDensity_pert

open CosDensity Aux_CosDensity_pert in
theorem solution {ι : Type*} [Fintype ι] {n : ℕ} (u : Fin n → EuclideanSpace ℝ ι)
    (hu : ∀ i, ‖u i‖ = 1) (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    (∀ i, ‖perturb ξ (u i)‖ = 1) ∧
    (∀ i j, ⟪perturb ξ (u i), perturb ξ (u j)⟫ = (1 - ξ ^ 2) * ⟪u i, u j⟫ + ξ ^ 2) ∧
    ((∀ i j, 0 ≤ ⟪u i, u j⟫) → ∀ i j, ξ ^ 2 ≤ ⟪perturb ξ (u i), perturb ξ (u j)⟫) ∧
    ∀ i, densityF (fun k => perturb ξ (u k)) i = (1 - ξ ^ 2) * densityF u i + n * ξ ^ 2 := by
  have hn : ∀ i, ‖perturb ξ (u i)‖ = 1 := by
    intro i
    have h1 := ip ξ hξ0 hξ1 (u i) (u i)
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu i] at h1
    have h2 : ‖perturb ξ (u i)‖ ^ 2 = 1 := by rw [h1]; ring
    have h3 := norm_nonneg (perturb ξ (u i))
    nlinarith
  refine ⟨hn, fun i j => ip ξ hξ0 hξ1 _ _, fun h i j => ?_, fun i => ?_⟩
  · rw [ip ξ hξ0 hξ1]
    have : 0 ≤ 1 - ξ ^ 2 := by nlinarith
    have := mul_nonneg this (h i j)
    linarith
  · unfold densityF
    simp only [unitize_of_norm _ (hn _), unitize_of_norm _ (hu _), ip ξ hξ0 hξ1]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
