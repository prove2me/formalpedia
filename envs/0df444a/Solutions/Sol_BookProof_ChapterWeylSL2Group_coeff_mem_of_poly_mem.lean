-- Prove2me | solution 1 for BookProof.ChapterWeylSL2Group.coeff_mem_of_poly_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:40:12.899609+00:00
-- url     : https://prove2.me/submissions/6dc21e0a-4006-4b2d-8406-e7fbcf0bfa93

-- Generated from ChapterWeylSL2Group.lean — solution of BookProof.ChapterWeylSL2Group.coeff_mem_of_poly_mem
import Mathlib
import Definitions.Def_ChapterWeylSL2Group
import Definitions.Def_ChapterWeylSl2
open BookProof.ChapterWeylSL2Group




open BookProof.ChapterWeylSl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution {W : Submodule ℂ V} {N : ℕ} {c : ℕ → V}
    (h : ∀ t : ℂ, ∑ k ∈ Finset.range N, t ^ k • c k ∈ W) {k : ℕ} (hk : k < N) : c k ∈ W := by

  by_contra hcon
  have hq : W.mkQ (c k) ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hcon
  obtain ⟨lam, hlam⟩ := Module.Projective.exists_dual_eq_one ℂ hq
  set mu : V →ₗ[ℂ] ℂ := lam ∘ₗ W.mkQ with hmu
  have hmuW : ∀ x ∈ W, mu x = 0 := by
    intro x hx
    have : W.mkQ x = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    rw [hmu]
    simp [this]
  have hmuk : mu (c k) = 1 := hlam
  set P : Polynomial ℂ :=
    ∑ j ∈ Finset.range N, Polynomial.C (mu (c j)) * Polynomial.X ^ j with hP
  have hPeval : ∀ t : ℂ, P.eval t = 0 := by
    intro t
    have h1 : P.eval t = ∑ j ∈ Finset.range N, mu (c j) * t ^ j := by
      rw [hP, Polynomial.eval_finset_sum]
      exact Finset.sum_congr rfl fun j _ => by simp
    have h2 : ∑ j ∈ Finset.range N, mu (c j) * t ^ j
        = mu (∑ j ∈ Finset.range N, t ^ j • c j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, mul_comm]
    rw [h1, h2, hmuW _ (h t)]
  have hP0 : P = 0 := Polynomial.funext fun t => by rw [hPeval t, Polynomial.eval_zero]
  have hcoeff : P.coeff k = mu (c k) := by
    rw [hP, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Polynomial.coeff_X_pow, Ne.symm hj]
    · intro hk'
      exact absurd (Finset.mem_range.mpr hk) hk'
  rw [hP0, Polynomial.coeff_zero, hmuk] at hcoeff
  exact zero_ne_one hcoeff
