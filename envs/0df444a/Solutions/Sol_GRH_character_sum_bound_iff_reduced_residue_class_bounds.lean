-- Prove2me | solution 1 for GRH.character_sum_bound_iff_reduced_residue_class_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:19:43.739938+00:00
-- url     : https://prove2.me/submissions/8c15d335-440f-4769-924e-6d0ea9db33b6

import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

open Filter Asymptotics

/-- Finite Fourier inversion identifies character-sum bounds with bounds on each reduced residue class. -/
theorem solution (q : ℕ) [NeZero q] (w : ℕ → ℂ) (g : ℕ → ℝ) :
    (∀ χ : DirichletCharacter ℂ q,
      (fun N : ℕ ↦ ∑ k ∈ Finset.range (N + 1), χ k * w k) =O[atTop] g) ↔
    (∀ a : ZMod q, IsUnit a →
      (fun N : ℕ ↦ ∑ k ∈ Finset.range (N + 1), if a = (k : ZMod q) then w k else 0) =O[atTop] g) := by
  classical
  let T (χ : DirichletCharacter ℂ q) (N : ℕ) := ∑ k ∈ Finset.range (N + 1), χ k * w k
  let R (a : ZMod q) (N : ℕ) := ∑ k ∈ Finset.range (N + 1), if a = (k : ZMod q) then w k else 0
  change (∀ χ, T χ =O[atTop] g) ↔ (∀ a, IsUnit a → R a =O[atTop] g)
  have sumBound {ι : Type} [Fintype ι] (F : ι → ℕ → ℂ) (h : ∀ i, F i =O[atTop] g) :
      (fun N ↦ ∑ i, F i N) =O[atTop] g := by
    have eq : (fun N ↦ ∑ i, F i N) = ∑ i, F i := by
      funext N
      simp only [Finset.sum_apply]
    rw [eq]
    exact IsBigO.sum (fun i _ ↦ h i)
  constructor
  · intro h a ha
    have hf (N : ℕ) : ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * T χ N = (q.totient : ℂ) * R a N := by
      simp only [T, R, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha]
      split_ifs <;> simp_all
    have hn : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
    have hinv : R a = fun N ↦ (q.totient : ℂ)⁻¹ * ∑ χ, χ a⁻¹ * T χ N := by
      funext N
      rw [hf N, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    rw [hinv]
    apply IsBigO.const_mul_left
    exact sumBound _ (fun χ ↦ (h χ).const_mul_left (χ a⁻¹))
  · intro h χ
    have hf : T χ = fun N ↦ ∑ a : ZMod q, χ a * R a N := by
      funext N
      simp only [T, R, Finset.mul_sum]
      rw [Finset.sum_comm (s := (Finset.univ : Finset (ZMod q)))]
      apply Finset.sum_congr rfl
      intro k _
      simp [mul_ite]
    rw [hf]
    have localBound (a : ZMod q) : (fun N ↦ χ a * R a N) =O[atTop] g := by
      by_cases ha : IsUnit a
      · exact (h a ha).const_mul_left _
      · simp only [χ.map_nonunit ha, zero_mul]
        exact isBigO_zero _ _
    exact sumBound _ localBound
