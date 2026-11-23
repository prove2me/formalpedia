-- Prove2me | solution 1 for EquivarianceConvolution.irrep_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T21:10:36.38253+00:00
-- url     : https://prove2.me/submissions/680d8af0-a805-42b7-98c9-3f93d50cbb58

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

open scoped BigOperators
namespace EquivarianceConvolution


theorem irrep_sum_eq_zero {G : Type*} [Group G] [Fintype G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : IsIrrep ρ) (htr : ¬ IsTrivialRep ρ) :
    ∑ u, ρ u = 0 := by
  classical
  set P : Matrix (Fin n) (Fin n) ℂ := ∑ u, ρ u with hPdef
  have hP : ∀ g, ρ g * P = P := by
    intro g
    rw [hPdef, Finset.mul_sum]
    simp only [← map_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)
  by_contra hne
  have hinv : ∀ g ∈ (Set.univ : Set G), ∀ w ∈ LinearMap.range (Matrix.mulVecLin P),
      Matrix.mulVec (ρ g) w ∈ LinearMap.range (Matrix.mulVecLin P) := by
    rintro g - w ⟨x, rfl⟩
    exact ⟨x, by simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP]⟩
  rcases hρ.2 _ hinv with h | h
  · apply hne
    ext i j
    have hm : P.mulVec (Pi.single j 1) = 0 := by
      have : P.mulVec (Pi.single j 1) ∈ LinearMap.range (Matrix.mulVecLin P) := ⟨_, rfl⟩
      rw [h] at this
      exact (Submodule.mem_bot ℂ).mp this
    have := congrFun hm i
    simpa [Matrix.mulVec_single] using this
  · have h1 : ∀ g, ρ g = 1 := by
      intro g
      have hy : ∀ y : Fin n → ℂ, (ρ g).mulVec y = y := by
        intro y
        have : y ∈ LinearMap.range (Matrix.mulVecLin P) := by rw [h]; trivial
        obtain ⟨x, rfl⟩ := this
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP]
      ext i j
      have := congrFun (hy (Pi.single j 1)) i
      simpa [Matrix.mulVec_single, Matrix.one_apply, Pi.single_apply, eq_comm] using this
    apply htr
    refine ⟨?_, h1⟩
    obtain ⟨i0⟩ := hρ.1
    have hv : (Pi.single i0 (1:ℂ) : Fin n → ℂ) ≠ 0 := by
      intro h0; have := congrFun h0 i0; simp at this
    rcases hρ.2 (Submodule.span ℂ {Pi.single i0 (1:ℂ)}) (by
        intro g _ w hw; show (ρ g).mulVec w ∈ _; rw [h1 g, Matrix.one_mulVec]; exact hw) with h2 | h2
    · exact absurd ((Submodule.span_singleton_eq_bot).mp h2) hv
    · have := finrank_span_singleton (K := ℂ) hv
      rw [h2, finrank_top, Module.finrank_fin_fun] at this
      exact this


end EquivarianceConvolution

open EquivarianceConvolution in
theorem solution {G : Type*} [Group G] [Fintype G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : IsIrrep ρ) (htr : ¬ IsTrivialRep ρ) :
    ∑ u, ρ u = 0 := by
  classical
  set P : Matrix (Fin n) (Fin n) ℂ := ∑ u, ρ u with hPdef
  have hP : ∀ g, ρ g * P = P := by
    intro g
    rw [hPdef, Finset.mul_sum]
    simp only [← map_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)
  by_contra hne
  have hinv : ∀ g ∈ (Set.univ : Set G), ∀ w ∈ LinearMap.range (Matrix.mulVecLin P),
      Matrix.mulVec (ρ g) w ∈ LinearMap.range (Matrix.mulVecLin P) := by
    rintro g - w ⟨x, rfl⟩
    exact ⟨x, by simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP]⟩
  rcases hρ.2 _ hinv with h | h
  · apply hne
    ext i j
    have hm : P.mulVec (Pi.single j 1) = 0 := by
      have : P.mulVec (Pi.single j 1) ∈ LinearMap.range (Matrix.mulVecLin P) := ⟨_, rfl⟩
      rw [h] at this
      exact (Submodule.mem_bot ℂ).mp this
    have := congrFun hm i
    simpa [Matrix.mulVec_single] using this
  · have h1 : ∀ g, ρ g = 1 := by
      intro g
      have hy : ∀ y : Fin n → ℂ, (ρ g).mulVec y = y := by
        intro y
        have : y ∈ LinearMap.range (Matrix.mulVecLin P) := by rw [h]; trivial
        obtain ⟨x, rfl⟩ := this
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP]
      ext i j
      have := congrFun (hy (Pi.single j 1)) i
      simpa [Matrix.mulVec_single, Matrix.one_apply, Pi.single_apply, eq_comm] using this
    apply htr
    refine ⟨?_, h1⟩
    obtain ⟨i0⟩ := hρ.1
    have hv : (Pi.single i0 (1:ℂ) : Fin n → ℂ) ≠ 0 := by
      intro h0; have := congrFun h0 i0; simp at this
    rcases hρ.2 (Submodule.span ℂ {Pi.single i0 (1:ℂ)}) (by
        intro g _ w hw; show (ρ g).mulVec w ∈ _; rw [h1 g, Matrix.one_mulVec]; exact hw) with h2 | h2
    · exact absurd ((Submodule.span_singleton_eq_bot).mp h2) hv
    · have := finrank_span_singleton (K := ℂ) hv
      rw [h2, finrank_top, Module.finrank_fin_fun] at this
      exact this

