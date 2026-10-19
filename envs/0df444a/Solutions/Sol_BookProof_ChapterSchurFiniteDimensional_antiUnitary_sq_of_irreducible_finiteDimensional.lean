-- Prove2me | solution 1 for BookProof.ChapterSchurFiniteDimensional.antiUnitary_sq_of_irreducible_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:25:42.273197+00:00
-- url     : https://prove2.me/submissions/93581177-3a03-4c7b-a93f-557e09442986

-- Generated from ChapterSchurFiniteDimensional.lean — solution of BookProof.ChapterSchurFiniteDimensional.antiUnitary_sq_of_irreducible_finiteDimensional
import Mathlib
import Definitions.Def_ChapterSchurFiniteDimensional
import Theorems.Thm_BookProof_ChapterSchurFiniteDimensional_isSchurFull_of_irreducible_finiteDimensional
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterSchurFiniteDimensional



open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System
open BookProof.ChapterA
open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution [FiniteDimensional ℂ V] [Nontrivial V]
    (M : System ℂ V) (hirr : M.IsIrreducible) {θ : AntiUnitary V}
    (hθ : CommutesAntiUnitary M θ) :
    (∀ x, θ (θ x) = x) ∨ (∀ x, θ (θ x) = -x) := by

  have hcomm : M.Commutes (antiSq θ) := by
    intro m hm
    ext x
    have h1 : θ (m x) = m (θ x) := hθ m hm x
    have h2 : θ (m (θ x)) = m (θ (θ x)) := hθ m hm (θ x)
    simp only [ContinuousLinearMap.mul_apply, antiSq_apply]
    rw [h1, h2]
  obtain ⟨c, hc⟩ := isSchurFull_of_irreducible_finiteDimensional M hirr (antiSq θ) hcomm
  have hcx : ∀ x : V, θ (θ x) = c • x := by
    intro x
    have := congrArg (fun T : V →L[ℂ] V => T x) hc
    simpa using this
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
  have hθx₀ : θ x₀ ≠ 0 := by
    intro h
    exact hx₀ (θ.injective (by simpa using h : θ x₀ = θ 0))
  have hconj : conj c = c := by
    have h1 : θ (θ (θ x₀)) = conj c • θ x₀ := by
      calc θ (θ (θ x₀)) = θ (c • x₀) := by rw [hcx x₀]
        _ = conj c • θ x₀ := by rw [map_smulₛₗ]
    have h2 : θ (θ (θ x₀)) = c • θ x₀ := hcx (θ x₀)
    have h3 : (conj c - c) • θ x₀ = 0 := by
      rw [sub_smul, ← h1, h2]; simp
    rcases smul_eq_zero.mp h3 with h | h
    · linear_combination (norm := ring_nf) h
    · exact absurd h hθx₀
  have hnorm : ‖c‖ = 1 := by
    have hiso : ‖θ (θ x₀)‖ = ‖x₀‖ := by rw [θ.norm_map, θ.norm_map]
    rw [hcx x₀, norm_smul] at hiso
    have hx0 : ‖x₀‖ ≠ 0 := norm_ne_zero_iff.mpr hx₀
    field_simp at hiso
    exact hiso
  have hreal : c = 1 ∨ c = -1 := by
    have himzero : c.im = 0 := by
      have h := congrArg Complex.im hconj
      simp [Complex.conj_im] at h
      linarith
    have hc' : c = (c.re : ℂ) := Complex.ext rfl (by simp [himzero])
    rw [hc', Complex.norm_real, Real.norm_eq_abs] at hnorm
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hnorm with h | h
    · left; rw [hc', h]; norm_num
    · right; rw [hc', h]; norm_num
  rcases hreal with rfl | rfl
  · left; intro x; simpa using hcx x
  · right; intro x; simpa using hcx x
