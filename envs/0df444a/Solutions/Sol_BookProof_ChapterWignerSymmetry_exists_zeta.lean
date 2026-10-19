-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.exists_zeta
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T09:58:25.008993+00:00
-- url     : https://prove2.me/submissions/98bae4d8-4a14-4d59-9ff4-a1b805abac5f

-- Generated from ChapterWignerSymmetry.lean — solution of BookProof.ChapterWignerSymmetry.exists_zeta
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
import Theorems.Thm_BookProof_ChapterWignerSymmetry_sum_pair_prime
import Theorems.Thm_BookProof_ChapterWignerSymmetry_S_zero
import Theorems.Thm_BookProof_ChapterWignerSymmetry_modulus_add
import Definitions.Def_ChapterWignerSymmetryInfinite
open BookProof.ChapterWignerSymmetry



open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {T : E → E}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

set_option maxHeartbeats 1000000 in
theorem solution (hS : WignerCoord S o) {i : ι} (hi : i ≠ o) :
    ∃ ζ : ℂ, (ζ = Complex.I ∨ ζ = -Complex.I) ∧
      ∀ v, ‖conj (S v o) + ζ * conj (S v i)‖ = ‖conj (v o) + Complex.I * conj (v i)‖ := by

  set w := pairCoordI o i with hw
  have hwo : w o = 1 := by simp [hw, pairCoordI]
  have hwi : w i = Complex.I := by simp [hw, pairCoordI, hi]
  have hwk : ∀ k, k ≠ o → k ≠ i → w k = 0 := by
    intro k h1 h2; simp [hw, pairCoordI, h1, h2]
  have hSw : ∀ k, k ≠ o → k ≠ i → S w k = 0 := fun k h1 h2 => S_zero hS (hwk k h1 h2)
  have hP : ‖S w o‖ = 1 := by rw [hS.coord_norm w o, hwo]; simp
  have hQ : ‖S w i‖ = 1 := by rw [hS.coord_norm w i, hwi]; simp
  -- the relative phase
  set P := S w o with hPdef
  set Q := S w i with hQdef
  have hsum : ‖P + Q‖ = ‖(1 : ℂ) + Complex.I‖ := by
    have := modulus_add hS hi w
    rwa [hwo, hwi] at this
  have hζnorm : ‖conj P * Q‖ = 1 := by rw [norm_mul, Complex.norm_conj, hP, hQ, mul_one]
  have hζre : (conj P * Q).re = 0 := by
    have h1 : ‖P + Q‖ ^ 2 = ‖(1 : ℂ) + Complex.I‖ ^ 2 := by rw [hsum]
    have hP2 : ‖P‖ ^ 2 = 1 := by rw [hP]; norm_num
    have hQ2 : ‖Q‖ ^ 2 = 1 := by rw [hQ]; norm_num
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im] at h1 hP2 hQ2
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    nlinarith [h1, hP2, hQ2]
  have hζ : conj P * Q = Complex.I ∨ conj P * Q = -Complex.I := by
    set z := conj P * Q with hz
    have him : z.im = 1 ∨ z.im = -1 := by
      have h2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [hζnorm, hζre] at h2
      have hfac : (z.im - 1) * (z.im + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 hfac with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases him with h | h
    · left; apply Complex.ext <;> simp [hζre, h]
    · right; apply Complex.ext <;> simp [hζre, h]
  refine ⟨conj P * Q, hζ, fun v => ?_⟩
  have h := hS.inner_norm v w
  rw [sum_pair_prime hi hSw, sum_pair_prime hi hwk, hwo, hwi] at h
  have hPP : P * conj P = 1 := by
    rw [Complex.mul_conj]
    have hsq : Complex.normSq P = ‖P‖ ^ 2 := by rw [Complex.sq_norm]
    rw [hsq, hP]
    norm_num
  have hPQ : conj (S v o) * P + conj (S v i) * Q
      = P * (conj (S v o) + (conj P * Q) * conj (S v i)) := by
    calc conj (S v o) * P + conj (S v i) * Q
        = P * conj (S v o) + (P * conj P) * (Q * conj (S v i)) := by rw [hPP]; ring
      _ = P * (conj (S v o) + (conj P * Q) * conj (S v i)) := by ring
  rw [hPQ, norm_mul, hP, one_mul] at h
  rw [h]
  congr 1
  ring
