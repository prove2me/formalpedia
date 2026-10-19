-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.key_consistent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T09:58:39.987949+00:00
-- url     : https://prove2.me/submissions/b819d29a-c07b-45e5-9003-ed6c4c88c295

-- Generated from ChapterWignerSymmetry.lean — solution of BookProof.ChapterWignerSymmetry.key_consistent
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
import Theorems.Thm_BookProof_ChapterWignerSymmetry_sum_triple
import Theorems.Thm_BookProof_ChapterWignerSymmetry_S_zero
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
theorem solution (hS : WignerCoord S o) {i j : ι} (hio : i ≠ o) (hjo : j ≠ o) (hij : i ≠ j)
    (hi : ∀ v, conj (S v o) * S v i = conj (v o) * v i)
    (hj : ∀ v, conj (S v o) * S v j = conj (conj (v o) * v j)) : False := by

  set v := tripleCoord o i j 1 with hv
  set w := tripleCoord o i j Complex.I with hw
  have hvo : v o = 1 := by simp [hv, tripleCoord]
  have hvi : v i = 1 := by simp [hv, tripleCoord, hio]
  have hvj : v j = 1 := by simp [hv, tripleCoord, hjo, Ne.symm hij]
  have hvk : ∀ k, k ≠ o → k ≠ i → k ≠ j → v k = 0 := by
    intro k h1 h2 h3; simp [hv, tripleCoord, h1, h2, h3]
  have hwo : w o = 1 := by simp [hw, tripleCoord]
  have hwi : w i = Complex.I := by simp [hw, tripleCoord, hio]
  have hwj : w j = Complex.I := by simp [hw, tripleCoord, hjo, Ne.symm hij]
  have hwk : ∀ k, k ≠ o → k ≠ i → k ≠ j → w k = 0 := by
    intro k h1 h2 h3; simp [hw, tripleCoord, h1, h2, h3]
  have hSw : ∀ k, k ≠ o → k ≠ i → k ≠ j → S w k = 0 :=
    fun k h1 h2 h3 => S_zero hS (hwk k h1 h2 h3)
  -- the images of `v` and `w`
  have hp : ‖S v o‖ = 1 := by rw [hS.coord_norm v o, hvo]; simp
  have hq : ‖S w o‖ = 1 := by rw [hS.coord_norm w o, hwo]; simp
  have hpp : S v o * conj (S v o) = 1 := by
    rw [Complex.mul_conj]
    have hsq : Complex.normSq (S v o) = ‖S v o‖ ^ 2 := by rw [Complex.sq_norm]
    rw [hsq, hp]; norm_num
  have hqq : S w o * conj (S w o) = 1 := by
    rw [Complex.mul_conj]
    have hsq : Complex.normSq (S w o) = ‖S w o‖ ^ 2 := by rw [Complex.sq_norm]
    rw [hsq, hq]; norm_num
  have hvi' : S v i = S v o := by
    have h := hi v
    rw [hvo, hvi] at h
    calc S v i = (S v o * conj (S v o)) * S v i := by rw [hpp]; ring
      _ = S v o * (conj (S v o) * S v i) := by ring
      _ = S v o := by rw [h]; simp
  have hvj' : S v j = S v o := by
    have h := hj v
    rw [hvo, hvj] at h
    calc S v j = (S v o * conj (S v o)) * S v j := by rw [hpp]; ring
      _ = S v o * (conj (S v o) * S v j) := by ring
      _ = S v o := by rw [h]; simp
  have hwi' : S w i = Complex.I * S w o := by
    have h := hi w
    rw [hwo, hwi] at h
    calc S w i = (S w o * conj (S w o)) * S w i := by rw [hqq]; ring
      _ = S w o * (conj (S w o) * S w i) := by ring
      _ = Complex.I * S w o := by rw [h]; simp; ring
  have hwj' : S w j = -Complex.I * S w o := by
    have h := hj w
    rw [hwo, hwj] at h
    calc S w j = (S w o * conj (S w o)) * S w j := by rw [hqq]; ring
      _ = S w o * (conj (S w o) * S w j) := by ring
      _ = -Complex.I * S w o := by rw [h]; simp; ring
  -- compare the two transition probabilities
  have h := hS.inner_norm v w
  rw [sum_triple hio hjo hij hSw, sum_triple hio hjo hij hwk] at h
  rw [hvi', hvj', hwi', hwj', hvo, hvi, hvj, hwo, hwi, hwj] at h
  rw [show conj (S v o) * S w o + conj (S v o) * (Complex.I * S w o)
        + conj (S v o) * (-Complex.I * S w o) = conj (S v o) * S w o by ring] at h
  have h5 : ‖conj (S v o) * S w o‖ ^ 2
      = ‖conj (1 : ℂ) * 1 + conj (1 : ℂ) * Complex.I + conj (1 : ℂ) * Complex.I‖ ^ 2 := by
    rw [h]
  rw [norm_mul, Complex.norm_conj, hp, hq] at h5
  simp only [Complex.sq_norm, Complex.normSq_apply] at h5
  norm_num at h5
