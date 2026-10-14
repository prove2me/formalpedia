-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.wignerCoord_coordMap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:05:59.810862+00:00
-- url     : https://prove2.me/submissions/7ffa34f5-672a-4e09-98e9-e854ac8bd7dd

-- Generated from ChapterWignerSymmetry.lean — solution of BookProof.ChapterWignerSymmetry.wignerCoord_coordMap
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
import Theorems.Thm_BookProof_ChapterWignerSymmetry_inner_basis_sum
import Theorems.Thm_BookProof_ChapterWignerSymmetry_inner_sum_smul
import Theorems.Thm_BookProof_ChapterWignerSymmetry_sum_pairCoord
import Theorems.Thm_BookProof_ChapterWignerSymmetry_alignPhase_self
import Theorems.Thm_BookProof_ChapterWignerSymmetry_imgBasis_apply
open BookProof.ChapterWignerSymmetry



open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {T : E → E}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}
variable {b : OrthonormalBasis ι ℂ E} {o : ι}

set_option maxHeartbeats 1000000 in
theorem solution (hT : IsWignerSymmetry T) :
    WignerCoord (coordMap b T (imgBasis b T o hT)) o := by

  set G := imgBasis b T o hT with hG
  constructor
  · intro v w
    have h1 : ∑ k, conj (coordMap b T G v k) * coordMap b T G w k
        = ⟪T (∑ j, v j • b j), T (∑ j, w j • b j)⟫_ℂ := by
      rw [← G.sum_inner_mul_inner (T (∑ j, v j • b j)) (T (∑ j, w j • b j))]
      exact Finset.sum_congr rfl fun k _ => by
        rw [coordMap, coordMap, inner_conj_symm]
    rw [h1, hT, inner_sum_smul]
  · intro v k
    have h1 : coordMap b T G v k
        = conj (alignPhase b T o k) * ⟪T (b k), T (∑ j, v j • b j)⟫_ℂ := by
      rw [coordMap, hG, imgBasis_apply hT, inner_smul_left]
    rw [h1, norm_mul, Complex.norm_conj, alignPhase_norm hT, one_mul, hT, inner_basis_sum]
  · intro i hi
    have hA : ‖⟪T (b o), T (b o + b i)⟫_ℂ‖ = 1 := inner_pair_left_norm hT hi
    have hB : ‖⟪T (b i), T (b o + b i)⟫_ℂ‖ = 1 := inner_pair_right_norm hT hi
    set A := ⟪T (b o), T (b o + b i)⟫_ℂ with hAdef
    set B := ⟪T (b i), T (b o + b i)⟫_ℂ with hBdef
    have hAne : A ≠ 0 := by intro h; rw [h] at hA; simp at hA
    have hcA : conj A ≠ 0 := by simpa using hAne
    have hAc : A * conj A = 1 := by
      rw [Complex.mul_conj]
      have hsq : Complex.normSq A = ‖A‖ ^ 2 := by rw [Complex.sq_norm]
      rw [hsq, hA]; norm_num
    have hBc : conj B * B = 1 := by
      rw [mul_comm, Complex.mul_conj]
      have hsq : Complex.normSq B = ‖B‖ ^ 2 := by rw [Complex.sq_norm]
      rw [hsq, hB]; norm_num
    have hLHS : coordMap b T G (pairCoord o i) o = A := by
      rw [coordMap, sum_pairCoord b hi, hG, imgBasis_apply hT, inner_smul_left,
        alignPhase_self]
      simp [hAdef]
    have hRHS : coordMap b T G (pairCoord o i) i = conj (B / A) * B := by
      rw [coordMap, sum_pairCoord b hi, hG, imgBasis_apply hT, inner_smul_left, alignPhase]
      rw [if_neg hi]
    rw [hLHS, hRHS, map_div₀]
    field_simp
    calc A * conj A = 1 := hAc
      _ = conj B * B := hBc.symm
