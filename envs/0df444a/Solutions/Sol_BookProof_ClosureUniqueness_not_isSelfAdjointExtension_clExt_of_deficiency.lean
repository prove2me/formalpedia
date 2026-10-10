-- Prove2me | solution 1 for BookProof.ClosureUniqueness.not_isSelfAdjointExtension_clExt_of_deficiency
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:17:47.381262+00:00
-- url     : https://prove2.me/submissions/d2132145-06d2-4de0-8041-b13d9c6f4ab7

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.not_isSelfAdjointExtension_clExt_of_deficiency
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Theorems.Thm_BookProof_ClosureUniqueness_clGraph_inner_deficiency
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (T : D →ₗ[ℂ] F)
    (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) {w : F} (hw0 : w ≠ 0)
    (hw : ∀ v : D, (inner ℂ (T v) w : ℂ) = Complex.I * inner ℂ (v : F) w) :
    ¬ IsSelfAdjointExtension T (clExt T hdense hsym) := by

  rintro ⟨-, hsymA, hsa⟩
  have hpair : ∀ v : clDom T, (inner ℂ (clExt T hdense hsym v) w : ℂ)
      = inner ℂ (v : F) (Complex.I • w) := by
    intro v
    have h := clGraph_inner_deficiency hw (clFun_spec T v)
    simpa [inner_smul_right] using h
  obtain ⟨hwmem, hval⟩ := hsa w (Complex.I • w) hpair
  have hs := hsymA ⟨w, hwmem⟩ ⟨w, hwmem⟩
  rw [hval] at hs
  simp only [inner_smul_left, inner_smul_right, Complex.conj_I] at hs
  have hnorm : (inner ℂ w w : ℂ) = 0 := by
    have h2 : (2 * Complex.I) * (inner ℂ w w : ℂ) = 0 := by linear_combination -hs
    have hI : (2 * Complex.I : ℂ) ≠ 0 := by
      simp [Complex.I_ne_zero]
    exact (mul_eq_zero.mp h2).resolve_left hI
  exact hw0 (inner_self_eq_zero.mp hnorm)
