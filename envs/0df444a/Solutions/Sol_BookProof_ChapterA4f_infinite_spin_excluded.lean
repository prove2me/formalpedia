-- Prove2me | solution 1 for BookProof.ChapterA4f.infinite_spin_excluded
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:08:20.946889+00:00
-- url     : https://prove2.me/submissions/11dd49f8-a054-4857-bf32-5743405afe12

-- Generated from ChapterA4f.lean — theorem BookProof.ChapterA4f.infinite_spin_excluded
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA5
import Mathlib
import Definitions.Def_ChapterA4f
import Definitions.Def_ChapterA4d
open BookProof.ChapterA4f


open Matrix
open scoped ComplexConjugate


open BookProof.ChapterA3 BookProof.ChapterA5

theorem solution {T : Matrix (Fin 2) (Fin 2) ℂ} (hT : T ∈ SEtwo)
    (hc : T 1 0 ≠ 0) :
    ∀ c : ℂ, c ≠ 0 → ∃ l : ℂ, l ≠ 0 ∧ boostZ l * T * boostZ l⁻¹ ∈ SEtwo ∧
      (boostZ l * T * boostZ l⁻¹) 1 0 = c := by
  intro c hc'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (c / T 1 0) (by decide : 0 < (2 : ℕ))
  have hzne : z ≠ 0 := by
    intro h
    have : c / T 1 0 = 0 := by simpa [h] using hz.symm
    exact (div_ne_zero hc' hc) this
  refine ⟨z⁻¹, inv_ne_zero hzne, ?_, ?_⟩
  · rcases hT with ⟨hd, hzero, hn⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.det_mul, Matrix.det_mul, hd]
      simp [boostZ, Matrix.det_fin_two, hzne]
    · simp [boostZ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hzero]
    · convert hn using 1
      congr 1
      simp [boostZ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
      field_simp
  · simp [boostZ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    calc
      z * T 1 0 * z = z ^ 2 * T 1 0 := by ring
      _ = c := by rw [hz]; exact div_mul_cancel₀ c hc

#print axioms solution
