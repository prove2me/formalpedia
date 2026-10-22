-- Prove2me | solution 1 for DissipativePrep.Unique.one_qubit_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T21:55:05.628144+00:00
-- url     : https://prove2.me/submissions/811005a6-feec-4dce-ad64-be4f2b508b67

import Mathlib
import Definitions.Def_DissipativePrep_Unique_Model

open scoped Matrix
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P16 DissipativePrep.Unique in
theorem solution (g : ℝ) (hg : 0 < g) :
    let G := gkslGenerator (krausData (0 : Matrix (Fin 2) (Fin 2) ℂ) Matrix.isHermitian_zero
      ![!![0, 1; 0, 0]] ![g])
    G !![1, 0; 0, 0] = 0 ∧
    G !![1, 0; 0, -1] = ((-2 * g : ℝ) : ℂ) • !![1, 0; 0, -1] ∧
    G !![0, 1; 1, 0] = ((-g : ℝ) : ℂ) • !![0, 1; 1, 0] ∧
    G !![0, -Complex.I; Complex.I, 0] = ((-g : ℝ) : ℂ) • !![0, -Complex.I; Complex.I, 0] := by
  intro G
  set σ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0] with hσ
  set s : ℂ := ((Real.sqrt (2 * g) : ℝ) : ℂ) with hsdef
  have hs : s * s = 2 * (g : ℂ) := by
    rw [hsdef, ← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
  have hsc : star s = s := Complex.conj_ofReal _
  have hD : krausData (0 : Matrix (Fin 2) (Fin 2) ℂ) Matrix.isHermitian_zero ![!![0, 1; 0, 0]] ![g] =
      ⟨1, fun l => ((Real.sqrt (2 * (![g] : Fin 1 → ℝ) l) : ℝ) : ℂ) • (![!![0, 1; 0, 0]] : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ) l, 0,
        Matrix.isHermitian_zero⟩ := rfl
  have hG : ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
      G X = (2 * (g : ℂ)) • (σ * X * σᴴ) - (g : ℂ) • (σᴴ * σ * X) - (g : ℂ) • (X * (σᴴ * σ)) := by
    intro X
    simp only [G]
    rw [hD]
    simp only [gkslGenerator, cpGenerator, driftK, sandwich, LinearMap.sub_apply,
      LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, Fin.sum_univ_one, Matrix.cons_val_zero, ← hsdef, ← hσ]
    simp only [Matrix.conjTranspose_smul, hsc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs,
      smul_zero, zero_add, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.zero_mul, Matrix.mul_zero]
    have h12 : star ((1:ℂ) / 2 * (2 * (g : ℂ))) = (g : ℂ) := by
      rw [show (1:ℂ) / 2 * (2 * (g : ℂ)) = (g : ℂ) by ring]; exact Complex.conj_ofReal g
    rw [h12, show (1:ℂ) / 2 * (2 * (g : ℂ)) = (g : ℂ) by ring]
    simp only [Matrix.mul_assoc, smul_smul]
  have hσH : σᴴ = !![0, 0; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hσ]
  have hσσ : σᴴ * σ = !![0, 0; 0, 1] := by
    rw [hσH, hσ, Matrix.mul_fin_two]; simp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hG, hσσ, hσH, hσ] <;>
    simp only [Matrix.mul_fin_two, Matrix.smul_of, Matrix.of_sub_of] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> ring
