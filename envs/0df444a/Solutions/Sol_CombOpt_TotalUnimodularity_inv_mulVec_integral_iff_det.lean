-- Prove2me | solution 1 for CombOpt.TotalUnimodularity.inv_mulVec_integral_iff_det
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:12:27.575911+00:00
-- url     : https://prove2.me/submissions/51ab54fb-77cb-4065-94b6-530faa9257e8

import Mathlib

open Matrix

theorem solution {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ)
    (hA : (A.map (Int.cast : ℤ → ℝ)).det ≠ 0) :
    (∀ b : Fin m → ℤ, ∃ z : Fin m → ℤ,
        (A.map (Int.cast : ℤ → ℝ))⁻¹ *ᵥ (fun i => (b i : ℝ)) = fun i => (z i : ℝ)) ↔
      (A.det = 1 ∨ A.det = -1) := by
  constructor
  · intro h
    choose z hz using fun k : Fin m => h (Pi.single k 1)
    let B : Matrix (Fin m) (Fin m) ℤ := fun r k => z k r
    have hcol : ∀ r k, (A.map (Int.cast : ℤ → ℝ))⁻¹ r k = (z k r : ℝ) := by
      intro r k
      have := congrFun (hz k) r
      rw [← this]
      have e : (fun i => ((Pi.single k (1 : ℤ) : Fin m → ℤ) i : ℝ)) = Pi.single k (1 : ℝ) := by
        funext i
        by_cases hik : i = k
        · subst hik; simp
        · simp [Pi.single_apply, hik]
      rw [e]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hinvB : (A.map (Int.cast : ℤ → ℝ))⁻¹ = B.map (Int.cast : ℤ → ℝ) := by
      ext r k
      rw [hcol]
      rfl
    have hAB : A.map (Int.cast : ℤ → ℝ) * B.map (Int.cast : ℤ → ℝ) = 1 := by
      rw [← hinvB]
      exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA)
    have hAB' : A * B = 1 := by
      apply Matrix.map_injective (f := (Int.cast : ℤ → ℝ)) Int.cast_injective
      show (A * B).map (Int.castRingHom ℝ) = (1 : Matrix (Fin m) (Fin m) ℤ).map (Int.castRingHom ℝ)
      rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      exact hAB
    have hu : IsUnit A.det :=
      IsUnit.of_mul_eq_one B.det (by rw [← Matrix.det_mul, hAB', Matrix.det_one])
    exact Int.isUnit_iff.mp hu
  · intro hdet
    have hd2 : A.det * A.det = 1 := by
      rcases hdet with h | h <;> rw [h] <;> norm_num
    have hB : (A.det • A.adjugate).map (Int.castRingHom ℝ) * A.map (Int.castRingHom ℝ) = 1 := by
      rw [← Matrix.map_mul, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, hd2, one_smul,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have hinv : (A.map (Int.cast : ℤ → ℝ))⁻¹ = (A.det • A.adjugate).map (Int.castRingHom ℝ) :=
      Matrix.inv_eq_left_inv hB
    intro b
    refine ⟨(A.det • A.adjugate) *ᵥ b, ?_⟩
    rw [hinv]
    funext r
    exact (RingHom.map_mulVec (Int.castRingHom ℝ) _ b r).symm
