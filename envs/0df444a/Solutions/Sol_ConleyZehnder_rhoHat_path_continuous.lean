-- Prove2me | solution 1 for ConleyZehnder.rhoHat_path_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T20:49:02.933528+00:00
-- url     : https://prove2.me/submissions/a31c63aa-15ff-4dc0-b980-45f097a3f475

import Theorems.Thm_ConleyZehnder_complexLinearDet_ne_zero

open ConleyZehnder Matrix

theorem solution {n : ℕ} (χ : C(unitInterval, Mat n))
    (hχ : ∀ t, IsSymplectic (χ t)) :
    Continuous (fun t => rhoHat (χ t)) ∧ ∀ t, ‖rhoHat (χ t)‖ = 1 := by
  have hC : Continuous (complexLinearPart : Mat n → Mat n) := by
    unfold complexLinearPart
    fun_prop
  have hdet : Continuous fun A : Mat n => complexLinearDet A := by
    unfold complexLinearDet
    refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₁, Matrix.of_apply, smul_eq_mul]
    exact (Complex.continuous_ofReal.comp (hC.matrix_elem _ _)).add
      (continuous_const.mul (Complex.continuous_ofReal.comp (hC.matrix_elem _ _)))
  have hd : Continuous fun t => complexLinearDet (χ t) := hdet.comp χ.continuous
  have hne : ∀ t, complexLinearDet (χ t) ≠ 0 := fun t => complexLinearDet_ne_zero _ (hχ t)
  refine ⟨?_, fun t => ?_⟩
  · unfold rhoHat
    refine hd.div (Complex.continuous_ofReal.comp hd.norm) fun t => ?_
    exact_mod_cast (norm_ne_zero_iff.2 (hne t))
  · unfold rhoHat
    rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 (hne t))]
