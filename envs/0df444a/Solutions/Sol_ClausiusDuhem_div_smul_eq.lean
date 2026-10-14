-- Prove2me | solution 1 for ClausiusDuhem.div_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T06:06:57.616133+00:00
-- url     : https://prove2.me/submissions/b2c7b517-8723-47cc-aa22-fa1b16c47da4

import Definitions.Def_ClausiusDuhem_field_calculus
set_option autoImplicit false
open ClausiusDuhem

theorem solution (φ : Space → ℝ) (v : Space → Fin 3 → ℝ) (x : Space)
    (hφ : DifferentiableAt ℝ φ x) (hv : DifferentiableAt ℝ v x) :
    div (fun y => φ y • v y) x = φ x * div v x + dot (v x) (grad φ x) := by
  have hc (j : Fin 3) : DifferentiableAt ℝ (fun y => v y j) x :=
    differentiableAt_pi.mp hv j
  have hp (j : Fin 3) : partialDeriv (fun y => (φ y • v y) j) j x =
      φ x * partialDeriv (fun y => v y j) j x + v x j * partialDeriv φ j x := by
    have he := (hφ.hasFDerivAt.mul (hc j).hasFDerivAt).fderiv
    change fderiv ℝ (fun y => φ y * v y j) x = _ at he
    unfold partialDeriv
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [he]
    simp [smul_eq_mul]
  simp only [div, hp, Finset.sum_add_distrib, ← Finset.mul_sum, dot, grad]

#print axioms solution
