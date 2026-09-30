-- Prove2me | solution 1 for BurauFaithful.sl2_normal_form_base
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T06:18:09.120782+00:00
-- url     : https://prove2.me/submissions/bf7e6685-2642-4fce-be41-fbd3568fa8ff

/-
`BurauFaithful.sl2_normal_form_base`: the terminal case of the Euclidean descent for `SL(2,ℤ)`.

The descent of `BurauFaithful.sl2_euclid_step` decreases `|M 0 0|` and stops when `M 0 0 = 0`. For
a matrix of determinant `1` this terminal case is completely described: `M = ± S · T^k`, since
`M 0 1 * M 1 0 = -1` forces `(M 0 1, M 1 0) = (1, -1)` or `(-1, 1)`.

Together with `BurauFaithful.modular_T_zpow_mul` and `BurauFaithful.sl2_euclid_step` this gives the
matrix side of the continued-fraction normal form `M = ±S^{ε}T^{a₁}ST^{a₂}⋯` used for the
Coxeter–Moser presentation of the modular group (Birman, *Braids, Links, and Mapping Class Groups*,
Ann. of Math. Studies 82, §3.3, pp. 129-130).
-/
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open Matrix

theorem solution (M : Matrix (Fin 2) (Fin 2) ℤ) (hd : M.det = 1) (h : M 0 0 = 0) :
    ∃ k : ℤ, M = (↑ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) *
          (↑(ModularGroup.T ^ k) : Matrix (Fin 2) (Fin 2) ℤ) ∨
      M = -((↑ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) *
          (↑(ModularGroup.T ^ k) : Matrix (Fin 2) (Fin 2) ℤ)) := by
  have hdet : M 0 1 * M 1 0 = -1 := by
    have h2 : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
      simpa [Matrix.det_fin_two] using hd
    rw [h] at h2
    simp only [zero_mul, zero_sub] at h2
    linarith
  have hone : M 0 1 * (-(M 1 0)) = 1 := by
    rw [mul_neg, hdet]
    ring
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hone with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h10 : M 1 0 = -1 := by linarith
    refine ⟨-(M 1 1), Or.inr ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ModularGroup.coe_S, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two,
        h, h1, h10] <;>
      ring
  · have h10 : M 1 0 = 1 := by linarith
    refine ⟨M 1 1, Or.inl ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ModularGroup.coe_S, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two,
        h, h1, h10] <;>
      ring
