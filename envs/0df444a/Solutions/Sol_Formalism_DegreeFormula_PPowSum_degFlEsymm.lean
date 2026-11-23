-- Prove2me | solution 1 for Formalism.DegreeFormula.PPowSum.degFlEsymm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:19.195799+00:00
-- url     : https://prove2.me/submissions/3ced8fa7-716c-4bed-bff2-918a730653a0

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_degFlPowerSum
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_Z_mul_left
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_Z_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.DegreeFormula Formalism.DegreeFormula.PPowSum
open Formalism.DegreeFormula
namespace Formalism.DegreeFormula.PPowSum
theorem _root_.solution : DegFlEsymm := by
  intro ι _ _ N τ k P hk
  have hp : ∀ n, 1 ≤ n → ∀ P : MvPolynomial (ι × Fin N) ℝ,
      degFl ι N (rename (fun i : Fin N => (τ, i)) (psum (Fin N) ℝ n) * P) = 0 := by
    intro n hn P
    simp only [psum, map_sum, map_pow, rename_X]
    exact degFlPowerSum ι N τ n P hn
  have hZ : ∀ P : MvPolynomial (ι × Fin N) ℝ, degFl ι N (rename (fun i : Fin N => (τ, i))
      ((k : MvPolynomial (Fin N) ℝ) * esymm (Fin N) ℝ k) * P) = 0 := by
    rw [mul_esymm_eq_sum, map_mul]
    apply Z_mul_left
    rw [map_sum]
    apply Z_sum
    intro a ha
    rw [map_mul]
    apply Z_mul_left
    apply hp
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at ha1
    omega
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hCC : C (k : ℝ) * C (k : ℝ)⁻¹ = (1 : MvPolynomial (ι × Fin N) ℝ) := by
    rw [← map_mul, mul_inv_cancel₀ hk0, map_one]
  have e1 : rename (fun i : Fin N => (τ, i)) (esymm (Fin N) ℝ k) * P =
      rename (fun i : Fin N => (τ, i)) ((k : MvPolynomial (Fin N) ℝ) * esymm (Fin N) ℝ k) *
        (C (k : ℝ)⁻¹ * P) := by
    rw [map_mul, map_natCast, ← map_natCast (C : ℝ →+* MvPolynomial (ι × Fin N) ℝ) k]
    linear_combination (-(rename (fun i : Fin N => (τ, i)) (esymm (Fin N) ℝ k) * P)) * hCC
  rw [e1]
  exact hZ _
end Formalism.DegreeFormula.PPowSum
