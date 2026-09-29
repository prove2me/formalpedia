-- Prove2me | solution 1 for CerednikDrinfeld.det_map_eq_nrd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/df58b5c7-6a18-50fe-b687-6d3564017957

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_det_map_eq_nrd

set_option autoImplicit false

open scoped Quaternion MatrixGroups TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

namespace DetNrdBody

variable {a b : ℚ}

theorem mul_self_eq (u : ℍ[ℚ, a, b]) :
    u * u = (trd u) • u - (nrd u) • (1 : ℍ[ℚ, a, b]) := by
  ext <;> simp [QuaternionAlgebra.nrd, QuaternionAlgebra.trd] <;> ring

theorem cayley_hamilton_two (m : Matrix (Fin 2) (Fin 2) ℝ) :
    m * m = m.trace • m - m.det • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

end DetNrdBody

open DetNrdBody in
theorem solution {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (x : ℍ[ℚ, a, b]) : (ι x).det = ((nrd x : ℚ) : ℝ) := by
  set t : ℝ := algebraMap ℚ ℝ (trd x) with ht
  set s : ℝ := algebraMap ℚ ℝ (nrd x) with hs
  have hs' : ((nrd x : ℚ) : ℝ) = s := by rw [hs, eq_ratCast]
  have hq1 : ι x * ι x = t • ι x - s • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [← map_mul, mul_self_eq, map_sub, map_smul, map_smul, map_one, ht, hs,
      algebraMap_smul, algebraMap_smul]
  have hCH := cayley_hamilton_two (ι x)
  have hlin : ((ι x).trace - t) • ι x = ((ι x).det - s) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    linear_combination (norm := module) hq1 - hCH
  rw [hs']
  by_cases htr : (ι x).trace - t = 0
  · rw [htr, zero_smul] at hlin
    have h := (smul_eq_zero.mp hlin.symm).resolve_right one_ne_zero
    exact sub_eq_zero.mp h
  ·
    have hsc : ι x = (((ι x).trace - t)⁻¹ * ((ι x).det - s)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      calc ι x = ((ι x).trace - t)⁻¹ • (((ι x).trace - t) • ι x) := by
            rw [smul_smul, inv_mul_cancel₀ htr, one_smul]
        _ = _ := by rw [hlin, smul_smul]
    have hcomm : ∀ y : ℍ[ℚ, a, b], x * y = y * x := fun y =>
      hι (by rw [map_mul, map_mul, hsc, smul_mul_assoc, mul_smul_comm, one_mul, mul_one])
    have h1 := hcomm ⟨0, 1, 0, 0⟩
    have h2 := hcomm ⟨0, 0, 1, 0⟩
    have e1 := congrArg QuaternionAlgebra.imJ h1
    have e2 := congrArg QuaternionAlgebra.imK h1
    have e3 := congrArg QuaternionAlgebra.imK h2
    simp at e1 e2 e3
    have hK0 : x.imK = 0 := by
      have : a * x.imK = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left ha
    have hJ0 : x.imJ = 0 := by linarith
    have hI0 : x.imI = 0 := by linarith
    have hx : x = ((x.re : ℚ) : ℍ[ℚ, a, b]) := by ext <;> simp [hI0, hJ0, hK0]
    have hn : nrd x = x.re ^ 2 := by
      rw [show nrd x = nrd ((x.re : ℚ) : ℍ[ℚ, a, b]) from congrArg nrd hx, nrd_coe]
    have hιx : ι x = ((x.re : ℚ) : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      conv_lhs => rw [hx]
      rw [show ((x.re : ℚ) : ℍ[ℚ, a, b]) = algebraMap ℚ ℍ[ℚ, a, b] x.re from rfl, AlgHom.commutes,
        Algebra.algebraMap_eq_smul_one, ← Rat.cast_smul_eq_qsmul ℝ]
    rw [← hs', hιx, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hn]
    push_cast
    ring

end S_CerednikDrinfeld_det_map_eq_nrd
end P2MW
export P2MW.S_CerednikDrinfeld_det_map_eq_nrd (solution)
