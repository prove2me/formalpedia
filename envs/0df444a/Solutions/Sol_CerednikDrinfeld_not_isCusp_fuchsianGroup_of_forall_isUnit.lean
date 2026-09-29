-- Prove2me | solution 1 for CerednikDrinfeld.not_isCusp_fuchsianGroup_of_forall_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/5e042483-fdd1-591c-871c-31bc88918308

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_not_isCusp_fuchsianGroup_of_forall_isUnit

set_option autoImplicit false

open scoped Quaternion MatrixGroups TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

namespace NoCuspBody

variable {a b : ℚ}

theorem mul_self_eq (u : ℍ[ℚ, a, b]) :
    u * u = (trd u) • u - (nrd u) • (1 : ℍ[ℚ, a, b]) := by
  ext <;> simp [QuaternionAlgebra.nrd, QuaternionAlgebra.trd] <;> ring

theorem not_isParabolic (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (u : ℍ[ℚ, a, b]) : ¬ (ι u).IsParabolic := by
  intro hp
  obtain ⟨c, n, hmn, hn0, hnsq⟩ := Matrix.isParabolic_iff_exists.mp hp
  set t : ℝ := algebraMap ℚ ℝ (trd u) with ht
  set s : ℝ := algebraMap ℚ ℝ (nrd u) with hs
  have hq1 : ι u * ι u = t • ι u - s • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [← map_mul, mul_self_eq, map_sub, map_smul, map_smul, map_one, ht, hs,
      algebraMap_smul, algebraMap_smul]
  have hsc : Matrix.scalar (Fin 2) c = c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hn : n = ι u - c • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [hmn, hsc]; abel
  have hq2 : ι u * ι u = (2 * c) • ι u - (c ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    have h2 : (ι u - c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * (ι u - c • 1) = 0 := by
      rw [← hn, ← sq]; exact hnsq
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at h2
    rw [← sub_eq_zero, ← h2]
    module
  have hlin : (t - 2 * c) • ι u = (s - c ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    linear_combination (norm := module) hq2 - hq1
  by_cases htc : t - 2 * c = 0
  · have hc : c = algebraMap ℚ ℝ u.re := by
      have : t = 2 * algebraMap ℚ ℝ u.re := by
        rw [ht, QuaternionAlgebra.trd, map_mul, map_ofNat]
      linarith
    set w : ℍ[ℚ, a, b] := u - u.re • (1 : ℍ[ℚ, a, b]) with hw
    have hnw : n = ι w := by
      rw [hn, hw, map_sub, map_smul, map_one, hc, algebraMap_smul]
    have hww : w * w = 0 := hι (by rw [map_mul, ← hnw, map_zero, ← sq, hnsq])
    have hw0 : w = 0 := by
      by_contra hw0
      exact hw0 ((hdiv w hw0).mul_right_eq_zero.mp hww)
    exact hn0 (by rw [hnw, hw0, map_zero])
  · apply hp.1
    refine ⟨(t - 2 * c)⁻¹ * (s - c ^ 2), ?_⟩
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, ← smul_smul, ← hlin, smul_smul,
      inv_mul_cancel₀ htc, one_smul]

end NoCuspBody

open NoCuspBody in
theorem solution {a b : ℚ}
    (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)
    (hι : Function.Injective ι) (c : OnePoint ℝ) :
    ¬ IsCusp c (fuchsianGroup R ι) := by
  rintro ⟨g, hg, hpar, -⟩
  obtain ⟨hgmap, -⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.mp hgmap
  exact not_isParabolic hdiv ι hι (v : ℍ[ℚ, a, b]) (by exact hpar)

end S_CerednikDrinfeld_not_isCusp_fuchsianGroup_of_forall_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_not_isCusp_fuchsianGroup_of_forall_isUnit (solution)
