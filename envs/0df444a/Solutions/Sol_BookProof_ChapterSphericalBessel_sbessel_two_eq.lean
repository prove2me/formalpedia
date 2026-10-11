-- Prove2me | solution 1 for BookProof.ChapterSphericalBessel.sbessel_two_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:32.927124+00:00
-- url     : https://prove2.me/submissions/a8eb6701-3f2a-42b3-ad28-093280c3e29c

-- Generated from ChapterSphericalBessel.lean — solution of BookProof.ChapterSphericalBessel.sbessel_two_eq
import Mathlib
import Definitions.Def_ChapterSphericalBessel
import Theorems.Thm_BookProof_ChapterSphericalBessel_deriv_sbesselBase
open BookProof.ChapterSphericalBessel




open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution {r : ℝ} (hr : r ≠ 0) : sbessel 2 r = sj2 r := by

  have hee : deriv (rayleighOp sbesselBase) r
      = deriv (fun x => -(1 / x) * (Real.cos x / x - Real.sin x / x ^ 2)) r := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [isOpen_ne.mem_nhds hr] with x hx
    simp only [rayleighOp, deriv_sbesselBase hx]
  have h2 : (rayleighOp^[2] sbesselBase) r
      = -(1 / r) * deriv (rayleighOp sbesselBase) r := rfl
  have hd2 : deriv (fun x => -(1 / x) * (Real.cos x / x - Real.sin x / x ^ 2)) r
      = Real.sin r / r ^ 2 + 3 * Real.cos r / r ^ 3 - 3 * Real.sin r / r ^ 4 := by
    have hcos : HasDerivAt (fun x => Real.cos x / x)
        ((-Real.sin r * id r - Real.cos r * 1) / id r ^ 2) r :=
      HasDerivAt.div (Real.hasDerivAt_cos r) (hasDerivAt_id r) hr
    have hsq : HasDerivAt (fun x => Real.sin x / x ^ 2)
        ((Real.cos r * (r ^ 2) - Real.sin r * (2 * r ^ 1)) / (r ^ 2) ^ 2) r :=
      HasDerivAt.div (Real.hasDerivAt_sin r) (hasDerivAt_pow 2 r)
        (pow_ne_zero 2 hr)
    have hdif : HasDerivAt (fun x => Real.cos x / x - Real.sin x / x ^ 2)
        (-Real.sin r / r - 2 * Real.cos r / r ^ 2 + 2 * Real.sin r / r ^ 3) r :=
      (hcos.sub hsq).congr_deriv (by simp only [id_eq, mul_one]; field_simp [hr]; ring)
    have hinv : HasDerivAt (fun x => -(1 / x)) (1 / r ^ 2) r := by
      have h : HasDerivAt (fun x => 1 / x) ((0 * id r - 1 * 1) / id r ^ 2) r :=
        HasDerivAt.div (hasDerivAt_const r 1) (hasDerivAt_id r) hr
      have hneg := h.neg
      have heq : -((0 * id r - 1 * 1) / id r ^ 2) = 1 / r ^ 2 := by
        simp only [id_eq, zero_mul, mul_one, zero_sub, neg_div, neg_neg]
      rw [heq] at hneg
      exact hneg
    have hprod := hinv.mul hdif
    refine HasDerivAt.deriv ?_
    convert hprod using 1
    · rfl
    · rfl
    · field_simp [hr]
      ring
  rw [sbessel, h2, hee, hd2, sj2]
  field_simp [hr]
  ring
