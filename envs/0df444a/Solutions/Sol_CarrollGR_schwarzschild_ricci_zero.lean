-- Prove2me | solution 1 for CarrollGR.schwarzschild_ricci_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T12:03:27.045027+00:00
-- url     : https://prove2.me/submissions/f8f6ae62-71d3-4f62-8fdf-2e99ada0da9c

import Mathlib
import Definitions.Def_CarrollGR_Defs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open scoped ContDiff

namespace CGRSchw
open CarrollGR Finset Filter Topology

theorem pd_prod (a b : ℝ → ℝ) (a' b' : ℝ) (x : Coord)
    (ha : HasDerivAt a a' (x 1)) (hb : HasDerivAt b b' (x 2)) (α : Fin 4) :
    partialD α (fun y => a (y 1) * b (y 2)) x
      = a' * b (x 2) * (Pi.single α (1:ℝ) : Coord) 1
        + a (x 1) * b' * (Pi.single α (1:ℝ) : Coord) 2 := by
  have p1 : HasFDerivAt (fun f : Coord => f 1) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 1 : Coord →L[ℝ] ℝ) x := hasFDerivAt_apply 1 x
  have p2 : HasFDerivAt (fun f : Coord => f 2) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 2 : Coord →L[ℝ] ℝ) x := hasFDerivAt_apply 2 x
  have h1 := ha.comp_hasFDerivAt (f := fun f : Coord => f 1) x p1
  have h2 := hb.comp_hasFDerivAt (f := fun f : Coord => f 2) x p2
  have h := h1.mul h2
  unfold partialD
  rw [show (fun y : Coord => a (y 1) * b (y 2)) = ((a ∘ fun f : Coord => f 1) * (b ∘ fun f : Coord => f 2)) from rfl, h.fderiv]
  simp
  ring

noncomputable def gA (k : ℝ) : Fin 4 → Fin 4 → ℝ → ℝ :=
  ![![(fun r : ℝ => -(1 - k / r)), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)],
    ![(fun _ : ℝ => 0), (fun r : ℝ => (1 - k / r)⁻¹), (fun _ : ℝ => 0), (fun _ : ℝ => 0)],
    ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun r : ℝ => r ^ 2), (fun _ : ℝ => 0)],
    ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun r : ℝ => r ^ 2)]]

noncomputable def gA' (k : ℝ) : Fin 4 → Fin 4 → ℝ → ℝ :=
  ![![(fun r : ℝ => -(k / r ^ 2)), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)],
    ![(fun _ : ℝ => 0), (fun r : ℝ => -(k / r ^ 2) / (1 - k / r) ^ 2), (fun _ : ℝ => 0), (fun _ : ℝ => 0)],
    ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun r : ℝ => 2 * r), (fun _ : ℝ => 0)],
    ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun r : ℝ => 2 * r)]]

noncomputable def gB : Fin 4 → Fin 4 → ℝ → ℝ :=
  ![![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)],
    ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)],
    ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)],
    ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun t : ℝ => Real.sin t ^ 2)]]

noncomputable def gB' : Fin 4 → Fin 4 → ℝ → ℝ :=
  ![![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)],
    ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)],
    ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)],
    ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun t : ℝ => 2 * Real.sin t * Real.cos t)]]

noncomputable def aF (k : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ :=
  ![![![(fun _ : ℝ => 0), (fun r : ℝ => k / (2 * r * (r - k))), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun r : ℝ => k / (2 * r * (r - k))), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)]],
    ![![(fun r : ℝ => k * (r - k) / (2 * r ^ 3)), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun r : ℝ => -(k / (2 * r * (r - k)))), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun r : ℝ => -(r - k)), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun r : ℝ => -(r - k))]],
    ![![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun r : ℝ => 1 / r), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun r : ℝ => 1 / r), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => -1)]],
    ![![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun r : ℝ => 1 / r)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 0), (fun r : ℝ => 1 / r), (fun _ : ℝ => 1), (fun _ : ℝ => 0)]]]

noncomputable def aF' (k : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ :=
  ![![![(fun _ : ℝ => 0), (fun r : ℝ => -(k * (2 * r - k)) / (2 * r ^ 2 * (r - k) ^ 2)), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun r : ℝ => -(k * (2 * r - k)) / (2 * r ^ 2 * (r - k) ^ 2)), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)]],
    ![![(fun r : ℝ => k * (3 * k - 2 * r) / (2 * r ^ 4)), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun r : ℝ => k * (2 * r - k) / (2 * r ^ 2 * (r - k) ^ 2)), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => -1), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => -1)]],
    ![![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun r : ℝ => -1 / r ^ 2), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun r : ℝ => -1 / r ^ 2), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)]],
    ![![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun r : ℝ => -1 / r ^ 2)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun r : ℝ => -1 / r ^ 2), (fun _ : ℝ => 0), (fun _ : ℝ => 0)]]]

noncomputable def bF : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ :=
  ![![![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)]],
    ![![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun t : ℝ => Real.sin t ^ 2)]],
    ![![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun t : ℝ => Real.sin t * Real.cos t)]],
    ![![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun t : ℝ => Real.cos t / Real.sin t)], ![(fun _ : ℝ => 1), (fun _ : ℝ => 1), (fun t : ℝ => Real.cos t / Real.sin t), (fun _ : ℝ => 1)]]]

noncomputable def bF' : Fin 4 → Fin 4 → Fin 4 → ℝ → ℝ :=
  ![![![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)]],
    ![![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun t : ℝ => 2 * Real.sin t * Real.cos t)]],
    ![![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun t : ℝ => Real.cos t * Real.cos t - Real.sin t * Real.sin t)]],
    ![![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun t : ℝ => -(Real.sin t * Real.sin t + Real.cos t * Real.cos t) / Real.sin t ^ 2)], ![(fun _ : ℝ => 0), (fun _ : ℝ => 0), (fun t : ℝ => -(Real.sin t * Real.sin t + Real.cos t * Real.cos t) / Real.sin t ^ 2), (fun _ : ℝ => 0)]]]


theorem hd_f1 (k r : ℝ) (hr : r ≠ 0) (hk : r - k ≠ 0) :
    HasDerivAt (fun r : ℝ => k / (2 * r * (r - k))) (-(k * (2 * r - k)) / (2 * r ^ 2 * (r - k) ^ 2)) r := by
  have h2 := ((hasDerivAt_id' r).const_mul (2:ℝ)).mul ((hasDerivAt_id' r).sub_const k)
  have h := (hasDerivAt_const r k).div h2 (mul_ne_zero (mul_ne_zero two_ne_zero hr) hk)
  exact h.congr_deriv (by (try simp only [Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.pow_apply, Pi.inv_apply]); field_simp; ring)

theorem hd_f2 (k r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun r : ℝ => k * (r - k) / (2 * r ^ 3)) (k * (3 * k - 2 * r) / (2 * r ^ 4)) r := by
  have h1 := (hasDerivAt_id' r).sub_const k |>.const_mul k
  have h2 := ((hasDerivAt_id' r).pow 3).const_mul (2:ℝ)
  have h := h1.div h2 (mul_ne_zero two_ne_zero (pow_ne_zero 3 hr))
  exact h.congr_deriv (by (try simp only [Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.pow_apply, Pi.inv_apply]); field_simp; ring)

theorem hd_f3 (k r : ℝ) (hr : r ≠ 0) (hk : r - k ≠ 0) :
    HasDerivAt (fun r : ℝ => -(k / (2 * r * (r - k)))) (k * (2 * r - k) / (2 * r ^ 2 * (r - k) ^ 2)) r := by
  have h := (hd_f1 k r hr hk).neg
  exact h.congr_deriv (by ring)

theorem hd_f4 (k r : ℝ) : HasDerivAt (fun r : ℝ => -(r - k)) (-1) r := by
  have h := ((hasDerivAt_id' r).sub_const k).neg
  exact h

theorem hd_f5 (r : ℝ) (hr : r ≠ 0) : HasDerivAt (fun r : ℝ => 1 / r) (-1 / r ^ 2) r := by
  have h := (hasDerivAt_const r (1:ℝ)).div (hasDerivAt_id' r) hr
  exact h.congr_deriv (by (try simp only [Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.pow_apply, Pi.inv_apply]); field_simp; ring)

theorem hd_g0 (k r : ℝ) (hr : r ≠ 0) : HasDerivAt (fun r : ℝ => -(1 - k / r)) (-(k / r ^ 2)) r := by
  have h := ((hasDerivAt_const r (1:ℝ)).sub ((hasDerivAt_const r k).div (hasDerivAt_id' r) hr)).neg
  exact h.congr_deriv (by (try simp only [Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.pow_apply, Pi.inv_apply]); field_simp; ring)

theorem hd_g1 (k r : ℝ) (hr : r ≠ 0) (hA : 1 - k / r ≠ 0) :
    HasDerivAt (fun r : ℝ => (1 - k / r)⁻¹) (-(k / r ^ 2) / (1 - k / r) ^ 2) r := by
  have h := ((hasDerivAt_const r (1:ℝ)).sub ((hasDerivAt_const r k).div (hasDerivAt_id' r) hr)).inv hA
  exact h.congr_deriv (by (try simp only [Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.pow_apply, Pi.inv_apply]); field_simp; ring)

theorem hd_sq (r : ℝ) : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
  have h := (hasDerivAt_id' r).pow 2
  exact h.congr_deriv (by simp)

theorem hd_s2 (t : ℝ) : HasDerivAt (fun t : ℝ => Real.sin t ^ 2) (2 * Real.sin t * Real.cos t) t := by
  have h := (Real.hasDerivAt_sin t).pow 2
  exact h.congr_deriv (by simp <;> ring)

theorem hd_sc (t : ℝ) : HasDerivAt (fun t : ℝ => Real.sin t * Real.cos t)
    (Real.cos t * Real.cos t - Real.sin t * Real.sin t) t := by
  have h := (Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)
  exact h.congr_deriv (by ring)

theorem hd_ct (t : ℝ) (hs : Real.sin t ≠ 0) : HasDerivAt (fun t : ℝ => Real.cos t / Real.sin t)
    (-(Real.sin t * Real.sin t + Real.cos t * Real.cos t) / Real.sin t ^ 2) t := by
  have h := (Real.hasDerivAt_cos t).div (Real.hasDerivAt_sin t) hs
  exact h.congr_deriv (by ring)

theorem gA_deriv (k r : ℝ) (hr : r ≠ 0) (hA : 1 - k / r ≠ 0) (i j : Fin 4) :
    HasDerivAt (gA k i j) (gA' k i j r) r := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact hasDerivAt_const r (0:ℝ)
    | exact hd_g0 k r hr
    | exact hd_g1 k r hr hA
    | exact hd_sq r

theorem gB_deriv (t : ℝ) (i j : Fin 4) : HasDerivAt (gB i j) (gB' i j t) t := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact hasDerivAt_const t (1:ℝ)
    | exact hd_s2 t

theorem aF_deriv (k r : ℝ) (hr : r ≠ 0) (hk : r - k ≠ 0) (σ μ ν : Fin 4) :
    HasDerivAt (aF k σ μ ν) (aF' k σ μ ν r) r := by
  fin_cases σ <;> fin_cases μ <;> fin_cases ν <;>
    first
    | exact hasDerivAt_const r (0:ℝ)
    | exact hasDerivAt_const r (1:ℝ)
    | exact hasDerivAt_const r (-1:ℝ)
    | exact hd_f1 k r hr hk
    | exact hd_f2 k r hr
    | exact hd_f3 k r hr hk
    | exact hd_f4 k r
    | exact hd_f5 r hr

theorem bF_deriv (t : ℝ) (hs : Real.sin t ≠ 0) (σ μ ν : Fin 4) :
    HasDerivAt (bF σ μ ν) (bF' σ μ ν t) t := by
  fin_cases σ <;> fin_cases μ <;> fin_cases ν <;>
    first
    | exact hasDerivAt_const t (1:ℝ)
    | exact hd_s2 t
    | exact hd_sc t
    | exact hd_ct t hs

theorem g_repr (GN m : ℝ) (y : Coord) (i j : Fin 4) :
    schwarzschild GN m y i j = gA (2 * GN * m) i j (y 1) * gB i j (y 2) := by
  fin_cases i <;> fin_cases j <;> simp [schwarzschild, sphericalMetric, gA, gB, Matrix.diagonal]

theorem pd_g (GN m : ℝ) (y : Coord) (hr : y 1 ≠ 0) (hA : 1 - 2 * GN * m / y 1 ≠ 0) (μ i j : Fin 4) :
    partialD μ (fun z => schwarzschild GN m z i j) y
      = gA' (2 * GN * m) i j (y 1) * gB i j (y 2) * (Pi.single μ (1:ℝ) : Coord) 1
        + gA (2 * GN * m) i j (y 1) * gB' i j (y 2) * (Pi.single μ (1:ℝ) : Coord) 2 := by
  have e : (fun z => schwarzschild GN m z i j) = fun z => gA (2 * GN * m) i j (z 1) * gB i j (z 2) :=
    funext fun z => g_repr GN m z i j
  rw [e]
  exact pd_prod _ _ _ _ y (gA_deriv _ _ hr hA i j) (gB_deriv _ i j) μ

theorem inv_g (GN m : ℝ) (y : Coord) (hr : y 1 ≠ 0) (hA : 1 - 2 * GN * m / y 1 ≠ 0)
    (hs : Real.sin (y 2) ≠ 0) :
    invMetric (schwarzschild GN m) y = Matrix.diagonal
      ![(-(1 - 2 * GN * m / y 1))⁻¹, 1 - 2 * GN * m / y 1, (y 1 ^ 2)⁻¹,
        (y 1 ^ 2 * Real.sin (y 2) ^ 2)⁻¹] := by
  have hk : y 1 - 2 * GN * m ≠ 0 := by
    intro h; apply hA; rw [show 2 * GN * m = y 1 by linarith, div_self hr, sub_self]
  have hk' : 2 * GN * m - y 1 ≠ 0 := by intro h; apply hk; linarith
  unfold invMetric schwarzschild sphericalMetric
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp <;> field_simp

theorem chr_eq (GN m : ℝ) (y : Coord) (hr : y 1 ≠ 0) (hk : y 1 - 2 * GN * m ≠ 0)
    (hs : Real.sin (y 2) ≠ 0) (σ μ ν : Fin 4) :
    christoffel (schwarzschild GN m) σ μ ν y = aF (2 * GN * m) σ μ ν (y 1) * bF σ μ ν (y 2) := by
  have hA : 1 - 2 * GN * m / y 1 ≠ 0 := by
    rw [one_sub_div hr]; exact div_ne_zero hk hr
  have hk' : 2 * GN * m - y 1 ≠ 0 := by intro h; apply hk; linarith
  simp only [christoffel, pd_g GN m y hr hA, inv_g GN m y hr hA hs]
  fin_cases σ <;> fin_cases μ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, gA, gA', gB, gB', aF, bF, Matrix.diagonal, Pi.single_apply] <;>
    (try field_simp) <;> ring

theorem pd_chr (GN m : ℝ) (x : Coord) (hr : x 1 ≠ 0) (hk : x 1 - 2 * GN * m ≠ 0)
    (hs : Real.sin (x 2) ≠ 0) (α σ μ ν : Fin 4) :
    partialD α (christoffel (schwarzschild GN m) σ μ ν) x
      = aF' (2 * GN * m) σ μ ν (x 1) * bF σ μ ν (x 2) * (Pi.single α (1:ℝ) : Coord) 1
        + aF (2 * GN * m) σ μ ν (x 1) * bF' σ μ ν (x 2) * (Pi.single α (1:ℝ) : Coord) 2 := by
  have h1 : ∀ᶠ y in 𝓝 x, y 1 ≠ 0 :=
    ((continuous_apply (1 : Fin 4)).continuousAt (x := x)).eventually_ne hr
  have h2 : ∀ᶠ y in 𝓝 x, y 1 - 2 * GN * m ≠ 0 :=
    (((continuous_apply (1 : Fin 4)).sub continuous_const).continuousAt (x := x)).eventually_ne hk
  have h3 : ∀ᶠ y in 𝓝 x, Real.sin (y 2) ≠ 0 :=
    ((Real.continuous_sin.comp (continuous_apply (2 : Fin 4))).continuousAt (x := x)).eventually_ne hs
  have heq : christoffel (schwarzschild GN m) σ μ ν =ᶠ[𝓝 x]
      fun y => aF (2 * GN * m) σ μ ν (y 1) * bF σ μ ν (y 2) := by
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    exact chr_eq GN m y hy1 hy2 hy3 σ μ ν
  have hp := pd_prod _ _ _ _ x (aF_deriv (2 * GN * m) (x 1) hr hk σ μ ν) (bF_deriv (x 2) hs σ μ ν) α
  unfold partialD at hp ⊢
  rw [heq.fderiv_eq]
  exact hp

theorem ricci_main (GN m : ℝ) (x : Coord) (hr : x 1 ≠ 0) (hk : x 1 - 2 * GN * m ≠ 0)
    (hs : Real.sin (x 2) ≠ 0) (μ ν : Fin 4) :
    ricci (schwarzschild GN m) μ ν x = 0 := by
  have hk' : 2 * GN * m - x 1 ≠ 0 := by intro h; apply hk; linarith
  simp only [ricci, riemann, pd_chr GN m x hr hk hs, chr_eq GN m x hr hk hs]
  fin_cases μ <;> fin_cases ν <;>
    simp [Fin.sum_univ_four, aF, aF', bF, bF', Pi.single_apply] <;>
    (try field_simp) <;> ring

end CGRSchw

open CarrollGR in open scoped ContDiff in
theorem solution (GN m : ℝ) (hGN : 0 < GN) (hm : 0 < m) (x : Coord)
    (hr : 0 < x 1) (hr' : x 1 ≠ 2 * GN * m) (hθ : x 2 ∈ Set.Ioo 0 Real.pi) (μ ν : Fin 4) :
    ricci (schwarzschild GN m) μ ν x = 0 := by
  exact CGRSchw.ricci_main GN m x hr.ne' (sub_ne_zero.mpr hr')
    (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne' μ ν
