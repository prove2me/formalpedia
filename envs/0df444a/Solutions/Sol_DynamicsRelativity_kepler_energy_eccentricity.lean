-- Prove2me | solution 1 for DynamicsRelativity.kepler_energy_eccentricity
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-23T07:51:18.618621+00:00
-- url     : https://prove2.me/submissions/45a15553-b384-4c6d-8482-ff80a9c1ea5c

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

namespace Ag4Aux_KeplerEnergyDis

noncomputable def E3 : (Fin 3 → ℝ) →L[ℝ] Vec :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm : (Fin 3 → ℝ) →L[ℝ] Vec)

theorem E3_apply (f : Fin 3 → ℝ) : E3 f = WithLp.toLp 2 f := rfl

noncomputable def pos (t : ℝ) : Fin 3 → ℝ := ![Real.cos t, Real.sin t, 0]
noncomputable def velc (t : ℝ) : Fin 3 → ℝ := ![-Real.sin t, Real.cos t, 0]

noncomputable def xc (t : ℝ) : Vec := E3 (pos t)

theorem hasDerivAt_pos (t : ℝ) : HasDerivAt pos (velc t) t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [pos, velc] using Real.hasDerivAt_cos t
  · simpa [pos, velc] using Real.hasDerivAt_sin t
  · simpa [pos, velc] using hasDerivAt_const t (0 : ℝ)

theorem hasDerivAt_velc (t : ℝ) : HasDerivAt velc (-pos t) t := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simpa [pos, velc] using (Real.hasDerivAt_sin t).const_mul (-1)
  · simpa [pos, velc] using Real.hasDerivAt_cos t
  · simpa [pos, velc] using hasDerivAt_const t (0 : ℝ)

theorem deriv_xc : deriv xc = fun t => E3 (velc t) := by
  funext t
  exact (E3.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_pos t)).deriv

theorem deriv2_xc : deriv (deriv xc) = fun t => -xc t := by
  rw [deriv_xc]
  funext t
  have := (E3.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_velc t)).deriv
  simp only [Function.comp_def] at this
  rw [this, map_neg]; rfl

theorem contDiff_pos : ContDiff ℝ 2 pos := by
  rw [contDiff_pi]
  intro i
  fin_cases i
  · simpa [pos] using Real.contDiff_cos
  · simpa [pos] using Real.contDiff_sin
  · simpa [pos] using (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => (0 : ℝ)))

theorem norm_xc (t : ℝ) : ‖xc t‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [xc, E3_apply, pos, Fin.sum_univ_three]

theorem norm_vel (t : ℝ) : ‖E3 (velc t)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [E3_apply, velc, Fin.sum_univ_three, add_comm]

theorem kepler : KeplerMotion 1 1 xc where
  mass_pos := one_pos
  smooth := E3.contDiff.comp contDiff_pos
  ne_origin := fun t h => by have := norm_xc t; rw [h, norm_zero] at this; norm_num at this
  eom := fun t => by
    simp only [acc, deriv2_xc, norm_xc, keplerForce, one_smul]
    norm_num

theorem angmom : angularMomentum 1 xc 0 = WithLp.toLp 2 ![0, 0, 1] := by
  unfold angularMomentum vel cross
  rw [deriv_xc]
  ext i
  fin_cases i <;> simp [xc, E3_apply, pos, velc, cross_apply]

end Ag4Aux_KeplerEnergyDis

open Ag4Aux_KeplerEnergyDis in
theorem solution : ¬ (∀ {k m r₀ : ℝ} {x : ℝ → Vec} {A : Vec},
    0 < k → KeplerMotion k m x → angularMomentum m x 0 ≠ 0 →
    r₀ = (‖angularMomentum m x 0‖ / m) ^ 2 / k →
    (∀ t, ‖x t‖ + inner ℝ A (x t) = r₀) → ∀ (t : ℝ),
    keplerEnergy k m x t =
      m * k ^ 2 * (‖A‖ ^ 2 - 1) / (2 * (‖angularMomentum m x 0‖ / m) ^ 2)) := by
  intro h
  have hL : ‖angularMomentum 1 xc 0‖ = 1 := by
    rw [angmom, EuclideanSpace.norm_eq]; simp [Fin.sum_univ_three]
  have hA : ‖(WithLp.toLp 2 ![0, 0, 1] : Vec)‖ = 1 := by
    rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_three]
  have := @h 1 1 1 xc (WithLp.toLp 2 ![0, 0, 1]) one_pos kepler
    (by rw [angmom]; intro h0; have := congrArg (fun v : Vec => v 2) h0; simp at this)
    (by rw [hL]; norm_num)
    (fun t => by
      rw [norm_xc]
      simp [xc, E3_apply, pos, PiLp.inner_apply, Fin.sum_univ_three])
    0
  rw [hL, hA] at this
  unfold keplerEnergy vel at this
  rw [deriv_xc, norm_vel, norm_xc] at this
  norm_num at this
