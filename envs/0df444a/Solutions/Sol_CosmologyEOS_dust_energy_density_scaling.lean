-- Prove2me | solution 1 for CosmologyEOS.dust_energy_density_scaling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:21:10.642034+00:00
-- url     : https://prove2.me/submissions/9ac8c6b2-08ac-4bdb-b8c7-7ea79dec7b65

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology
open CosmologyEOS

namespace LUCore

theorem scale_core (I : Set ℝ) (hI : IsOpen I) (hIc : IsPreconnected I) (a ε : ℝ → ℝ) (k : ℝ)
    (ha : ∀ t ∈ I, DifferentiableAt ℝ a t) (hε : ∀ t ∈ I, DifferentiableAt ℝ ε t)
    (hpos : ∀ t ∈ I, 0 < a t)
    (hode : ∀ t ∈ I, deriv ε t = -k * (deriv a t / a t) * ε t) :
    ∀ s ∈ I, ∀ t ∈ I, ε t * a t ^ k = ε s * a s ^ k := by
  have hd : ∀ t ∈ I, HasDerivAt (fun t => ε t * a t ^ k) 0 t := by
    intro t ht
    have h1 : HasDerivAt (fun t => ε t * a t ^ k)
        (deriv ε t * a t ^ k + ε t * (deriv a t * k * a t ^ (k - 1))) t :=
      (hε t ht).hasDerivAt.mul ((ha t ht).hasDerivAt.rpow_const (p := k)
        (Or.inl (hpos t ht).ne'))
    refine h1.congr_deriv ?_
    rw [hode t ht, Real.rpow_sub_one (hpos t ht).ne']
    have := (hpos t ht).ne'
    field_simp
    ring
  intro s hs t ht
  exact hI.is_const_of_deriv_eq_zero hIc (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv) ht hs

end LUCore

theorem solution (a ε p : ℝ → ℝ) (I : Set ℝ)
    (hI_open : IsOpen I) (hI_conn : IsPreconnected I)
    (ha_diff : ∀ t ∈ I, DifferentiableAt ℝ a t)
    (hε_diff : ∀ t ∈ I, DifferentiableAt ℝ ε t)
    (ha_pos : ∀ t ∈ I, 0 < a t)
    (heos : ∀ t ∈ I, p t = 0 * ε t)
    (hfluid : ∀ t ∈ I, FluidEquation a ε p t) :
    ∀ s ∈ I, ∀ t ∈ I, ε t * a t ^ 3 = ε s * a s ^ 3 := by
  intro s hs t ht
  have h := LUCore.scale_core I hI_open hI_conn a ε ((3 : ℕ) : ℝ) ha_diff hε_diff ha_pos
    (fun t ht => by rw [hfluid t ht, heos t ht]; push_cast; ring) s hs t ht
  rw [Real.rpow_natCast, Real.rpow_natCast] at h
  exact h
