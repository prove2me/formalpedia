-- Prove2me | solution 1 for DarkEnergyLCDM.radiation_density_scaling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:22:42.035171+00:00
-- url     : https://prove2.me/submissions/6647cafb-ab85-40b0-9f73-eb820a8addc2

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

open Real
open DarkEnergyLCDM

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

namespace LUCore2

theorem dens (I : Set ℝ) (hI : IsOpen I) (hIc : IsPreconnected I)
    (a ρ : ℝ → ℝ) (ha : DifferentiableOn ℝ a I) (ha_pos : ∀ t ∈ I, 0 < a t)
    (hρ : DifferentiableOn ℝ ρ I) (n : ℕ) (c : ℝ) (hn : (n : ℝ) = 3 * (1 + c))
    (hcont : ∀ t ∈ I, ContinuityEq a ρ (fun s => c * ρ s) t)
    (t₀ : ℝ) (ht₀ : t₀ ∈ I) (ha₀ : a t₀ = 1) :
    ∀ t ∈ I, ρ t = ρ t₀ * (a t)⁻¹ ^ n := by
  intro t ht
  have h := LUCore.scale_core I hI hIc a ρ (n : ℝ)
    (fun t ht => ha.differentiableAt (hI.mem_nhds ht))
    (fun t ht => hρ.differentiableAt (hI.mem_nhds ht)) ha_pos
    (fun t ht => by
      have := hcont t ht
      unfold ContinuityEq hubble at this
      rw [hn]; linarith) t₀ ht₀ t ht
  rw [Real.rpow_natCast, Real.rpow_natCast, ha₀] at h
  have := (ha_pos t ht).ne'
  rw [inv_pow, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ this), h]
  simp

end LUCore2

theorem solution (I : Set ℝ) (hI : IsOpen I) (hIc : IsPreconnected I)
    (a ρ : ℝ → ℝ) (ha : DifferentiableOn ℝ a I) (ha_pos : ∀ t ∈ I, 0 < a t)
    (hρ : DifferentiableOn ℝ ρ I)
    (hcont : ∀ t ∈ I, ContinuityEq a ρ (fun s => ρ s / 3) t)
    (t₀ : ℝ) (ht₀ : t₀ ∈ I) (ha₀ : a t₀ = 1) :
    ∀ t ∈ I, ρ t = ρ t₀ * (a t)⁻¹ ^ 4 :=
  LUCore2.dens I hI hIc a ρ ha ha_pos hρ 4 (1/3) (by norm_num)
    (fun t ht => by
      have := hcont t ht
      unfold ContinuityEq at this ⊢
      linarith) t₀ ht₀ ha₀
