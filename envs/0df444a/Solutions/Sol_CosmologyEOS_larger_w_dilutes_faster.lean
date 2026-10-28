-- Prove2me | solution 1 for CosmologyEOS.larger_w_dilutes_faster
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:26:01.287608+00:00
-- url     : https://prove2.me/submissions/6e9de02e-f300-4f42-a624-9ca669cc08b1

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

theorem solution (w₁ w₂ : ℝ) (hw : w₁ < w₂) (a ε₁ ε₂ p₁ p₂ : ℝ → ℝ)
    (ha_diff : ∀ t, DifferentiableAt ℝ a t)
    (hε₁_diff : ∀ t, DifferentiableAt ℝ ε₁ t)
    (hε₂_diff : ∀ t, DifferentiableAt ℝ ε₂ t)
    (ha_pos : ∀ t, 0 < a t)
    (hε₁_pos : ∀ t, 0 < ε₁ t)
    (heos₁ : ∀ t, p₁ t = w₁ * ε₁ t) (heos₂ : ∀ t, p₂ t = w₂ * ε₂ t)
    (hfluid₁ : ∀ t, FluidEquation a ε₁ p₁ t) (hfluid₂ : ∀ t, FluidEquation a ε₂ p₂ t)
    (hexpand : Tendsto a atTop atTop) :
    Tendsto (fun t => ε₂ t / ε₁ t) atTop (𝓝 0) := by
  have h1 := LUCore.scale_core Set.univ isOpen_univ isPreconnected_univ a ε₁ (3 * (1 + w₁))
    (fun t _ => ha_diff t) (fun t _ => hε₁_diff t) (fun t _ => ha_pos t)
    (fun t _ => by rw [hfluid₁ t, heos₁ t]; ring)
  have h2 := LUCore.scale_core Set.univ isOpen_univ isPreconnected_univ a ε₂ (3 * (1 + w₂))
    (fun t _ => ha_diff t) (fun t _ => hε₂_diff t) (fun t _ => ha_pos t)
    (fun t _ => by rw [hfluid₂ t, heos₂ t]; ring)
  have key : ∀ t, ε₂ t / ε₁ t = (ε₂ 0 * a 0 ^ (3 * (1 + w₂))) / (ε₁ 0 * a 0 ^ (3 * (1 + w₁)))
      * a t ^ (-(3 * (w₂ - w₁))) := by
    intro t
    rw [← h1 0 trivial t trivial, ← h2 0 trivial t trivial,
      show -(3 * (w₂ - w₁)) = 3 * (1 + w₁) - 3 * (1 + w₂) by ring, Real.rpow_sub (ha_pos t)]
    have := (hε₁_pos t).ne'
    have : 0 < a t ^ (3 * (1 + w₁)) := Real.rpow_pos_of_pos (ha_pos t) _
    have : 0 < a t ^ (3 * (1 + w₂)) := Real.rpow_pos_of_pos (ha_pos t) _
    field_simp
  simp_rw [key]
  have := ((tendsto_rpow_neg_atTop (by linarith : (0:ℝ) < 3 * (w₂ - w₁))).comp hexpand).const_mul
    ((ε₂ 0 * a 0 ^ (3 * (1 + w₂))) / (ε₁ 0 * a 0 ^ (3 * (1 + w₁))))
  simpa using this
