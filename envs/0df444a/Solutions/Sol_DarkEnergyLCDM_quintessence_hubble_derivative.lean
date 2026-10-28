-- Prove2me | solution 1 for DarkEnergyLCDM.quintessence_hubble_derivative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:24:25.452772+00:00
-- url     : https://prove2.me/submissions/1a516363-e4e4-4d3c-a58e-3d19f7fcdabf

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

open Real
open DarkEnergyLCDM

theorem solution (G : ℝ) (I : Set ℝ) (hI : IsOpen I)
    (a ϕ V ρ p : ℝ → ℝ) (ha : ContDiffOn ℝ 2 a I) (ha_pos : ∀ t ∈ I, 0 < a t)
    (hϕ : ContDiffOn ℝ 2 ϕ I) (hV : Differentiable ℝ V) (hρ : DifferentiableOn ℝ ρ I)
    (hfried : ∀ t ∈ I,
      hubble a t ^ 2 = 8 * π * G / 3 * (deriv ϕ t ^ 2 / 2 + V (ϕ t) + ρ t))
    (hKG : ∀ t ∈ I, deriv (deriv ϕ) t + 3 * hubble a t * deriv ϕ t + deriv V (ϕ t) = 0)
    (hcont : ∀ t ∈ I, ContinuityEq a ρ p t) :
    ∀ t ∈ I, hubble a t ≠ 0 →
      deriv (hubble a) t = -(4 * π * G) * (deriv ϕ t ^ 2 + ρ t + p t) := by
  intro t ht hH
  have hn := hI.mem_nhds ht
  have hd1 : DifferentiableAt ℝ ϕ t := (hϕ.differentiableOn (by norm_num)).differentiableAt hn
  have hd2 : DifferentiableAt ℝ (deriv ϕ) t :=
    ((hϕ.deriv_of_isOpen hI (m := 1) (by norm_num)).differentiableOn (by norm_num)).differentiableAt hn
  have ha1 : DifferentiableAt ℝ a t := (ha.differentiableOn (by norm_num)).differentiableAt hn
  have ha2 : DifferentiableAt ℝ (deriv a) t :=
    ((ha.deriv_of_isOpen hI (m := 1) (by norm_num)).differentiableOn (by norm_num)).differentiableAt hn
  have hρd : DifferentiableAt ℝ ρ t := hρ.differentiableAt hn
  have hHd : DifferentiableAt ℝ (hubble a) t :=
    show DifferentiableAt ℝ (fun s => deriv a s / a s) t from ha2.div ha1 (ha_pos t ht).ne'
  have hF : HasDerivAt (fun s => 8 * π * G / 3 * (deriv ϕ s ^ 2 / 2 + V (ϕ s) + ρ s))
      (8 * π * G / 3 * ((↑2 * deriv ϕ t ^ (2 - 1) * deriv (deriv ϕ) t) / 2
        + deriv V (ϕ t) * deriv ϕ t + deriv ρ t)) t :=
    ((((hd2.hasDerivAt.pow 2).div_const 2).add
      ((hV (ϕ t)).hasDerivAt.comp t hd1.hasDerivAt)).add hρd.hasDerivAt).const_mul _
  have hL : HasDerivAt (fun s => hubble a s ^ 2)
      (↑2 * hubble a t ^ (2 - 1) * deriv (hubble a) t) t := hHd.hasDerivAt.pow 2
  have hev : (fun s => hubble a s ^ 2) =ᶠ[nhds t]
      (fun s => 8 * π * G / 3 * (deriv ϕ s ^ 2 / 2 + V (ϕ s) + ρ s)) :=
    Filter.eventually_of_mem hn (fun s hs => hfried s hs)
  have heq := hL.unique (hF.congr_of_eventuallyEq hev)
  have hc := hcont t ht
  unfold ContinuityEq at hc
  have hk := hKG t ht
  apply mul_left_cancel₀ hH
  linear_combination (1/2 : ℝ) * heq + (4 * π * G / 3) * (deriv ϕ t * hk + hc)
