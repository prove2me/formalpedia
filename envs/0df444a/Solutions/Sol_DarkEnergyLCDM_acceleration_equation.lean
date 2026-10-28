-- Prove2me | solution 1 for DarkEnergyLCDM.acceleration_equation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:25:19.667461+00:00
-- url     : https://prove2.me/submissions/91e5a8da-e860-4b15-956c-9b3fa5ee2f41

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs

open Real
open DarkEnergyLCDM

theorem solution (G K Λ : ℝ) (I : Set ℝ) (a ρr ρm : ℝ → ℝ)
    (hbg : IsLCDMBackground G K Λ I a ρr ρm) (t : ℝ) (ht : t ∈ I) (hda : deriv a t ≠ 0) :
    AccelerationEq G Λ a (fun s => ρr s + ρm s) (fun s => ρr s / 3) t := by
  have hn := hbg.isOpen.mem_nhds ht
  have hA : a t ≠ 0 := (hbg.pos_a t ht).ne'
  have ha1 : DifferentiableAt ℝ a t :=
    (hbg.contDiff_a.differentiableOn (by norm_num)).differentiableAt hn
  have ha2 : DifferentiableAt ℝ (deriv a) t :=
    ((hbg.contDiff_a.deriv_of_isOpen hbg.isOpen (m := 1) (by norm_num)).differentiableOn
      (by norm_num)).differentiableAt hn
  have hr : DifferentiableAt ℝ ρr t := hbg.diff_ρr.differentiableAt hn
  have hm : DifferentiableAt ℝ ρm t := hbg.diff_ρm.differentiableAt hn
  have hH : HasDerivAt (hubble a)
      ((deriv (deriv a) t * a t - deriv a t * deriv a t) / a t ^ 2) t :=
    show HasDerivAt (fun s => deriv a s / a s) _ t from ha2.hasDerivAt.div ha1.hasDerivAt hA
  have hL : HasDerivAt (fun s => hubble a s ^ 2)
      (↑2 * hubble a t ^ (2 - 1) *
        ((deriv (deriv a) t * a t - deriv a t * deriv a t) / a t ^ 2)) t := hH.pow 2
  have hF : HasDerivAt (fun s => 8 * π * G / 3 * (ρr s + ρm s) - K / a s ^ 2 + Λ / 3)
      (8 * π * G / 3 * (deriv ρr t + deriv ρm t) -
        (0 * a t ^ 2 - K * (↑2 * a t ^ (2 - 1) * deriv a t)) / (a t ^ 2) ^ 2) t :=
    ((((hr.hasDerivAt.add hm.hasDerivAt).const_mul _).sub
      ((hasDerivAt_const t K).div (ha1.hasDerivAt.pow 2) (pow_ne_zero 2 hA))).add_const _)
  have hev : (fun s => hubble a s ^ 2) =ᶠ[nhds t]
      (fun s => 8 * π * G / 3 * (ρr s + ρm s) - K / a s ^ 2 + Λ / 3) :=
    Filter.eventually_of_mem hn (fun s hs => hbg.friedmann s hs)
  have heq := hL.unique (hF.congr_of_eventuallyEq hev)
  set h := hubble a t with hh
  have hh' : h = deriv a t / a t := rfl
  have hne : h ≠ 0 := by rw [hh']; exact div_ne_zero hda hA
  have e1 : (deriv (deriv a) t * a t - deriv a t * deriv a t) / a t ^ 2
      = deriv (deriv a) t / a t - h ^ 2 := by rw [hh']; field_simp
  have e2 : (0 * a t ^ 2 - K * (↑2 * a t ^ (2 - 1) * deriv a t)) / (a t ^ 2) ^ 2
      = -2 * K * h / a t ^ 2 := by rw [hh']; field_simp; ring
  rw [e1] at heq
  rw [e2] at heq
  have cr := hbg.continuity_r t ht
  have cm := hbg.continuity_m t ht
  have fr := hbg.friedmann t ht
  unfold ContinuityEq at cr cm
  unfold FriedmannEq at fr
  rw [← hh] at cr cm fr
  unfold AccelerationEq
  apply mul_left_cancel₀ hne
  linear_combination (1/2 : ℝ) * heq + (4 * π * G / 3) * (cr + cm) + h * fr
