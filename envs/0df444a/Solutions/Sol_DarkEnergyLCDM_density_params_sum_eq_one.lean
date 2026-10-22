-- Prove2me | solution 1 for DarkEnergyLCDM.density_params_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:39:49.486931+00:00
-- url     : https://prove2.me/submissions/fbced6e8-cc19-4418-85e4-ee1e15b77bb2

import Mathlib
import Definitions.Def_DarkEnergyLCDM_Defs
set_option autoImplicit false

open DarkEnergyLCDM

theorem solution (G K Λ : ℝ) (I : Set ℝ) (a ρr ρm : ℝ → ℝ)
    (hbg : IsLCDMBackground G K Λ I a ρr ρm) (t₀ : ℝ) (ht₀ : t₀ ∈ I) (ha₀ : a t₀ = 1)
    (hH₀ : hubble a t₀ ≠ 0) :
    lambdaParam Λ (hubble a t₀) + densityParam G (hubble a t₀) (ρm t₀)
      + densityParam G (hubble a t₀) (ρr t₀) + curvatureParam K (hubble a t₀) = 1 := by
  have h := hbg.friedmann t₀ ht₀
  unfold FriedmannEq at h
  rw [ha₀] at h
  unfold lambdaParam densityParam curvatureParam
  have h2 : hubble a t₀ ^ 2 ≠ 0 := pow_ne_zero 2 hH₀
  field_simp
  simp only [one_pow, div_one] at h
  linarith
