-- Prove2me | solution 1 for Freiman.markov_symbolic
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:26:52.759068+00:00
-- url     : https://prove2.me/submissions/31974e87-8a80-4989-9cd4-1f44e39fabdb

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Definitions.Def_Freiman_markovSpectrum
import Theorems.Thm_Freiman_form_reduced_pair
import Theorems.Thm_Freiman_form_reduced_orbit_exists
import Theorems.Thm_Freiman_form_orbit_spectrum_criterion
import Theorems.Thm_Freiman_form_symbolic_orbit
import Theorems.Thm_Freiman_form_reduced_discriminant

open Freiman

theorem solution  :
    markovSpectrum = symbolicMarkovSpectrum := by
  apply Set.Subset.antisymm
  · rintro t ⟨A, B, C, hd, hm, ht⟩
    obtain ⟨α, β, hα, hβ, hβ1, hiα, hiβ, hmin, hratio⟩ := form_reduced_pair A B C hd hm
    obtain ⟨R, hRα, hRβ⟩ := form_reduced_orbit_exists α β hα hβ hβ1 hiα hiβ
    refine ⟨R.digits, (form_orbit_spectrum_criterion R t).mpr ?_⟩
    rw [hRα, hRβ]
    exact ⟨hmin, ht.trans hratio⟩
  · rintro t ⟨a, ha⟩
    obtain ⟨R, hRa⟩ := form_symbolic_orbit a
    rw [← hRa] at ha
    obtain ⟨hm, ht⟩ := (form_orbit_spectrum_criterion R t).mp ha
    have hsum : R.alpha 0 + R.beta 0 ≠ 0 := by linarith [R.alpha_gt 0, R.beta_pos 0]
    have hd := form_reduced_discriminant (R.alpha 0) (R.beta 0) hsum
    refine ⟨reducedA (R.alpha 0) (R.beta 0), reducedB (R.alpha 0) (R.beta 0),
      reducedC (R.alpha 0) (R.beta 0), ?_, hm, ?_⟩
    · rw [hd]; norm_num
    · rw [hd, Real.sqrt_one]
      exact ht
