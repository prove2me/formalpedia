-- Prove2me | solution 1 for Freiman.trunk_diagonal_factor
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T04:22:36.907981+00:00
-- url     : https://prove2.me/submissions/5ea20d6f-b84b-4bdc-a83c-4e13ff494250

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

open Freiman

theorem val_scale (q : ℚ) (x : CertField) : certFieldVal (certFieldScale q x) = (q:ℝ) * certFieldVal x := by
  simp only [certFieldVal, certFieldScale]; push_cast; ring

theorem solution (P : CertPoly22) (hs : ∀ i j : Fin 3, P i j = certFieldScale (-1) (P j i)) (r s : ℝ) :
    certPolyEval P r s = (r-s)*(certFieldVal (P 1 0)+certFieldVal (P 2 0)*(r+s)+certFieldVal (P 2 1)*r*s) := by
  have hv : ∀ i j : Fin 3, certFieldVal (P i j) = - certFieldVal (P j i) := by
    intro i j
    rw [hs i j, val_scale]; push_cast; ring
  have h00 := hv 0 0
  have h11 := hv 1 1
  have h22 := hv 2 2
  have h01 := hv 0 1
  have h02 := hv 0 2
  have h12 := hv 1 2
  simp only [certPolyEval, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  linear_combination (1/2:ℝ) * h00 + (1/2:ℝ) * r * s * h11 + (1/2:ℝ) * r^2 * s^2 * h22
    + s * h01 + s^2 * h02 + r * s^2 * h12
