-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.equiCoBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:02.363022+00:00
-- url     : https://prove2.me/submissions/ecd62cfe-50a9-4eb0-8252-906d02888022

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
theorem _root_.solution : Formalism.FourierDecayAlt.F7.EquiCoBound := by
  intro n L hn hL
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hLpos : 0 < L := lt_of_lt_of_le hnpos hL
  have h1 : (1:ℝ) ≤ L / n := by rw [le_div_iff₀ hnpos]; linarith
  have hfl : (1:ℤ) ≤ ⌊L / (n:ℝ)⌋ := Int.le_floor.mpr (by exact_mod_cast h1)
  set h : ℝ := ((⌊L / (n:ℝ)⌋ : ℤ) : ℝ) with hh
  have hh1 : (1:ℝ) ≤ h := by rw [hh]; exact_mod_cast hfl
  have hlt : L / n < h + 1 := Int.lt_floor_add_one _
  have hpos : 0 < h := by linarith
  have h2 : 2 / h ≤ 4 * n / L := by
    rw [div_le_div_iff₀ hpos hLpos]
    have : L < (h + 1) * n := by rwa [div_lt_iff₀ hnpos] at hlt
    nlinarith
  have h3 : (2 / h) ^ n ≤ (4 * n / L) ^ n := pow_le_pow_left₀ (by positivity) h2 n
  have hf : (0:ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  calc (2 / h) ^ n / (n.factorial : ℝ) ≤ (4 * n / L) ^ n / (n.factorial : ℝ) := by gcongr
    _ = (4 / L) ^ n * ((n:ℝ) ^ n / n.factorial) := by
        rw [show 4 * (n:ℝ) / L = 4 / L * n by ring, mul_pow]; ring
    _ ≤ (4 / L) ^ n * Real.exp n := by
        gcongr
        exact Real.pow_div_factorial_le_exp _ hnpos.le n
    _ = (4 * Real.exp 1 / L) ^ n := by
        rw [show 4 * Real.exp 1 / L = 4 / L * Real.exp 1 by ring, mul_pow, ← Real.exp_nat_mul, mul_one]
end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
