-- Prove2me | solution 1 for FixedPointAA.Main.chebT_gammaInv
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:42:24.620991+00:00
-- url     : https://prove2.me/submissions/9af57020-3fbe-4b2a-ab7c-a1a84d589220

import Mathlib
import Definitions.Def_FixedPointAA_Main_Setting
set_option autoImplicit false
open FixedPointAA.Main

theorem solution (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (L : ℕ) (hL : 1 ≤ L) :
    chebT L (gammaInv L δ) = 1 / δ := by
  have hone : 1 ≤ 1 / δ := by
    rw [le_div_iff₀ hδ0]; linarith
  have hL' : (L : ℝ) ≠ 0 := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    exact this.ne'
  unfold chebT gammaInv
  rw [Polynomial.Chebyshev.T_real_cosh]
  have : ((L : ℤ) : ℝ) * (Real.arcosh (1 / δ) / (L : ℝ)) = Real.arcosh (1 / δ) := by
    push_cast; field_simp
  rw [this, Real.cosh_arcosh hone]
