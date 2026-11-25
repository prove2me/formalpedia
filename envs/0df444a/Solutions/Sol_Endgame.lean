-- Prove2me | solution 1 for Endgame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:24:43.540164+00:00
-- url     : https://prove2.me/submissions/856b496f-02db-4a43-88e5-71519d18a100

module
public import Definitions.Def_PHarmonicPoly_CauchySchwarzPi
public import Definitions.Def_PHarmonicPoly_Endgame
public import Theorems.Thm_CauchySchwarzPi


set_option autoImplicit false
@[expose] public section
public section
open Real
theorem _root_.solution (a b s δ : ℝ)
    (_hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 13)
    (ha : 8 / 13 < a) (ha1 : a ≤ 1)
    (hs : 0 ≤ s) (hsq : s ^ 2 + b ^ 2 = 1) :
    s + |b| / Real.pi - (2 - δ) * a + (1 - a) ^ 2 / (2 * a) < 0 := by
  have ha0 : (0:ℝ) < a := by linarith
  have h1 : s + |b| / π < 17 / 16 := CauchySchwarzPi b s hs hsq
  have h2 : (200 : ℝ) / 169 < (2 - δ) * a := by nlinarith
  have h3 : (1 - a) ^ 2 / (2 * a) < 25 / 208 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have : (17:ℝ)/16 - 200/169 + 25/208 = -(1/1352) := by norm_num
  linarith
