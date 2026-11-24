-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.positionTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:13.246462+00:00
-- url     : https://prove2.me/submissions/daa8b549-c06a-4e4a-9913-c9f18c1b27e7

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Sz Finset
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : PositionTop := by
  intro c de de' Y l h ht hl hlk hY
  obtain ⟨hY1, hY2⟩ := hY
  have hD := h.hDel
  have hk := h.hk
  have hc : c.top = true ∧ c.k - 1 + 1 = c.k := ⟨ht, by omega⟩
  simp only [Cfg.rho, if_pos hc]
  obtain ⟨hb1, hb2⟩ := h.htop ht
  have hbp : 0 < c.bp := by have := h.hb1; linarith
  have hkc : ((c.k - 1 : ℕ) : ℝ) = (c.k:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ c.k)]; norm_num
  have hvk : c.v (c.k - 1) = c.vlast := by simp only [Cfg.v, hkc]; ring
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = -(c.vlast + Y) := ⟨_, rfl⟩
  have hlR : (l:ℝ) + 2 ≤ c.k := by exact_mod_cast hlk
  have hl1 : (1:ℝ) ≤ l := by exact_mod_cast hl
  have hvl : c.v l = c.vlast + 4 * c.Del * ((c.k:ℝ) - 1 - l) := rfl
  have m1 : 4 * c.Del * 1 ≤ 4 * c.Del * ((c.k:ℝ) - 1 - l) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have m2 : 4 * c.Del * ((c.k:ℝ) - 1 - l) ≤ 4 * c.Del * (c.k:ℝ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hX1 : 7 / 2 * c.Del ≤ X := by rw [hX]; linarith
  have hX2 : X ≤ 4 * c.k * c.Del := by rw [hX]; linarith
  have hv0 := h.hv0
  rw [hvk]
  have e1 : (c.vlast - -Y) * (c.vlast + 1 - -Y) = X * (X - 1) := by rw [hX]; ring
  have hX0 : 0 ≤ X := by linarith
  rw [e1, abs_of_nonneg (mul_nonneg hX0 (by linarith))]
  have hs : Real.sqrt (X * (X - 1)) ≤ X := by
    rw [Real.sqrt_le_iff]; exact ⟨hX0, by nlinarith⟩
  have hden : c.bp ≤ c.bp + -Y - 1 / 2 := by
    have : -Y = X + c.vlast := by rw [hX]; ring
    linarith
  calc Real.sqrt (X * (X - 1)) / (c.bp + -Y - 1 / 2) ≤ X / c.bp := div_le_div₀ hX0 hs hbp hden
    _ ≤ 4 * c.k * c.Del / c.bp := div_le_div_of_nonneg_right hX2 hbp.le
end Formalism.FourierDecayAlt.P
