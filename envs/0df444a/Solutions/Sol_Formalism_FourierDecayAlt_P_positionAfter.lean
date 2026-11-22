-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.positionAfter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:18:43.654587+00:00
-- url     : https://prove2.me/submissions/a8c2c49f-7a9b-4bf6-ae97-e4ed49637e66

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
theorem _root_.solution : PositionAfter := by
  intro c de de' Y l i h hw hw' hl hli hik hor hY
  obtain ⟨hY1, hY2⟩ := hY
  have hD := h.hDel
  have hnt : ¬ (c.top = true ∧ i + 1 = c.k) := by
    rintro ⟨h1, h2⟩
    rcases hor with h3 | h3
    · omega
    · rw [h1] at h3; exact absurd h3 (by decide)
  have hliR : (l:ℝ) + 1 ≤ i := by exact_mod_cast hli
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = -(c.v i + Y) := ⟨_, rfl⟩
  have hXge : 7 / 2 * c.Del ≤ X := by
    have e : c.v i = c.v l - 4 * c.Del * ((i:ℝ) - l) := by simp only [Cfg.v]; ring
    have : 4 * c.Del * 1 ≤ 4 * c.Del * ((i:ℝ) - l) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    rw [hX, e]; linarith
  simp only [Cfg.rho, if_neg hnt]
  have e1 : (c.v i - -Y) * (c.v i + 1 - -Y) = X * (X - 1) := by rw [hX]; ring
  have e2 : (c.v i - de i * c.Del - -Y) * (c.v i - de' i * c.Del - -Y) =
      (X + de i * c.Del) * (X + de' i * c.Del) := by rw [hX]; ring
  rw [e1, e2]
  have hX1 : 1 ≤ X := by linarith
  have ha : 0 ≤ de i * c.Del := by
    rcases hw.1 i with a | a <;> rw [a] <;> linarith
  have hb : 0 ≤ de' i * c.Del := by
    rcases hw'.1 i with a | a <;> rw [a] <;> linarith
  have hden : 0 < (X + de i * c.Del) * (X + de' i * c.Del) := by
    apply mul_pos <;> linarith
  rw [div_le_one (Real.sqrt_pos.mpr (abs_pos.mpr hden.ne'))]
  apply Real.sqrt_le_sqrt
  rw [abs_of_nonneg (mul_nonneg (by linarith) (by linarith)), abs_of_pos hden]
  nlinarith [mul_nonneg ha hb, mul_nonneg (by linarith : (0:ℝ) ≤ X) ha,
    mul_nonneg (by linarith : (0:ℝ) ≤ X) hb]
end Formalism.FourierDecayAlt.P
