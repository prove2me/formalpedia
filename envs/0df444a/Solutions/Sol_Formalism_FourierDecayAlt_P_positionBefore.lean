-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.positionBefore
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:54.32182+00:00
-- url     : https://prove2.me/submissions/29201aae-7a78-4e22-8d2a-b2bd07e6ff4f

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
theorem _root_.solution : PositionBefore := by
  intro c de de' Y l i h hw hw' hi hil hlk hY
  obtain ⟨hY1, hY2⟩ := hY
  have hD := h.hDel
  have hnt : ¬ (c.top = true ∧ i + 1 = c.k) := by rintro ⟨_, h2⟩; omega
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (l:ℝ) - i := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by
    have : (i:ℝ) + 1 ≤ l := by exact_mod_cast hil
    rw [hp]; linarith
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = c.v l + Y := ⟨_, rfl⟩
  rw [← hd] at hY1 hY2
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 4 * c.Del * p + d := ⟨_, rfl⟩
  have hXv : c.v i + Y = X := by rw [hX, hd, hp]; simp only [Cfg.v]; ring
  simp only [Cfg.rho, if_neg hnt]
  rw [← hp]
  have e1 : (c.v i - -Y) * (c.v i + 1 - -Y) = X * (X + 1) := by rw [← hXv]; ring
  have e2 : (c.v i - de i * c.Del - -Y) * (c.v i - de' i * c.Del - -Y) =
      (X - de i * c.Del) * (X - de' i * c.Del) := by rw [← hXv]; ring
  rw [e1, e2]
  have mp : 4 * c.Del * 1 ≤ 4 * c.Del * p := mul_le_mul_of_nonneg_left hp1 (by linarith)
  have hXD : 0 < X - c.Del := by rw [hX]; linarith
  have hX0 : 0 < X := by linarith
  have ha : X - c.Del ≤ X - de i * c.Del := by
    rcases hw.1 i with a | a <;> rw [a] <;> linarith
  have hb : X - c.Del ≤ X - de' i * c.Del := by
    rcases hw'.1 i with a | a <;> rw [a] <;> linarith
  have hnum : Real.sqrt |X * (X + 1)| ≤ X + 1 := by
    rw [abs_of_pos (by positivity), Real.sqrt_le_iff]; exact ⟨by linarith, by nlinarith⟩
  have hden : X - c.Del ≤ Real.sqrt |(X - de i * c.Del) * (X - de' i * c.Del)| := by
    apply Real.le_sqrt_of_sq_le
    rw [abs_of_pos (mul_pos (by linarith) (by linarith)), sq]
    exact mul_le_mul ha hb hXD.le (by linarith)
  have h4p : 0 < 4 * p - 1 := by linarith
  have e3 : 1 + 2 / (4 * p - 1) = (4 * p + 1) / (4 * p - 1) := by field_simp; ring
  calc _ ≤ (X + 1) / (X - c.Del) := div_le_div₀ (by linarith) hnum hXD hden
    _ ≤ 1 + 2 / (4 * p - 1) := by
      rw [e3, div_le_div_iff₀ hXD h4p, hX]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ p - 1) (by linarith : (0:ℝ) ≤ c.Del - 1)]
end Formalism.FourierDecayAlt.P
