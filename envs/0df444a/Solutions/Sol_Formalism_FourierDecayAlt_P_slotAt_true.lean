-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.slotAt_true
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:58.176467+00:00
-- url     : https://prove2.me/submissions/fb66094b-f284-4dda-9e8c-24470aa650b9

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
theorem _root_.solution : PositionAt := by
  intro c de de' Y l h hw hw' hl hlk hne hY
  obtain ⟨hY1, hY2⟩ := hY
  have hD := h.hDel
  set d := c.v l + Y with hd
  have hnt : ¬ (c.top = true ∧ l + 1 = c.k) := by rintro ⟨_, h2⟩; omega
  have hd0 : 0 < d := by linarith
  have hDd : 0 < c.Del - d := by linarith
  have e1 : c.v l - -Y = d := by rw [hd]; ring
  have e2 : c.v l + 1 - -Y = d + 1 := by rw [hd]; ring
  have hden : |(c.v l - de l * c.Del - -Y) * (c.v l - de' l * c.Del - -Y)| = d * (c.Del - d) := by
    rcases hw.1 l with a | a <;> rcases hw'.1 l with b | b
    · exact absurd (a.trans b.symm) hne
    · rw [a, b]
      have : (c.v l - 0 * c.Del - -Y) * (c.v l - 1 * c.Del - -Y) = -(d * (c.Del - d)) := by rw [hd]; ring
      rw [this, abs_neg, abs_of_pos (mul_pos hd0 hDd)]
    · rw [a, b]
      have : (c.v l - 1 * c.Del - -Y) * (c.v l - 0 * c.Del - -Y) = -(d * (c.Del - d)) := by rw [hd]; ring
      rw [this, abs_neg, abs_of_pos (mul_pos hd0 hDd)]
    · exact absurd (a.trans b.symm) hne
  have hrho : c.rho de de' (-Y) l = Real.sqrt ((d + 1) / (c.Del - d)) := by
    simp only [Cfg.rho, if_neg hnt, hden, e1, e2]
    rw [abs_of_pos (by positivity), ← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  refine ⟨hrho, ?_⟩
  rw [hrho]
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ hDd (by positivity)]
  nlinarith
end Formalism.FourierDecayAlt.P
