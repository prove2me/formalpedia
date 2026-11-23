-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz3.xx_bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:39:38.813969+00:00
-- url     : https://prove2.me/submissions/ddd34c32-b7f6-4007-8d6e-d7d082d6306f

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz3
theorem _root_.solution (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) (i i' : ℕ) (h : i < i') :
    |xx de i i'| ≤ 1 / 4 ∧ (xx de i i') ^ 2 ≤ 1 / 16 * (1 / (((i' - i : ℕ) : ℝ)) ^ 2) := by
  have hR : (i : ℝ) + 1 ≤ (i' : ℝ) := by exact_mod_cast h
  have hc : ((i' - i : ℕ) : ℝ) = (i' : ℝ) - i := by rw [Nat.cast_sub h.le]
  have hpos : (0 : ℝ) < (i' : ℝ) - i := by linarith
  have hnum : |de i' - de i| ≤ 1 := by
    rcases hde i with h1 | h1 <;> rcases hde i' with h2 | h2 <;> rw [h1, h2] <;> norm_num
  constructor
  · unfold xx
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * ((i' : ℝ) - i)),
      div_le_iff₀ (by positivity)]
    linarith
  · unfold xx
    rw [hc, div_pow, mul_pow, ← sq_abs (de i' - de i)]
    have : |de i' - de i| ^ 2 ≤ 1 := by
      have h0 := abs_nonneg (de i' - de i)
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    have e : 1 / 16 * (1 / ((i' : ℝ) - i) ^ 2) * (4 ^ 2 * ((i' : ℝ) - i) ^ 2) = 1 := by
      field_simp; norm_num
    rw [e]; exact this
end Formalism.FourierDecayAlt.P.Sz3
