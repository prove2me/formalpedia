-- Prove2me | solution 1 for D1Bound5.bennettTwoBetaFactor_pos
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:33:37.125428+00:00
-- url     : https://prove2.me/submissions/1ee7d26d-9df4-4686-b7d2-c334f21e8a68

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoBetaBound_Definitions

section
namespace D1Bound5







theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) :
    0 < bennettTwoBetaFactor k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold bennettTwoBetaFactor
  exact div_pos
    (mul_pos (mul_pos (pow_pos (by norm_num) _)
      (Real.Gamma_pos_of_pos (by linarith))) (Real.Gamma_pos_of_pos (by linarith)))
    (mul_pos Real.pi_pos (Real.Gamma_pos_of_pos (by positivity)))













end D1Bound5
end
