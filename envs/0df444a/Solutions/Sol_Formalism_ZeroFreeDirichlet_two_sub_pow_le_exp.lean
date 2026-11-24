-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.two_sub_pow_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:45:07.897892+00:00
-- url     : https://prove2.me/submissions/0635b5d4-7582-4138-b90b-4f2102133ed2

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_IteratedDerivLseriesAlternatingNonneg
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqKeyOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped ComplexOrder Nat
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {A P σ : ℝ} {M : ℕ} (hA : 0 ≤ A) (hσ1 : 7 / 8 ≤ σ) (hσ2 : σ < 1)
    (hM : (M : ℝ) ≤ A + P) : (2 - σ) ^ M ≤ Real.exp A * Real.exp (P * (1 - σ)) := by
  have h1 : 0 < 1 - σ := by linarith
  have hb : 2 - σ ≤ Real.exp (1 - σ) := by
    have := Real.add_one_le_exp (1 - σ); linarith
  have hb0 : 0 ≤ 2 - σ := by linarith
  calc (2 - σ) ^ M ≤ Real.exp (1 - σ) ^ M := pow_le_pow_left₀ hb0 hb M
    _ = Real.exp (M * (1 - σ)) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (A + P * (1 - σ)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hM h1.le, mul_nonneg hA (by linarith : (0 : ℝ) ≤ σ)]
    _ = Real.exp A * Real.exp (P * (1 - σ)) := Real.exp_add _ _
end Formalism.ZeroFreeDirichlet
