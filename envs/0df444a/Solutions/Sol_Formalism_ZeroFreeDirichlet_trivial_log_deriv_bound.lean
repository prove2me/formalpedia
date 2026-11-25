-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.trivial_log_deriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:19:04.586341+00:00
-- url     : https://prove2.me/submissions/9c98252b-a21a-4c74-a3b7-d194bb9ed73b

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_EulerFactorLogDerivBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZetaLogDerivLandauBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_TrivLogDeriv
import Theorems.Thm_Formalism_ZeroFreeDirichlet_re_negLogDeriv_le
import Theorems.Thm_Formalism_ZeroFreeDirichlet_zeta_neg_log_deriv_re_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution : TrivLogDeriv := by
  obtain ⟨K, hK0, hK⟩ := zeta_neg_log_deriv_re_bound
  refine ⟨K + 1, fun q _ σ t hσ hσ2 => ?_⟩
  have hs : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have h1 := re_negLogDeriv_le q ((σ : ℂ) + t * I) hs
  have h2 := hK σ t hσ hσ2
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hT : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hlog : Real.log ((q : ℝ) * (|t| + 2)) = Real.log q + Real.log (|t| + 2) :=
    Real.log_mul (by linarith : (0 : ℝ) < q).ne' (by linarith [abs_nonneg t] : (0 : ℝ) < |t| + 2).ne'
  rw [hlog]
  nlinarith [mul_nonneg hK0 hlq]
end Formalism.ZeroFreeDirichlet
