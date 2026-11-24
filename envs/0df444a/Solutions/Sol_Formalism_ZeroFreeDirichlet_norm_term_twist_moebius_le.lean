-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.norm_term_twist_moebius_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:45:15.112371+00:00
-- url     : https://prove2.me/submissions/eaaa1df3-339e-4768-bb8d-fa051cfe3665

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaInvBound
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivRight
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation ArithmeticFunction.Moebius
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) :
    ‖term (↗χ * ↗μ) s n‖ ≤ ‖term (1 : ℕ → ℂ) s n‖ := by
  apply LSeries.norm_term_le
  simp only [Pi.mul_apply, Pi.one_apply, norm_one, norm_mul]
  have h1 := DirichletCharacter.norm_le_one χ (n : ZMod q)
  have h2 : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  exact mul_le_one₀ h1 (norm_nonneg _) h2
end Formalism.ZeroFreeDirichlet
