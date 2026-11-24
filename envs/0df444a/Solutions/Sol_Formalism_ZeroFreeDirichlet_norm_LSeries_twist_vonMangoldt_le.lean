-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.norm_LSeries_twist_vonMangoldt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:44:11.838127+00:00
-- url     : https://prove2.me/submissions/15efcb17-98d8-4bd8-8ddb-9c3e55ab31c0

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
theorem _root_.solution {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖L (↗χ * ↗Λ) s‖ ≤ Formalism.ZF.lamF s.re := by
  have hre : 1 < (s.re : ℂ).re := by simpa using hs
  have hSΛ : Summable fun n => ‖term ↗Λ (s.re : ℂ) n‖ :=
    summable_norm_iff.2 (ArithmeticFunction.LSeriesSummable_vonMangoldt hre)
  have hle : ∀ n, ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term ↗Λ (s.re : ℂ) n‖ := by
    intro n
    calc ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term ↗Λ s n‖ := by
          apply LSeries.norm_term_le
          simp only [Pi.mul_apply, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
      _ = ‖term ↗Λ (s.re : ℂ) n‖ := by
          rw [LSeries.norm_term_eq, LSeries.norm_term_eq, Complex.ofReal_re]
  have hS2 : Summable fun n => ‖term (↗χ * ↗Λ) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hSΛ
  calc ‖L (↗χ * ↗Λ) s‖ = ‖∑' n, term (↗χ * ↗Λ) s n‖ := rfl
    _ ≤ ∑' n, ‖term (↗χ * ↗Λ) s n‖ := norm_tsum_le_tsum_norm hS2
    _ ≤ ∑' n, ‖term ↗Λ (s.re : ℂ) n‖ := Summable.tsum_le_tsum hle hS2 hSΛ
    _ = Formalism.ZF.lamF s.re := rfl
end Formalism.ZeroFreeDirichlet
