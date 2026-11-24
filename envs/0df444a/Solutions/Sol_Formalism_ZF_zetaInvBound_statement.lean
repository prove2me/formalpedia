-- Prove2me | solution 1 for Formalism.ZF.zetaInvBound_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:10:41.846434+00:00
-- url     : https://prove2.me/submissions/b4334297-33ea-408e-9b49-e08ae2729137

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaInvBound
import Theorems.Thm_Formalism_ZF_MoebiusInverseZetaBounds_summable_shift
import Theorems.Thm_Formalism_ZF_MoebiusInverseZetaBounds_tsum_rpow_le
import Theorems.Thm_Formalism_ZF_MoebiusInverseZetaBounds_norm_term_one_succ
import Theorems.Thm_Formalism_ZF_MoebiusInverseZetaBounds_norm_term_moebius_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology LSeries ArithmeticFunction
noncomputable section
open Formalism Formalism.ZF
open MoebiusInverseZetaBounds
namespace Formalism.ZF
theorem _root_.solution : ZetaInvBound := by
  intro s hs
  have hL := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at hL
  have hinv := eq_inv_of_mul_eq_one_right hL
  rw [← norm_inv, ← hinv]
  have hσ : 0 < s.re - 1 := by linarith
  have hsum1 : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) := summable_shift (by linarith)
  have hs1 : Summable fun n => ‖term (1 : ℕ → ℂ) s n‖ := by
    rw [← summable_nat_add_iff 1]
    simpa only [norm_term_one_succ] using hsum1
  have hsμ : Summable fun n => ‖term (fun n => ((moebius n : ℤ) : ℂ)) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_moebius_le s) hs1
  calc ‖LSeries (fun n => ((moebius n : ℤ) : ℂ)) s‖
      ≤ ∑' n, ‖term (fun n => ((moebius n : ℤ) : ℂ)) s n‖ := norm_tsum_le_tsum_norm hsμ
    _ ≤ ∑' n, ‖term (1 : ℕ → ℂ) s n‖ := Summable.tsum_le_tsum (norm_term_moebius_le s) hsμ hs1
    _ = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) := by
      rw [hs1.tsum_eq_zero_add]
      simp only [LSeries.term_zero, norm_zero, zero_add, norm_term_one_succ]
    _ ≤ 1 + 1 / (s.re - 1) := tsum_rpow_le hσ
    _ = s.re / (s.re - 1) := by
      field_simp
      ring
end Formalism.ZF
