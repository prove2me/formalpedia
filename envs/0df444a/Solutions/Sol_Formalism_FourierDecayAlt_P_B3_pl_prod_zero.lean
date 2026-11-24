-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.pl_prod_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:59:06.127122+00:00
-- url     : https://prove2.me/submissions/71eb71c9-f9de-4ef6-a501-0c7ca516b09a

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B3
open Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B3
theorem _root_.solution {a₁ b₁ a₂ b₂ k : ℝ} (hk : 0 ≤ k) {τ : ℝ × ℝ} (hτ : τ ∉ Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) :
    pl a₁ b₁ k τ.1 * pl a₂ b₂ k τ.2 = 0 := by
  rw [Set.mem_prod, not_and_or] at hτ
  rcases hτ with h | h
  · rw [pl_eq_zero hk h, zero_mul]
  · rw [pl_eq_zero hk h, mul_zero]
end Formalism.FourierDecayAlt.P.B3
