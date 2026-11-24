-- Prove2me | solution 1 for Formalism.REAL.compactCasimirValue_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:43:14.936258+00:00
-- url     : https://prove2.me/submissions/05274735-1b7f-4cf0-8023-5db17139cab0

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf
import Theorems.Thm_Formalism_REAL_abs_compactHalfSum_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) (R : ℝ)
    (hμ : ∀ a, |μ a| ≤ R) : ckv ε μ ≤ n * (R + n) ^ 2 := by
  unfold ckv nsq dot
  have h0 : 0 ≤ ∑ a, rhoC ε a * rhoC ε a := Finset.sum_nonneg fun a _ => mul_self_nonneg _
  have h1 : ∑ a, (μ + rhoC ε) a * (μ + rhoC ε) a ≤ ∑ _a : Fin n, (R + n) ^ 2 := by
    apply Finset.sum_le_sum
    intro a _
    simp only [Pi.add_apply]
    have h3 : |μ a + rhoC ε a| ≤ R + n :=
      (abs_add_le (μ a) (rhoC ε a)).trans (add_le_add (hμ a) (abs_compactHalfSum_le ε a))
    rw [← sq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  linarith
end Formalism.REAL
