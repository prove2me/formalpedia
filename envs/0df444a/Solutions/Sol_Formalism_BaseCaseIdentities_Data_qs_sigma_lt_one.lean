-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.qs_sigma_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:00:49.208466+00:00
-- url     : https://prove2.me/submissions/c323a960-5fdf-4242-a1dc-bb85cc6e2783

import Definitions.Def_Formalism_FrobeniusBaseCase_StatementFix
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_FixAll
import Theorems.Thm_Formalism_BaseCaseIdentities_identity_twenty_d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
open Formalism.BaseCaseIdentities.Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution (s : ℕ) (hsK : s < D.K) : qnum D.l ^ s * sg D.l D.i < 1 := by
  have hl : (3 : ℝ) ≤ (D.l : ℝ) := by exact_mod_cast D.l_ge
  have h1 := identity_twenty_d D.l D.i (by have := D.l_ge; omega) D.i_odd
  have hq1 : (1 : ℝ) ≤ qnum D.l := by unfold qnum; nlinarith
  have hsg : 0 < sg D.l D.i := by unfold sg; positivity
  have h2 : qnum D.l ^ (s + 1) ≤ qnum D.l ^ Kn D.i := pow_le_pow_right₀ hq1 hsK
  have h3 : qnum D.l ^ (s + 1) * sg D.l D.i ≤ 3 * (D.l : ℝ) / 8 := by
    rw [← h1]; exact mul_le_mul_of_nonneg_right h2 hsg.le
  by_contra hcon
  rw [not_lt] at hcon
  have h4 : qnum D.l ^ (s + 1) * sg D.l D.i = (qnum D.l ^ s * sg D.l D.i) * qnum D.l := by
    rw [pow_succ]; ring
  rw [h4] at h3
  have h5 : qnum D.l ≤ (qnum D.l ^ s * sg D.l D.i) * qnum D.l := by nlinarith
  unfold qnum at h5 h3
  nlinarith
end Formalism.BaseCaseIdentities.Data
