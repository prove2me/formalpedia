-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.hasWt_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:53.282445+00:00
-- url     : https://prove2.me/submissions/58acc825-ab99-4a95-a0a1-4798f37b1744

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_coeff_sum_C_mul_X_pow


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
variable {k : Type*} [Field k] {Z C : Type*}
namespace Formalism.BaseCaseIdentities
theorem _root_.solution [Fintype Z] {v : AddValuation k (WithTop ℝ)} {r w : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (x : Z → k) (h : HasWt v r w (∑ d, MvPowerSeries.C (x d) * X d ^ M)) (d : Z) :
    HasWt v r w (MvPowerSeries.C (x d) * X d ^ M) := by
  intro A
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs with hA
  · subst hA
    have h1 := h (Finsupp.single d M)
    rw [coeff_sum_C_mul_X_pow] at h1
    have h2 : (∑ e, if Finsupp.single d M = Finsupp.single e M then x e else 0) = x d := by
      rw [Finset.sum_eq_single d]
      · simp
      · intro e _ hne
        rw [if_neg]
        intro heq
        exact hne ((Finsupp.single_left_inj (by omega)).1 heq).symm
      · simp
    rw [h2] at h1
    simpa using h1
  · simp
end Formalism.BaseCaseIdentities
