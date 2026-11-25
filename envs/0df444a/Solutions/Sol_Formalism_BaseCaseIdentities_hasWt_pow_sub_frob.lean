-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.hasWt_pow_sub_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:23:55.467137+00:00
-- url     : https://prove2.me/submissions/80fef078-ac32-4a23-be1e-cf6761e36757

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Theorems.Thm_Formalism_BaseCaseIdentities_hasWt_term
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_frob_sum_X
import Theorems.Thm_Formalism_BaseCaseIdentities_hasWt_sum_pow_sub


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
theorem _root_.solution [Fintype Z] {v : AddValuation k (WithTop ℝ)} {r w : ℝ} {l e M : ℕ}
    (hl : l.Prime) (hv : v (l : k) = 1) (he : 1 ≤ e) (hM : 1 ≤ M)
    (x : Z → k) (h : HasWt v r w (∑ d, MvPowerSeries.C (x d) * X d ^ M)) :
    HasWt v r (1 + ((l ^ e : ℕ) : ℝ) * w)
      ((∑ d, MvPowerSeries.C (x d) * X d ^ M) ^ (l ^ e)
        - frob (l ^ e) (∑ d, MvPowerSeries.C (x d) * X d ^ M)) := by
  have h1 := hasWt_sum_pow_sub hl hv he Finset.univ (fun d _ => hasWt_term hM x h d)
  rw [frob_sum_X (Nat.one_le_pow _ _ hl.pos) hM]
  have h2 : ∀ d, (MvPowerSeries.C (x d) * X d ^ M : MvPowerSeries Z k) ^ (l ^ e)
      = MvPowerSeries.C (x d ^ (l ^ e)) * X d ^ (l ^ e * M) := by
    intro d
    rw [mul_pow, ← map_pow, ← pow_mul, mul_comm M]
  simpa only [h2] using h1
end Formalism.BaseCaseIdentities
