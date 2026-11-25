-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:01:19.305002+00:00
-- url     : https://prove2.me/submissions/133024f6-db9a-40f5-9571-3145216adec2

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_inWTo_iff
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_mu_succ
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_wt_contrib
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_opIsLimit
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_neg
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum


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
theorem _root_.solution (J : ℕ) (hJ1 : 1 ≤ J) (hJK : J ≤ D.K) (t : C → MvPowerSeries Z k)
    (hnc : NoConst t) (ht : D.InWTo J t) : D.InWTo (min (J + 1) D.K) (D.Psi t) := by
  rw [inWTo_iff] at ht ⊢
  intro b A
  have h1 : coeff A (D.Psi t b - D.mu (min (J + 1) D.K) b) =
      coeff A (D.PsiPartial (max A.degree 2) t b - D.mu (min (J + 1) D.K) b) := by
    rw [map_sub, map_sub, D.opIsLimit t hnc b A _ (le_max_left _ _)]
  rw [h1]
  have h2 : D.PsiPartial (max A.degree 2) t b - D.mu (min (J + 1) D.K) b =
      -∑ c, (∑ j ∈ Finset.Icc 1 (max A.degree 2),
        MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j) + D.main J c b) := by
    rw [D.mu_succ J hJ1 hJK b, PsiPartial, Finset.sum_add_distrib]
    ring
  rw [h2]
  exact (HasWt.neg (HasWt.sum _ fun c _ =>
    D.wt_contrib J hJK t ht _ (le_max_right _ _) c b)) A
end Formalism.BaseCaseIdentities.Data
