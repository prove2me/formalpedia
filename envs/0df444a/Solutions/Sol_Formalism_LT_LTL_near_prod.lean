-- Prove2me | solution 1 for Formalism.LT.LTL.near_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:33:38.833589+00:00
-- url     : https://prove2.me/submissions/eb3fd675-2f1c-4f3a-a55e-f48617325866

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_Near_of_eq
import Theorems.Thm_Formalism_LT_LTL_Near_mul
import Theorems.Thm_Formalism_LT_LTL_near_one
import Theorems.Thm_Formalism_LT_LTL_Near_pow
import Theorems.Thm_Formalism_G_LogCR_Agree_mul
import Theorems.Thm_Formalism_LT_InvIntP_Low_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] {ι : Type*}
namespace Formalism.LT.LTL
theorem _root_.solution {τ : Type*} [DecidableEq ι] {a b : ι → MvPowerSeries τ K}
    (hab : ∀ i, Near 1 (a i) (b i)) (m : ι → ℕ) (s : Finset ι) :
    Near (∑ i ∈ s, m i) (∏ i ∈ s, a i ^ m i) (∏ i ∈ s, b i ^ m i) := by
  induction s using Finset.induction_on with
  | empty => simpa using near_one
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    exact (((hab j).pow (m j)).mul ih).of_eq (by ring)
end Formalism.LT.LTL
