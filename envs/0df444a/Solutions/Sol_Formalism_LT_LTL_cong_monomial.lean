-- Prove2me | solution 1 for Formalism.LT.LTL.cong_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:28:51.027079+00:00
-- url     : https://prove2.me/submissions/9a733d5f-0bf0-4bab-8ed5-1b8b2b2758ea

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
import Theorems.Thm_Formalism_LT_LTL_Near_mul
import Theorems.Thm_Formalism_LT_LTL_Near_pow
import Theorems.Thm_Formalism_LT_LTL_Cong_mul
import Theorems.Thm_Formalism_LT_LTL_cong_one
import Theorems.Thm_Formalism_LT_LTL_Cong_pow
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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}
namespace Formalism.LT.LTL
theorem _root_.solution {τ : Type*} {c : K} {a b : ι → MvPowerSeries τ K}
    (hab : ∀ i, Cong c (a i) (b i)) (m : ι →₀ ℕ) :
    Cong c (m.prod fun s e => a s ^ e) (m.prod fun s e => b s ^ e) := by
  classical
  unfold Finsupp.prod
  induction m.support using Finset.induction_on with
  | empty => simpa using cong_one c
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact ((hab j).pow (m j)).mul ih
end Formalism.LT.LTL
