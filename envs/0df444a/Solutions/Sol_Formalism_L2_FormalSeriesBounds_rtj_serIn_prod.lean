-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rtj_serIn_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:02.950808+00:00
-- url     : https://prove2.me/submissions/f707e902-1773-4a17-81ae-6b055af4701a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_serIn_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_serIn_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {ι : Type} (A : Set σ) (s : Finset ι) (F : ι → MvPowerSeries σ K)
    (hF : ∀ i ∈ s, rtjSerIn A (F i)) : rtjSerIn A (∏ i ∈ s, F i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact rtj_serIn_one A
  | insert i t hi ih =>
    rw [Finset.prod_insert hi]
    exact rtj_serIn_mul (hF i (Finset.mem_insert_self i t))
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))
end Formalism.L2.FormalSeriesBounds
