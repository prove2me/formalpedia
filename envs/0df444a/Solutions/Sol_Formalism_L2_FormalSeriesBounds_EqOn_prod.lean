-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.EqOn.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:41:58.799315+00:00
-- url     : https://prove2.me/submissions/61126ad4-549b-4a05-b3d0-fcfce17afdd2

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCut
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LeafHolds
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_refl
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul


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
namespace EqOn
theorem _root_.solution {A : Set σ} {ι : Type} (s : Finset ι) {F G : ι → MvPowerSeries σ K}
    (h : ∀ i ∈ s, EqOn A (F i) (G i)) : EqOn A (∏ i ∈ s, F i) (∏ i ∈ s, G i) := by
  induction s using Finset.induction_on with
  | empty => simpa using EqOn.refl A (1 : MvPowerSeries σ K)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end EqOn
end Formalism.L2.FormalSeriesBounds
