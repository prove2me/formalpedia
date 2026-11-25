-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.IsIU.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:30.300183+00:00
-- url     : https://prove2.me/submissions/861949bf-570b-4070-8f71-3f7ad186150c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValU
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_IsIU_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_IsIU_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWtG_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWtG_one
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_one
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_one


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
namespace Formalism.L2.FormalSeriesBounds
namespace IsIU
theorem _root_.solution {σ ι : Type} (s : Finset ι) {U : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IsIU V (U i)) :
    IsIU V (∏ i ∈ s, U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact IsIU.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end IsIU
end Formalism.L2.FormalSeriesBounds
