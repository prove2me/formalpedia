-- Prove2me | solution 1 for Formalism.L2.DIV.level_idempotent_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:59.421818+00:00
-- url     : https://prove2.me/submissions/a57fe284-cb03-46ce-ac5e-a7bb480139e7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution : LvlIdemBot := by
  intro K _ G _ _ ψ
  unfold lvlIdem
  have hb : ∀ (inst : Fintype (⊥ : Subgroup G)) (F : (⊥ : Subgroup G) → MonoidAlgebra K G),
      @Finset.sum _ _ _ (@Finset.univ _ inst) F = F 1 := fun inst F => by
    convert Fintype.sum_subsingleton F 1
  rw [hb]
  simp [MonoidAlgebra.one_def]
end Formalism.L2.DIV
