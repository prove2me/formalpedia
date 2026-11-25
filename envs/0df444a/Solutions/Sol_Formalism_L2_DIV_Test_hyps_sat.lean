-- Prove2me | solution 1 for Formalism.L2.DIV.Test.hyps_sat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:28:12.101531+00:00
-- url     : https://prove2.me/submissions/76b70419-69a0-4a06-be56-2c121479fda3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_Test_regAct_good
import Theorems.Thm_Formalism_L2_DIV_Test_isAbsIrrChar_one
import Theorems.Thm_Formalism_L2_DIV_Test_reg_good
import Theorems.Thm_Formalism_L2_DIV_Test_reg_H_posDef
import Theorems.Thm_Formalism_L2_DIV_Test_reg_V0dim_pos_lvl
import Theorems.Thm_Formalism_L2_DIV_Test_rat_isConjAt

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
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.Test
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
namespace Formalism.L2.DIV.Test
theorem _root_.solution (P : Subgroup (Equiv.Perm (Fin 3))) :
    ∃ v0 : InfinitePlace ℚ, IsConjAt v0 ∧
      (regCSD ℚ (Equiv.Perm (Fin 3))).Good 1 ∧
      ((regCSD ℚ (Equiv.Perm (Fin 3))).H.map v0.embedding).PosDef ∧
      (regCSD ℚ (Equiv.Perm (Fin 3))).ActGood (regAct ℚ (Equiv.Perm (Fin 3))) ∧
      (∀ χ ∈ ({fun _ => (1 : ℚ)} : Finset (Equiv.Perm (Fin 3) → ℚ)), IsAbsIrrChar χ) ∧
      0 < (regCSD ℚ (Equiv.Perm (Fin 3))).BaseDimension (regAct ℚ (Equiv.Perm (Fin 3)))
        ({fun _ => (1 : ℚ)} : Finset (Equiv.Perm (Fin 3) → ℚ)) P 1 := by
  have v0 : InfinitePlace ℚ := by
    first
    | exact Rat.infinitePlace
    | exact Classical.choice inferInstance
  exact ⟨v0, rat_isConjAt v0, reg_good ℚ _, reg_H_posDef ℚ _ v0 (rat_isConjAt v0), regAct_good ℚ _,
    fun χ hχ => (Finset.mem_singleton.mp hχ) ▸ isAbsIrrChar_one ℚ _, reg_V0dim_pos_lvl ℚ _ P⟩
end Formalism.L2.DIV.Test
