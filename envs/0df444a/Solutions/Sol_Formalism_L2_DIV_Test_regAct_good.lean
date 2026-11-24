-- Prove2me | solution 1 for Formalism.L2.DIV.Test.regAct_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:13:31.109601+00:00
-- url     : https://prove2.me/submissions/bef83094-4fd6-4062-952c-ab41d783b2d3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_Test_reg_csum

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
theorem _root_.solution : (regCSD K G).ActGood (regAct K G) where
  unitary := by
    intro t f g
    rw [reg_csum, reg_csum]
    exact Equiv.sum_comp (Equiv.mulRight t) (fun c : G => star ((f.1 : G → K) c) * (g.1 : G → K) c)
  nab_stable := by
    intro t f hf c
    exact hf ((c : G) * t)
  del_stable := by
    intro t f hf c
    exact hf ((c : G) * t)
end Formalism.L2.DIV.Test
