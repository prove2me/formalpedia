-- Prove2me | solution 1 for Formalism.L2.DIV.good_part_spec_of_central
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:29:36.142348+00:00
-- url     : https://prove2.me/submissions/d5f64cf5-c5eb-4211-8314-380005d2f71b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_range_V0E

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
theorem _root_.solution (h : IdemOfCentral) : GoodPartSpec := by
  intro K _ _ _ S G _ _ r X hX P ψ
  obtain ⟨hidem, hcent⟩ := h K G X hX
  exact range_V0E S r X P ψ hidem (hcent _)
end Formalism.L2.DIV
