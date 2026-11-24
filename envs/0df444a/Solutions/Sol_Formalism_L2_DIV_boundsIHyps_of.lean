-- Prove2me | solution 1 for Formalism.L2.DIV.boundsIHyps_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:54:55.983532+00:00
-- url     : https://prove2.me/submissions/be2c335d-908b-46cd-bd23-38cd9571ca7d

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
theorem _root_.solution (h1 : CutOrthProj) (h2 : GoodAtSpec) (h3 : ActLat) : BoundsIHyps := by
  intro K _ _ _ v0 hv S hpos G _ _ r hr X hX P ψ
  have hP := h2 K v0 hv G X hX P ψ
  obtain ⟨hO, hEP⟩ := h1 K v0 hv S hpos G r hr (goodAt X P ψ) hP.idem hP.selfAdj
  exact ⟨hO, hEP, hP.integral, fun t x hx => (h3 K S G r hr t).2 x hx⟩
end Formalism.L2.DIV
