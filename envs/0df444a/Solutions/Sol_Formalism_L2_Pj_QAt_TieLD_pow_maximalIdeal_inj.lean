-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLD.pow_maximalIdeal_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:39:01.927988+00:00
-- url     : https://prove2.me/submissions/31f70697-0a52-49ad-ae7c-35dd837b7643

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_LenDescentOfLengthBaseChangeLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open Formalism.L2.Pj.QAt.TieLD
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
attribute [local instance] TieLDA.modT TieLDA.modR
namespace Formalism.L2.Pj.QAt.TieLD
theorem _root_.solution {T : Type*} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    {a b : ℕ} (h : IsLocalRing.maximalIdeal T ^ a = IsLocalRing.maximalIdeal T ^ b) : a = b := by
  have h0 : IsLocalRing.maximalIdeal T ≠ ⊥ := IsDiscreteValuationRing.not_a_field T
  have h1 : IsLocalRing.maximalIdeal T ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal T).ne_top
  exact (Ideal.pow_right_strictAnti _ h0 h1).injective h
end Formalism.L2.Pj.QAt.TieLD
