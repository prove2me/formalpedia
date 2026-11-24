-- Prove2me | solution 1 for Formalism.L2.Th1.C.CompactOperatorsAlt.isOneUnit_veluXs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:33:47.296804+00:00
-- url     : https://prove2.me/submissions/18707905-5d69-4830-aeb5-3d85d7604f3e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralEndomorphismFromDatum
import Theorems.Thm_Formalism_L2_Th1_C_USideA_intPS_C
import Theorems.Thm_Formalism_L2_Th1_C_USideA_intPS_X_pow
import Theorems.Thm_Formalism_L2_Th1_C_USideA_intPS_add
import Theorems.Thm_Formalism_L2_Th1_C_USideA_intPS_mul
import Theorems.Thm_Formalism_L2_Th1_C_USideA_intPS_sub
import Theorems.Thm_Formalism_L2_Th1_C_USideA_intPS_sum


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
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.CompactOperatorsAlt
variable {K : Type} [Field K] {R : Subring K}
namespace Formalism.L2.Th1.C.CompactOperatorsAlt
theorem _root_.solution {A : PowerSeries K} {ι : Type} [Fintype ι] {xs : ι → PowerSeries K}
    {xP : ι → K} {r : K} (hA : IsOneUnit R A) (hxs : ∀ P, IntPS R (xs P)) (hxP : ∀ P, xP P ∈ R)
    (hr : r ∈ R) : IsOneUnit R (veluXs A xs xP r) := by
  refine ⟨by simp [veluXs, hA.1], ?_⟩
  exact USideA.intPS_add hA.2 (USideA.intPS_mul (USideA.intPS_X_pow 2)
    (USideA.intPS_sub (USideA.intPS_sum _ fun P _ =>
      USideA.intPS_sub (hxs P) (USideA.intPS_C (hxP P))) (USideA.intPS_C hr)))
end Formalism.L2.Th1.C.CompactOperatorsAlt
