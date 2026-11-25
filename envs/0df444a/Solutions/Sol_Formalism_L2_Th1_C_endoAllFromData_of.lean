-- Prove2me | solution 1 for Formalism.L2.Th1.C.endoAllFromData_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:28:43.889773+00:00
-- url     : https://prove2.me/submissions/5658d42a-c4dd-4655-b51a-5e3b8d9ddb4e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralEndomorphismFromDatum
import Theorems.Thm_Formalism_L2_Th1_C_integral_endomorphism_from_datum
import Theorems.Thm_Formalism_L2_Th1_C_phi_norm_from_datum

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
open CompactOperatorsAlt
namespace Formalism.L2.Th1.C
theorem _root_.solution (hA : EndoAll) : EndoAllFromData := by
  intro K _ _ _ _ R hR e s2 l linv ph A c0 hF hF1 hPh hX hA1 O _ _ _ τ hτ hstar hself h2 h2O hsum
    Dn hDn hdata
  refine hA K R hR l linv ph hF hF1 O τ hτ hstar hself h2 h2O hsum Dn hDn ?_
  intro α hα
  obtain ⟨ι, _, neg, xP, w, xs, hD, hs⟩ := hdata α hα
  exact ⟨integral_endomorphism_from_datum K R e l linv A c0 ι neg xP w xs _ _ hF.1 hX hA1 h2 hD,
    phi_norm_from_datum K R e s2 l linv ph A c0 ι neg xP w xs _ _ hF.1 hPh hX hA1 h2 hD hs⟩
end Formalism.L2.Th1.C
