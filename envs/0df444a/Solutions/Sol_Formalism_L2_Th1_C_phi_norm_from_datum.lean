-- Prove2me | solution 1 for Formalism.L2.Th1.C.phi_norm_from_datum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:03:33.400332+00:00
-- url     : https://prove2.me/submissions/c793ba21-9743-4ce7-9e25-45d514b6fb76

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntegralEndomorphismFromDatum
import Theorems.Thm_Formalism_L2_Th1_C_CompactOperatorsAlt_ne_zero_of_isEndoR
import Theorems.Thm_Formalism_L2_Th1_C_integral_endomorphism_from_datum
import Theorems.Thm_Formalism_L2_Th1_C_isogenyIffBar
import Theorems.Thm_Formalism_L2_Th1_C_phNormUnit


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
theorem _root_.solution : PhNormFromDatum := by
  intro K _ _ R e s2 l linv ph A c0 ι _ neg xP w xs al albar hL hPh hX hA h2 hD hs
  have hE : EndInt R l linv al :=
    integral_endomorphism_from_datum K R e l linv A c0 ι neg xP w xs al albar hL hX hA h2 hD
  obtain ⟨hZ, hN, -, -, hxP, hal, hali, -⟩ := hD
  have hal0 : al ≠ 0 := ne_zero_of_isEndoR hN
  have hI : IsogenyFormula e s2 (fun P => xP P + c0) al :=
    (isogenyIffBar K e s2 ι neg xP c0 w al albar hal0 hN hZ).mpr hs
  have := phNormUnit K R e s2 l linv ph A c0 ι xP al hL hPh hX hI hA hxP hal hali hal0 h2 hE
  show Cong R (PowerSeries.subst (mulBy l linv al) ph) ((al * albar) • ph)
  rw [hN]
  exact this
end Formalism.L2.Th1.C
