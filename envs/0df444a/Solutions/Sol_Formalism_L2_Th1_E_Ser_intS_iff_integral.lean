-- Prove2me | solution 1 for Formalism.L2.Th1.E.Ser.intS_iff_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:09.631585+00:00
-- url     : https://prove2.me/submissions/13564747-0e82-4c92-a005-b7bc767c1bdc

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Ser
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.L2.Th1.E.Ser
theorem _root_.solution (f : K⟦X⟧) : IntS f ↔ Formalism.DworkPowerSeriesWeights.Integral (ι := Unit) f := by
  constructor
  · intro h n
    have := h (n ())
    rwa [coeff_def (s := n) rfl] at this
  · intro h n
    exact h (Finsupp.single () n)
end Formalism.L2.Th1.E.Ser
