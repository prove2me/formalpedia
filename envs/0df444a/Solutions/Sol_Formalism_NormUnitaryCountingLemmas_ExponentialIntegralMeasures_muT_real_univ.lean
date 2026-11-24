-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures.muT_real_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:09:58.794224+00:00
-- url     : https://prove2.me/submissions/2848580b-6a3f-427d-8ed9-fc21320ec137

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_IntegralExpInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures
namespace Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures
theorem _root_.solution (G : ℕ) : (muT G).real Set.univ = (2 * Real.pi) ^ G := by
  rw [Measure.real, Measure.pi_univ, ENNReal.toReal_prod]
  simp [Real.volume_Ioc, Real.pi_pos.le]
end Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures
