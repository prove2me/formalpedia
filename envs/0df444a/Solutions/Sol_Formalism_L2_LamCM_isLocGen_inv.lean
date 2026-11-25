-- Prove2me | solution 1 for Formalism.L2.LamCM.isLocGen_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:09:32.579008+00:00
-- url     : https://prove2.me/submissions/74b1f390-3619-4068-8867-13841856d481

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementB
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ValuationLeOfEqAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM
theorem _root_.solution {p : HeightOneSpectrum (𝓞 K)} {c : K} {I : FractionalIdeal (𝓞 K)⁰ K}
    (h : IsLocGen p c I) : IsLocGen p c⁻¹ I⁻¹ := by
  refine ⟨inv_ne_zero h.1, ?_⟩
  rw [← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, FractionalIdeal.count_inv, h.2]
end Formalism.L2.LamCM
