-- Prove2me | solution 1 for Formalism.L2.LamCM.spanSingleton_pow8_div_pow4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:12.942726+00:00
-- url     : https://prove2.me/submissions/90fb66c8-5ce7-4213-86ec-cdd44beec00e

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
theorem _root_.solution (a b : K) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (a ^ 8 / b ^ 4) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ a ^ 8 * (FractionalIdeal.spanSingleton (𝓞 K)⁰ b ^ 4)⁻¹ := by
  rw [FractionalIdeal.spanSingleton_pow, FractionalIdeal.spanSingleton_pow, FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.spanSingleton_mul_spanSingleton, div_eq_mul_inv]
end Formalism.L2.LamCM
