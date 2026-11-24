-- Prove2me | solution 1 for Formalism.L2.LamCM.count_pow8_inv_pow4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:13:18.234395+00:00
-- url     : https://prove2.me/submissions/7e2b4525-6221-4d02-a3e4-32f1b684de4a

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
theorem _root_.solution (p : HeightOneSpectrum (𝓞 K)) {A B : FractionalIdeal (𝓞 K)⁰ K} (hA : A ≠ 0)
    (hB : B ≠ 0) :
    FractionalIdeal.count K p (A ^ 8 * (B ^ 4)⁻¹) =
      8 * FractionalIdeal.count K p A - 4 * FractionalIdeal.count K p B := by
  rw [FractionalIdeal.count_mul K p (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB)),
    FractionalIdeal.count_inv, FractionalIdeal.count_pow, FractionalIdeal.count_pow]
  push_cast
  ring
end Formalism.L2.LamCM
