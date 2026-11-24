-- Prove2me | solution 1 for Formalism.L2.LamCM.count_eq_of_valuation_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:18:34.757393+00:00
-- url     : https://prove2.me/submissions/4c9ca1a9-01c4-423e-a713-9c21361acacf

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementB
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ValuationLeOfEqAlgebraMap
import Theorems.Thm_Formalism_L2_LamCM_valuation_eq_exp_neg_count

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
theorem _root_.solution (p : HeightOneSpectrum (𝓞 K)) {k c : K} (hk : k ≠ 0) (hc : c ≠ 0)
    (h1 : p.valuation K k ≤ p.valuation K c) (h2 : p.valuation K k⁻¹ ≤ p.valuation K c⁻¹) :
    FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ k) =
      FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ c) := by
  rw [valuation_eq_exp_neg_count p hk, valuation_eq_exp_neg_count p hc, WithZero.exp_le_exp] at h1
  rw [valuation_eq_exp_neg_count p (inv_ne_zero hk), valuation_eq_exp_neg_count p (inv_ne_zero hc),
    WithZero.exp_le_exp, ← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.count_inv, FractionalIdeal.count_inv] at h2
  omega
end Formalism.L2.LamCM
