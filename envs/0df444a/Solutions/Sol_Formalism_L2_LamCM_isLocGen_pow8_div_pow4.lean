-- Prove2me | solution 1 for Formalism.L2.LamCM.isLocGen_pow8_div_pow4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:18:36.651611+00:00
-- url     : https://prove2.me/submissions/4c93ac5b-1c33-48ad-8f80-089f6958cf45

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementB
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ValuationLeOfEqAlgebraMap
import Theorems.Thm_Formalism_L2_LamCM_count_pow8_inv_pow4
import Theorems.Thm_Formalism_L2_LamCM_spanSingleton_pow8_div_pow4

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
theorem _root_.solution {p : HeightOneSpectrum (𝓞 K)} {ca cd : K} {A B : FractionalIdeal (𝓞 K)⁰ K}
    (hA : A ≠ 0) (hB : B ≠ 0) (ha : IsLocGen p ca A) (hb : IsLocGen p cd B) :
    IsLocGen p (ca ^ 8 / cd ^ 4) (A ^ 8 * (B ^ 4)⁻¹) := by
  have hsa : FractionalIdeal.spanSingleton (𝓞 K)⁰ ca ≠ 0 :=
    FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr ha.1
  have hsb : FractionalIdeal.spanSingleton (𝓞 K)⁰ cd ≠ 0 :=
    FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hb.1
  refine ⟨div_ne_zero (pow_ne_zero _ ha.1) (pow_ne_zero _ hb.1), ?_⟩
  rw [spanSingleton_pow8_div_pow4, count_pow8_inv_pow4 p hsa hsb, count_pow8_inv_pow4 p hA hB, ha.2, hb.2]
end Formalism.L2.LamCM
