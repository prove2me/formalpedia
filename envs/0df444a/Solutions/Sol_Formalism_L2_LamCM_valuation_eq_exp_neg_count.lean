-- Prove2me | solution 1 for Formalism.L2.LamCM.valuation_eq_exp_neg_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:13:32.745373+00:00
-- url     : https://prove2.me/submissions/9483f256-9bbc-4a03-8723-65dab34f88c3

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
theorem _root_.solution (p : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    p.valuation K x =
      WithZero.exp (-FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hsa : Ideal.span {a} ≠ 0 := by simpa using ha0
  have hsb : Ideal.span {b} ≠ 0 := by simpa using hb0
  rw [map_div₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_def, IsDedekindDomain.HeightOneSpectrum.intValuation_def,
    if_neg ha0, if_neg hb0, div_eq_mul_inv, div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    ← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.coeIdeal_span_singleton,
    ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_mul K p ?_ ?_, FractionalIdeal.count_inv,
    FractionalIdeal.count_coe K p hsa, FractionalIdeal.count_coe K p hsb, ← WithZero.exp_neg, ← WithZero.exp_add]
  · congr 1
    ring
  · rw [FractionalIdeal.coeIdeal_span_singleton, Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha0
  · rw [FractionalIdeal.coeIdeal_span_singleton, Ne, inv_eq_zero, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hb0
end Formalism.L2.LamCM
