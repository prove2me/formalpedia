-- Prove2me | solution 1 for Formalism.L2.LamCM.eq_of_count_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:29.594401+00:00
-- url     : https://prove2.me/submissions/98a4434b-8867-4186-9436-8d520bc6608e

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
theorem _root_.solution {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ p : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K p I = FractionalIdeal.count K p J) : I = J := by
  calc I = ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v I :=
        (FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI).symm
    _ = ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v J := by
        simp_rw [h]
    _ = J := FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ
end Formalism.L2.LamCM
