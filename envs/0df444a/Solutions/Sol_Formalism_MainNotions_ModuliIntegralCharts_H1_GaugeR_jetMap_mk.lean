-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.jetMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:13.787107+00:00
-- url     : https://prove2.me/submissions/3c0587f4-9ac7-43b7-8693-4748d28b180f

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GaugeUniqB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open MvPolynomial Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
variable {R ι : Type} [CommRing R]
variable [Fintype ι] [DecidableEq ι]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
theorem _root_.solution {ι' : Type} (m : ℕ) (φ : ι → MvPolynomial ι' R) (hφ : ∀ i, φ i ∈ orig R ι')
    (p : MvPolynomial ι R) :
    jetMap φ hφ (Ideal.Quotient.mk (orig R ι ^ (m + 1)) p) = Ideal.Quotient.mk _ (aeval φ p) := rfl
end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
