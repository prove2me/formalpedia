-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.aeval_coe_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:46:53.218399+00:00
-- url     : https://prove2.me/submissions/57752090-e4f1-4918-889a-e55149b2ecb7

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
theorem _root_.solution {σ τ : Type} (A : σ → MvPolynomial τ R) (P : MvPolynomial σ R) :
    MvPolynomial.aeval (fun i => (A i : MvPowerSeries τ R)) P =
      ((MvPolynomial.aeval A P : MvPolynomial τ R) : MvPowerSeries τ R) := by
  induction P using MvPolynomial.induction_on
  next c =>
    first
    | simp [MvPowerSeries.algebraMap_apply, MvPolynomial.algebraMap_eq]
    | simp [MvPolynomial.algebraMap_eq]
    | (rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
        MvPolynomial.coe_C]; rfl)
    | (ext n; simp [MvPowerSeries.coeff_C, MvPolynomial.coeff_C, MvPolynomial.algebraMap_eq])
  next p q hp hq => simp only [map_add, MvPolynomial.coe_add, hp, hq]
  next p i hp => simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.coe_mul, hp]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
