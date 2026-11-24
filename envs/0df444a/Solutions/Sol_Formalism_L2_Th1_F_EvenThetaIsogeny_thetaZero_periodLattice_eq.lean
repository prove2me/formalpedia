-- Prove2me | solution 1 for Formalism.L2.Th1.F.EvenThetaIsogeny.thetaZero_periodLattice_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:19:14.478856+00:00
-- url     : https://prove2.me/submissions/5986ffad-568f-49df-9491-8b0905c9e5ad

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroTranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EllipticOnePole
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MemOfDenEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EvenThetaIsogeny
open IsogenySigmaQuotient
variable (L : PeriodPair)
variable (α t : ℂ) (T : Finset ℂ)
namespace Formalism.L2.Th1.F.EvenThetaIsogeny
theorem _root_.solution (w : ℂ) : th0 L t w = (opU L t (sgStar L) 0)⁻¹ * (sgStar L (w + t) *
    Complex.exp (-(Real.pi : ℂ) * herm L w t - (Real.pi : ℂ) * herm L t t / 2)) := by
  unfold th0
  rw [div_eq_inv_mul]
  rfl
end Formalism.L2.Th1.F.EvenThetaIsogeny
