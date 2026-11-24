-- Prove2me | solution 1 for Formalism.ELL.FormalGroupQuadraticJets.linearCoeff_one_subst_X1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:25.424055+00:00
-- url     : https://prove2.me/submissions/a9d41965-3817-4f0e-87b5-ef09e4b460fe

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_cc_psubst
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_cc_derivative
import Theorems.Thm_Formalism_G_LogCR_pderiv_psubst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupQuadraticJets
open Formalism.G.LogCR
variable {K : Type*} [CommRing K]
namespace Formalism.ELL.FormalGroupQuadraticJets
theorem _root_.solution (g : PowerSeries K) :
    ccd 1 (g.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K)) =
      PowerSeries.coeff 1 g := by
  unfold ccd
  rw [pderiv_psubst (MvPowerSeries.constantCoeff_X _)]
  simp [MvPowerSeries.pderiv_X, cc_psubst (MvPowerSeries.constantCoeff_X _), cc_derivative]
end Formalism.ELL.FormalGroupQuadraticJets
