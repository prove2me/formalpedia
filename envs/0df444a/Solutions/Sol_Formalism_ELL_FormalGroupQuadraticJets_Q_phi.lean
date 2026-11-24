-- Prove2me | solution 1 for Formalism.ELL.FormalGroupQuadraticJets.Q_phi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:24.05307+00:00
-- url     : https://prove2.me/submissions/93cac2a0-9ab2-446e-992c-f1bb279ee6f4

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_cc_psubst
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
theorem _root_.solution (φ : PowerSeries K) {S : MvPowerSeries (Fin 2) K}
    (hS : MvPowerSeries.constantCoeff S = 0) :
    Q (φ.subst S) =
      PowerSeries.constantCoeff (PowerSeries.derivative K (PowerSeries.derivative K φ)) *
          ccd 1 S * ccd 0 S +
        PowerSeries.constantCoeff (PowerSeries.derivative K φ) * Q S := by
  unfold Q ccd
  rw [pderiv_psubst hS, Derivation.leibniz, pderiv_psubst hS]
  simp only [smul_eq_mul, map_add, map_mul, cc_psubst hS]
  ring
end Formalism.ELL.FormalGroupQuadraticJets
