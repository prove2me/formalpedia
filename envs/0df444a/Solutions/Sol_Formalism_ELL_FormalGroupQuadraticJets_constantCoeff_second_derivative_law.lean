-- Prove2me | solution 1 for Formalism.ELL.FormalGroupQuadraticJets.constantCoeff_second_derivative_law
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:25.199234+00:00
-- url     : https://prove2.me/submissions/afc8a15e-125d-4cf0-9460-3f3f2465aecb

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_cc_omega
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_cc_domega

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.ELL.FormalGroupQuadraticJets
theorem _root_.solution (F : FormalGroup (Formalism.G.unitBall K)) (φ : PowerSeries K) :
    PowerSeries.constantCoeff ((invD F)^[2] φ) =
      ccd 1 (FK F).toPowerSeries *
        (ccd 0 (MvPowerSeries.pderiv K 1 (FK F).toPowerSeries) *
            PowerSeries.constantCoeff (PowerSeries.derivative K φ) +
          ccd 1 (FK F).toPowerSeries *
            PowerSeries.constantCoeff (PowerSeries.derivative K (PowerSeries.derivative K φ))) := by
  unfold Formalism.ELL.invD
  show PowerSeries.constantCoeff (Formalism.ELL.omegaF F * PowerSeries.derivative K
      (Formalism.ELL.omegaF F * PowerSeries.derivative K φ)) = _
  rw [map_mul, Derivation.leibniz]
  simp only [map_add, map_mul, smul_eq_mul, cc_omega, cc_domega]
  ring
end Formalism.ELL.FormalGroupQuadraticJets
