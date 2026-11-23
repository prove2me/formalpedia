-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.weq_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:22.32829+00:00
-- url     : https://prove2.me/submissions/e1c8f37e-ec03-4b75-8d86-7a974593980d

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G
variable {K : Type u} [Field K]
namespace Formalism.ELL.FormalGroupPointsHom
theorem _root_.solution {W : WeierstrassCurve K} {σ : Type} {s v : MvPowerSeries σ K} (h : WEqAt W s v) :
    v = s ^ 3 + MvPowerSeries.C W.a₁ * (s * v) + MvPowerSeries.C W.a₂ * (s ^ 2 * v)
      + MvPowerSeries.C W.a₃ * v ^ 2 + MvPowerSeries.C W.a₄ * (s * v ^ 2)
      + MvPowerSeries.C W.a₆ * v ^ 3 := by
  unfold WEqAt at h
  simpa only [MvPowerSeries.smul_eq_C_mul] using h
end Formalism.ELL.FormalGroupPointsHom
