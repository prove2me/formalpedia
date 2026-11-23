-- Prove2me | solution 1 for Formalism.ELL.FormalGroupQuadraticJets.cc_psubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:39.148787+00:00
-- url     : https://prove2.me/submissions/705bc096-ebf3-4fd1-9f96-a692396a7a42

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero


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
theorem _root_.solution {τ : Type*} [Finite τ] {a : MvPowerSeries τ K}
    (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (f.subst a) = PowerSeries.constantCoeff f := by
  exact Formalism.G.LogP.constantCoeff_subst_of_zero (f : MvPowerSeries Unit K) (b := fun _ => a) (fun _ => ha)
end Formalism.ELL.FormalGroupQuadraticJets
