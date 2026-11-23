-- Prove2me | solution 1 for Formalism.L2.Th1.A.Univ.mv_map_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:27.244371+00:00
-- url     : https://prove2.me/submissions/6811702f-33d1-4b2c-b619-b84637320eba

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Univ
namespace Formalism.L2.Th1.A.Univ
theorem _root_.solution {σ : Type*} {A : Type*} {B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) :
    Function.Injective (MvPowerSeries.map f : MvPowerSeries σ A →+* MvPowerSeries σ B) := by
  intro a b h
  ext e
  apply hf
  have h1 := congrArg (MvPowerSeries.coeff e) h
  simpa using h1
end Formalism.L2.Th1.A.Univ
