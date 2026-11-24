-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.iv_OF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:19:18.438853+00:00
-- url     : https://prove2.me/submissions/6a25eccb-958e-425d-ac0d-0d9435bdf2a6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_incl_OF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z5
open Formalism.MainNotions.S PIW.AdelClassFin Formalism.L2.SG.Pf.LatDictZ
variable (I : AutInst)
namespace Formalism.L2.SG.Pf.LatDictZ.Z5
theorem _root_.solution (a : 𝓞 I.F) (w : Fin I.n → I.E) :
    iv I (algebraMap (𝓞 I.F) (𝓞 I.E) a • w) = iA I (algebraMap (𝓞 I.F) (Af I.F) a) • iv I w := by
  funext i
  show Formalism.UG.inclE (F := I.F) (Af I.F) ((algebraMap (𝓞 I.F) (𝓞 I.E) a • w) i) =
    iA I (algebraMap (𝓞 I.F) (Af I.F) a) • Formalism.UG.inclE (F := I.F) (Af I.F) (w i)
  rw [Pi.smul_apply, Algebra.smul_def, map_mul, incl_OF, smul_eq_mul]
end Formalism.L2.SG.Pf.LatDictZ.Z5
