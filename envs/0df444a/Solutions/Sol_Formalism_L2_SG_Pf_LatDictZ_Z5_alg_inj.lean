-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.alg_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:59:07.90173+00:00
-- url     : https://prove2.me/submissions/6592b262-b52a-48b9-90ff-6b88769e7843

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_coeOF

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
theorem _root_.solution : Function.Injective (algebraMap (𝓞 I.F) (𝓞 I.E)) := by
  intro a b hab
  have h := congrArg (algebraMap (𝓞 I.E) I.E) hab
  rw [coeOF, coeOF] at h
  exact RingOfIntegers.coe_injective ((algebraMap I.F I.E).injective h)
end Formalism.L2.SG.Pf.LatDictZ.Z5
