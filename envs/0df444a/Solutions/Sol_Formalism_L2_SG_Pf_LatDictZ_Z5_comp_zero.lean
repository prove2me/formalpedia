-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.comp_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:26:47.151256+00:00
-- url     : https://prove2.me/submissions/6c68aa9e-b97a-482b-9736-20939721e19f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA

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
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.L2.SG.Pf.LatDictZ.Z5
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) : (0 : Af F) v = 0 := rfl
end Formalism.L2.SG.Pf.LatDictZ.Z5
