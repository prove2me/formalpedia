-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.mkI_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:57:32.859802+00:00
-- url     : https://prove2.me/submissions/cf73388c-f7cf-40ab-96c7-e1232e3a0140

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
theorem _root_.solution (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) : mkI c hc v = c v := rfl
end Formalism.L2.SG.Pf.LatDictZ.Z5
