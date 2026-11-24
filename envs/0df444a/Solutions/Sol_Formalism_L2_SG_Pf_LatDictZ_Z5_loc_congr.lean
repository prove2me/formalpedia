-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.loc_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:43:46.274863+00:00
-- url     : https://prove2.me/submissions/90c839bc-3ba6-42bc-bda0-ac9a48bccfd2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_loc_iff

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
theorem _root_.solution {p p' : Ideal (𝓞 I.E)} (hp : p.IsMaximal) (hp' : p'.IsMaximal)
    (h : p.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = p'.comap (algebraMap (𝓞 I.F) (𝓞 I.E)))
    (N : Submodule (𝓞 I.E) (Fin I.n → I.E)) : locE I p N = locE I p' N := by
  ext v
  rw [loc_iff I p hp, loc_iff I p' hp', h]
end Formalism.L2.SG.Pf.LatDictZ.Z5
