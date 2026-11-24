-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.ne0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:15:42.595388+00:00
-- url     : https://prove2.me/submissions/dcc5e5ec-8031-4caf-b120-9bd6904e224c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_val_one

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
theorem _root_.solution {v : HeightOneSpectrum (𝓞 F)} {r : 𝓞 F} (h : r ∉ v.asIdeal) :
    algebraMap (𝓞 F) (v.adicCompletion F) r ≠ 0 := by
  intro h0
  have h1 := val_one h
  rw [h0, map_zero] at h1
  exact zero_ne_one h1
end Formalism.L2.SG.Pf.LatDictZ.Z5
