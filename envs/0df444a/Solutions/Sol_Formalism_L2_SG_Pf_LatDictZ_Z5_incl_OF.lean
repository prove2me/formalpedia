-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.incl_OF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:51:02.303288+00:00
-- url     : https://prove2.me/submissions/2f18f583-b2d5-4d1c-8e5c-d37901114d12

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
theorem _root_.solution (a : 𝓞 I.F) :
    Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E (algebraMap (𝓞 I.F) (𝓞 I.E) a)) =
      iA I (algebraMap (𝓞 I.F) (Af I.F) a) := by
  rw [coeOF]
  show (algebraMap I.F I.E (algebraMap (𝓞 I.F) I.F a)) ⊗ₜ[I.F] (1 : Af I.F) =
    (1 : I.E) ⊗ₜ[I.F] (algebraMap (𝓞 I.F) (Af I.F) a)
  rw [Algebra.algebraMap_eq_smul_one (algebraMap (𝓞 I.F) I.F a), TensorProduct.smul_tmul,
    ← Algebra.algebraMap_eq_smul_one]
  congr 1
end Formalism.L2.SG.Pf.LatDictZ.Z5
