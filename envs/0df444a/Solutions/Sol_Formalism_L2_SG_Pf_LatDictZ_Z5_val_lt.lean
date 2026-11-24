-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.val_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:38:39.67733+00:00
-- url     : https://prove2.me/submissions/019f0e65-296a-4e96-9d3b-1eaf617c9d24

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
theorem _root_.solution {v : HeightOneSpectrum (𝓞 F)} {r : 𝓞 F} (h : r ∈ v.asIdeal) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 := by
  erw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
  rw [
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
  exact h
end Formalism.L2.SG.Pf.LatDictZ.Z5
