-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.eT_compl_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:43:55.749504+00:00
-- url     : https://prove2.me/submissions/8cce9604-8664-4577-8876-7c154a7a4889

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_eT_of_not

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
theorem _root_.solution {Q : Set (HeightOneSpectrum (𝓞 F))} {i : HeightOneSpectrum (𝓞 F)} (hi : i ∈ Q) :
    eT Qᶜ * eT {i} = 0 := by
  apply RestrictedProduct.ext
  intro v
  show eT Qᶜ v * eT {i} v = 0
  by_cases hv : v ∈ ({i} : Set (HeightOneSpectrum (𝓞 F)))
  · have h2 : v ∉ Qᶜ := by
      rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact fun h => h hi
    rw [eT_of_not h2, zero_mul]
  · rw [eT_of_not hv, mul_zero]
end Formalism.L2.SG.Pf.LatDictZ.Z5
