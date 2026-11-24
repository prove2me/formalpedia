-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.eT_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:43:57.001015+00:00
-- url     : https://prove2.me/submissions/46f71c17-9769-4ddc-a529-6b17aca87d68

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZGlueA
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z5_eT_of_mem
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
open Classical
namespace Formalism.L2.SG.Pf.LatDictZ.Z5
theorem _root_.solution (i j : HeightOneSpectrum (𝓞 F)) :
    eT {i} * eT {j} = if i = j then eT {i} else 0 := by
  apply RestrictedProduct.ext
  intro v
  show eT {i} v * eT {j} v = (if i = j then eT {i} else 0) v
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hv : v ∈ ({i} : Set (HeightOneSpectrum (𝓞 F)))
    · rw [eT_of_mem hv, mul_one]
    · rw [eT_of_not hv, mul_zero]
  · rw [if_neg hij]
    show eT {i} v * eT {j} v = 0
    by_cases hv : v ∈ ({i} : Set (HeightOneSpectrum (𝓞 F)))
    · have hv' : v ∉ ({j} : Set (HeightOneSpectrum (𝓞 F))) := by
        rw [Set.mem_singleton_iff] at hv ⊢
        rw [hv]
        exact hij
      rw [eT_of_not hv', mul_zero]
    · rw [eT_of_not hv, zero_mul]
end Formalism.L2.SG.Pf.LatDictZ.Z5
