-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z5.eT_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:43:58.119359+00:00
-- url     : https://prove2.me/submissions/4a5e0da8-a9d0-4478-ae9e-2e95e46aa82e

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
namespace Formalism.L2.SG.Pf.LatDictZ.Z5
theorem _root_.solution {Q : Set (HeightOneSpectrum (𝓞 F))} (hQ : Q.Finite) :
    eT Qᶜ + ∑ i ∈ hQ.toFinset, eT {i} = 1 := by
  apply RestrictedProduct.ext
  intro v
  have hs : (∑ i ∈ hQ.toFinset, eT {i}) v = ∑ i ∈ hQ.toFinset, eT {i} v := map_sum (ev v) _ _
  show eT Qᶜ v + (∑ i ∈ hQ.toFinset, eT {i}) v = 1
  rw [hs]
  by_cases hv : v ∈ Q
  · rw [eT_of_not (T := Qᶜ) (fun h => h hv), zero_add, Finset.sum_eq_single v]
    · exact eT_of_mem (Set.mem_singleton v)
    · intro b _ hb
      exact eT_of_not (fun h => hb (Set.mem_singleton_iff.mp h).symm)
    · intro h
      exact absurd (hQ.mem_toFinset.mpr hv) h
  · rw [eT_of_mem hv, Finset.sum_eq_zero, add_zero]
    intro b hb
    apply eT_of_not
    rw [Set.mem_singleton_iff]
    rintro rfl
    exact hv (hQ.mem_toFinset.mp hb)
end Formalism.L2.SG.Pf.LatDictZ.Z5
