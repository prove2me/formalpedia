-- Prove2me | solution 1 for Formalism.MainNotions.J.genus_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:29:51.504005+00:00
-- url     : https://prove2.me/submissions/4509cc49-1d06-4b06-bc08-cafd4ee9505c

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLa
import Theorems.Thm_Formalism_MainNotions_J_gmap_cj
import Theorems.Thm_Formalism_MainNotions_J_loc_tr
import Theorems.Thm_Formalism_MainNotions_J_cj_mem_isom
import Theorems.Thm_Formalism_MainNotions_J_isLattice_tr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.MainNotions.J
theorem _root_.solution {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {L M : Submodule (𝓞 K) V}
    (hM : M ∈ genus h L) : latMap φ M ∈ genus h' (latMap φ L) := by
  refine ⟨isLattice_tr φ hM.1, fun p hp => ?_⟩
  obtain ⟨g, hg, e⟩ := hM.2 p hp
  exact ⟨cj φ g, cj_mem_isom hφ hg, by rw [loc_tr, gmap_cj, e, loc_tr]⟩
end Formalism.MainNotions.J
