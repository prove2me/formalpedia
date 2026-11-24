-- Prove2me | solution 1 for Formalism.MainNotions.J.card_autL_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:29:46.596603+00:00
-- url     : https://prove2.me/submissions/e69fa934-ca6b-4fe8-a03f-b5de57dfe08c

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLa
import Theorems.Thm_Formalism_MainNotions_J_cj_symm_cj
import Theorems.Thm_Formalism_MainNotions_J_cj_cj_symm
import Theorems.Thm_Formalism_MainNotions_J_gmap_cj
import Theorems.Thm_Formalism_MainNotions_J_isom_symm
import Theorems.Thm_Formalism_MainNotions_J_cj_mem_isom

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
theorem _root_.solution {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) (M : Submodule (𝓞 K) V) :
    Nat.card (autL h' (latMap φ M)) = Nat.card (autL h M) := by
  have a1 : ∀ g : autL h M, gmap (cj φ g.1) (latMap φ M) = latMap φ M := fun g => by
    rw [gmap_cj, g.2.2]
  have a2 : ∀ g : autL h' (latMap φ M), gmap (cj φ.symm g.1) M = M := fun g => by
    have h2 := gmap_cj φ.symm g.1 (latMap φ M)
    rw [tr_symm_tr] at h2
    rw [h2, g.2.2, tr_symm_tr]
  exact (Nat.card_congr ⟨fun g => ⟨cj φ g.1, cj_mem_isom hφ g.2.1, a1 g⟩,
    fun g => ⟨cj φ.symm g.1, cj_mem_isom (isom_symm hφ) g.2.1, a2 g⟩,
    fun g => Subtype.ext (cj_symm_cj φ g.1), fun g => Subtype.ext (cj_cj_symm φ g.1)⟩).symm
end Formalism.MainNotions.J
