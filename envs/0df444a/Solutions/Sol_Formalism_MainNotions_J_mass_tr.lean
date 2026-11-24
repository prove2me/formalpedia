-- Prove2me | solution 1 for Formalism.MainNotions.J.mass_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:20:28.786209+00:00
-- url     : https://prove2.me/submissions/f90572a5-13c1-4192-afef-7689b536de18

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLa
import Theorems.Thm_Formalism_MainNotions_J_isom_symm
import Theorems.Thm_Formalism_MainNotions_J_classReps_tr
import Theorems.Thm_Formalism_MainNotions_J_card_autL_tr
import Theorems.Thm_Formalism_MainNotions_J_mass_eq_sum

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
theorem _root_.solution {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) (L : Submodule (𝓞 K) V) :
    mass h' (latMap φ L) = mass h L := by
  by_cases hs : ∃ s, IsClassReps h L s
  · obtain ⟨s, hs⟩ := hs
    rw [mass_eq_sum h L s hs, mass_eq_sum h' _ _ (classReps_tr hφ hs), Finset.sum_map]
    exact Finset.sum_congr rfl fun M _ => by
      rw [Function.Embedding.coeFn_mk, card_autL_tr hφ]
  · have hs' : ¬ ∃ s, IsClassReps h' (latMap φ L) s := by
      rintro ⟨s, hs'⟩
      apply hs
      have := classReps_tr (isom_symm hφ) hs'
      rw [tr_symm_tr] at this
      exact ⟨_, this⟩
    unfold mass
    rw [dif_neg hs, dif_neg hs']
end Formalism.MainNotions.J
