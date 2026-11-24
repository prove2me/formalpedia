-- Prove2me | solution 1 for Formalism.MainNotions.J.mass_ortho_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:37:51.061481+00:00
-- url     : https://prove2.me/submissions/668c8289-beb2-4bd5-bba5-05d6ddcaaacc

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLa
import Theorems.Thm_Formalism_MainNotions_J_mass_tr
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.MainNotions.J
theorem _root_.solution {n : ℕ} {L : Submodule (𝓞 K) V} {L' : Submodule (𝓞 K) V'}
    (hL : IsOrthoLattice h L n) (hL' : IsOrthoLattice h' L' n) : mass h L = mass h' L' := by
  obtain ⟨e, he1, he2, rfl, he⟩ := hL
  obtain ⟨e', he1', he2', rfl, he'⟩ := hL'
  let b : Module.Basis (Fin n) K V := Module.Basis.mk he1 he2.ge
  let b' : Module.Basis (Fin n) K V' := Module.Basis.mk he1' he2'.ge
  let φ : V ≃ₗ[K] V' := b.equiv b' (Equiv.refl _)
  have hφe : ∀ i, φ (e i) = e' i := fun i => by
    have := b.equiv_apply i b' (Equiv.refl _)
    simpa [b, b', φ] using this
  have hφ : ∀ x y, h' (φ x) (φ y) = h x y := by
    intro x y
    have hx := b.sum_repr x
    have hy := b.sum_repr y
    rw [← hx, ← hy]
    simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, b,
      Module.Basis.mk_apply, hφe, he, he']
  rw [← mass_tr hφ]
  congr 1
  unfold latMap
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext i
  exact hφe i
end Formalism.MainNotions.J
