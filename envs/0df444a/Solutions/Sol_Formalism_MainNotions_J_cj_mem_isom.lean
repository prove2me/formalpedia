-- Prove2me | solution 1 for Formalism.MainNotions.J.cj_mem_isom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:22.276113+00:00
-- url     : https://prove2.me/submissions/c1a06d04-02b2-457f-af2f-b964fb05dbdb

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLa
import Theorems.Thm_Formalism_MainNotions_J_cj_apply
import Theorems.Thm_Formalism_MainNotions_J_isom_symm

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
theorem _root_.solution {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {g : V ≃ₗ[K] V}
    (hg : g ∈ isom h) : cj φ g ∈ isom h' := by
  intro x y
  rw [cj_apply, cj_apply, hφ, hg, isom_symm hφ]
end Formalism.MainNotions.J
