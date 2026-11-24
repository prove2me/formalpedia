-- Prove2me | solution 1 for Formalism.MainNotions.J.isLattice_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:42:51.088872+00:00
-- url     : https://prove2.me/submissions/fdccc787-096f-4971-97fa-4f0c497b152e

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLa

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
theorem _root_.solution (φ : V ≃ₗ[K] V') {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (latMap φ M) where
  fg := hM.fg.map _
  span_eq_top := by
    have h1 : ((latMap φ M : Submodule (𝓞 K) V') : Set V') = (φ : V →ₗ[K] V') '' (M : Set V) := rfl
    rw [h1, Submodule.span_image, hM.span_eq_top, Submodule.map_top, LinearEquiv.range]
end Formalism.MainNotions.J
