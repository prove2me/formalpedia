-- Prove2me | solution 1 for Formalism.MainNotions.J.cj_cj_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:42:50.237709+00:00
-- url     : https://prove2.me/submissions/546e5e48-dc15-43bd-ab4e-ec9f51db01c2

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLa
import Theorems.Thm_Formalism_MainNotions_J_cj_apply
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
namespace Formalism.MainNotions.J
theorem _root_.solution (φ : V ≃ₗ[K] V') (g : V' ≃ₗ[K] V') : cj φ (cj φ.symm g) = g := by
  ext x; simp [cj_apply]
end Formalism.MainNotions.J
