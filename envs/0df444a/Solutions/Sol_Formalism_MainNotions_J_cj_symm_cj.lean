-- Prove2me | solution 1 for Formalism.MainNotions.J.cj_symm_cj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:40:07.024908+00:00
-- url     : https://prove2.me/submissions/c41b259e-d139-4a52-a9b3-402e1687054a

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
theorem _root_.solution (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) : cj φ.symm (cj φ g) = g := by
  ext x; simp [cj_apply]
end Formalism.MainNotions.J
