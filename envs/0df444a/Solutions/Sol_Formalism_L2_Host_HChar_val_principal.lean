-- Prove2me | solution 1 for Formalism.L2.Host.HChar.val_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:11:04.514453+00:00
-- url     : https://prove2.me/submissions/22975a3f-5a59-4822-9c41-a35c31a113d0

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HeckeProd
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharProd
import Theorems.Thm_Formalism_L2_Host_HChar_productRule
import Theorems.Thm_PI_HeckeProdW_productRule


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.Host Formalism.L2.Host.HChar
variable {L : Type} [Field L] [NumberField L] (χ : HChar L)
namespace Formalism.L2.Host.HChar
theorem _root_.solution (S : Finset (HeightOneSpectrum (𝓞 L))) (hS : ∀ v, v ∉ S → χ.UnrAt v) (k : Lˣ) :
    (∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ S), χ.val v ^ ordF v k) = (χ.inf k * ∏ v ∈ S, χ.locK v k)⁻¹ :=
  eq_inv_of_mul_eq_one_right (χ.productRule S hS k)
end Formalism.L2.Host.HChar
