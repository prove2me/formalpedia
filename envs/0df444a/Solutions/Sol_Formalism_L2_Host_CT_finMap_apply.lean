-- Prove2me | solution 1 for Formalism.L2.Host.CT.finMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:12:32.527414+00:00
-- url     : https://prove2.me/submissions/185ba04f-04f4-452e-93f9-bc0de003a5bb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open Formalism Formalism.L2 Formalism.L2.Host Formalism.L2.Host.CT
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀
variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]
namespace Formalism.L2.Host.CT
theorem _root_.solution (j : E ≃+* L) (a : FiniteAdeleRing (𝓞 E) E) (v : HeightOneSpectrum (𝓞 L)) :
    finMap j a v = (compEquiv j.symm v).symm (a (plMap j.symm v)) := rfl
end Formalism.L2.Host.CT
