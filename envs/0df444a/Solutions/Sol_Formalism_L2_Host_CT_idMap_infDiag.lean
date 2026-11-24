-- Prove2me | solution 1 for Formalism.L2.Host.CT.idMap_infDiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:17:17.696343+00:00
-- url     : https://prove2.me/submissions/488b0406-bc2c-4917-86ae-468382f361ef

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharTransport
import Theorems.Thm_Formalism_L2_Host_CT_infDiag_coe

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
theorem _root_.solution (j : E ≃+* L) (k : Eˣ) : idMap j (infDiag k) = infDiag (Units.map j.toMonoidHom k) := by
  apply Units.ext
  show adMap j ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = _
  rw [infDiag_coe, infDiag_coe]
  refine Prod.ext ?_ ?_
  · funext u
    exact infEquiv_algebraMap j u (k : E)
  · exact map_one (finMap j)
end Formalism.L2.Host.CT
