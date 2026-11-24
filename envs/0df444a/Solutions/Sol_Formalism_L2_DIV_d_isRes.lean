-- Prove2me | solution 1 for Formalism.L2.DIV.d_isRes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:25:02.593041+00:00
-- url     : https://prove2.me/submissions/42790234-5769-450d-bbe6-c82830f06405

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
set_option quotPrecheck false in
local notation "uIn" => Units.map (RInt F E).subtype.toMonoidHom
namespace Formalism.L2.DIV
theorem _root_.solution (hEx : ResCharEx) (ξ : Chr F E L) (ht : ∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker)
    (P : HeightOneSpectrum (𝓞 E)) : IsResChar ξ P (resChar ξ P) := by
  have h : ∃ χ, IsResChar ξ P χ := (hEx F E L ξ ht P).exists
  rw [resChar, dif_pos h]
  exact h.choose_spec
end Formalism.L2.DIV
