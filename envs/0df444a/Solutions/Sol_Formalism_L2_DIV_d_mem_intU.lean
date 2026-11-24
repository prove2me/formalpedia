-- Prove2me | solution 1 for Formalism.L2.DIV.d_mem_intU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:25:17.502776+00:00
-- url     : https://prove2.me/submissions/e2455388-0a6f-428f-a606-9764d959f424

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
theorem _root_.solution (u : (RInt F E)ˣ) : uIn u ∈ intU F E := by
  rw [intU, Submonoid.mem_units_iff]
  exact ⟨u.1.2, (u⁻¹).1.2⟩
end Formalism.L2.DIV
