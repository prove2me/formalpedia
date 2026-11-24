-- Prove2me | solution 1 for Formalism.L2.DIV.b_intU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:25:26.655051+00:00
-- url     : https://prove2.me/submissions/6acb2bae-6f50-4f1d-b297-06c650d06cdf

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.L2.DIV
theorem _root_.solution (x : (AfE F E)ˣ) (hx : x ∈ intU F E) :
    ∃ u : (RInt F E)ˣ, Units.map (RInt F E).subtype.toMonoidHom u = x := by
  rw [intU, Submonoid.mem_units_iff] at hx
  refine ⟨⟨⟨x, hx.1⟩, ⟨(x⁻¹ : (AfE F E)ˣ), hx.2⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩, Units.ext rfl⟩
end Formalism.L2.DIV
