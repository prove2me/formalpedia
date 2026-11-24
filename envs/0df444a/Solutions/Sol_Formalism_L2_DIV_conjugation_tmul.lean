-- Prove2me | solution 1 for Formalism.L2.DIV.conjugation_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:25:23.470784+00:00
-- url     : https://prove2.me/submissions/9c21854d-8777-4dd9-a332-0c1493ec659c

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
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
namespace Formalism.L2.DIV
theorem _root_.solution (σ : E →ₐ[F] E) (e : E) (a : 𝔸) : sigR σ 𝔸 (e ⊗ₜ[F] a) = σ e ⊗ₜ[F] a := rfl
end Formalism.L2.DIV
