-- Prove2me | solution 1 for Formalism.L2.DIV.c_T_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:25:22.105211+00:00
-- url     : https://prove2.me/submissions/bac883dc-e8ea-4026-96ab-fded251b416d

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
local notation "ιE" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.DIV
theorem _root_.solution (N N' : Submodule (𝓞 E) E) {z z' : AfE F E} (hz : z ∈ integralAdeleSpan (F := F) N)
    (hz' : z' ∈ integralAdeleSpan (F := F) N') : z * z' ∈ integralAdeleSpan (F := F) (N * N') := by
  have h := Submodule.mul_mem_mul hz hz'
  rw [integralAdeleSpan, integralAdeleSpan, Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨n, hn, rfl⟩, _, ⟨n', hn', rfl⟩, rfl⟩
  exact ⟨n * n', Submodule.mul_mem_mul hn hn', map_mul _ _ _⟩
end Formalism.L2.DIV
