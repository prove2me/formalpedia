-- Prove2me | solution 1 for Formalism.L2.DIV.finite_adele_is_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:26:23.270363+00:00
-- url     : https://prove2.me/submissions/d4de903a-4aa7-41cf-a20a-234ad14ce8c4

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
theorem _root_.solution (a : 𝔸) (h0 : ∀ v, a v ≠ 0)
    (h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (a v) = 1) : IsUnit a := by
  let b : 𝔸 := ⟨fun v => (a v)⁻¹, by
    filter_upwards [h1] with v hv
    show (a v)⁻¹ ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]⟩
  refine IsUnit.of_mul_eq_one b ?_
  refine FiniteAdeleRing.ext _ fun v => ?_
  show a v * (a v)⁻¹ = 1
  exact mul_inv_cancel₀ (h0 v)
end Formalism.L2.DIV
