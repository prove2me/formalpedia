-- Prove2me | solution 1 for Formalism.L2.DIV.b_exists_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:25:17.497334+00:00
-- url     : https://prove2.me/submissions/529cb4fb-bf02-4a94-87f5-eebbbe2489f0

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (b : 𝓞 E)
    (hb : ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.under (𝓞 F) = v.asIdeal → b ∉ P.asIdeal) :
    ∃ (c : 𝓞 E) (r : 𝓞 F), r ∉ v.asIdeal ∧ b * c = algebraMap (𝓞 F) (𝓞 E) r := by
  by_contra hcon
  push Not at hcon
  have hle : Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) (Ideal.span {b}) ≤ v.asIdeal := by
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hr
    obtain ⟨c, hc⟩ := hr
    by_contra hrv
    exact hcon c r hrv hc.symm
  have := v.isPrime
  obtain ⟨Q, hQ, hQp, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (Ideal.span {b}) hle
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  exact hb ⟨Q, hQp, hQ0⟩ hQv (hQ (Ideal.mem_span_singleton_self b))
end Formalism.L2.DIV
