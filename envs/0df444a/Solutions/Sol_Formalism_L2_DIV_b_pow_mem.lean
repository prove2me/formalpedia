-- Prove2me | solution 1 for Formalism.L2.DIV.b_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:25:20.904104+00:00
-- url     : https://prove2.me/submissions/f1f74c1e-9759-43a7-bc78-cfb0c4e8f623

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
theorem _root_.solution (z : RInt F E) (hz : ∀ P : HeightOneSpectrum (𝓞 E), z ∈ P.asIdeal.map (toRInt F E))
    (I : Ideal (𝓞 E)) : I ≠ 0 → ∃ k : ℕ, z ^ k ∈ I.map (toRInt F E) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ x hx =>
    intro _
    rw [Ideal.isUnit_iff] at hx
    exact ⟨0, by rw [hx, Ideal.map_top]; trivial⟩
  | h₃ a p ha hp ih =>
    intro _
    obtain ⟨k, hk⟩ := ih ha
    refine ⟨k + 1, ?_⟩
    rw [Ideal.map_mul, pow_succ']
    exact Ideal.mul_mem_mul (hz ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩) hk
end Formalism.L2.DIV
