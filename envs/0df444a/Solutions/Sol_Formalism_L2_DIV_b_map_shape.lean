-- Prove2me | solution 1 for Formalism.L2.DIV.b_map_shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:24:51.462794+00:00
-- url     : https://prove2.me/submissions/29ec0d21-9282-4cb7-9f5f-f989e6319205

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_b_approx

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
theorem _root_.solution (I : Ideal (𝓞 E)) (D : 𝓞 F) (hD0 : D ≠ 0)
    (s : RInt F E) (hs : s ∈ I.map (toRInt F E)) :
    ∃ c ∈ I, ∃ t : RInt F E, s = toRInt F E c + toRInt F E (algebraMap (𝓞 F) (𝓞 E) D) * t := by
  unfold Ideal.map at hs
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨c, hc, 0, by rw [mul_zero, add_zero]⟩
  | zero => exact ⟨0, I.zero_mem, 0, by rw [mul_zero, add_zero, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, t, rfl⟩ := hx
    obtain ⟨c', hc', t', rfl⟩ := hy
    exact ⟨c + c', I.add_mem hc hc', t + t', by rw [map_add]; ring⟩
  | smul a x _ hx =>
    obtain ⟨c, hc, t, rfl⟩ := hx
    obtain ⟨b, t', rfl⟩ := b_approx D hD0 a
    refine ⟨b * c, I.mul_mem_left b hc, toRInt F E b * t + t' * toRInt F E c +
      toRInt F E (algebraMap (𝓞 F) (𝓞 E) D) * t' * t, ?_⟩
    rw [smul_eq_mul, map_mul]; ring
end Formalism.L2.DIV
