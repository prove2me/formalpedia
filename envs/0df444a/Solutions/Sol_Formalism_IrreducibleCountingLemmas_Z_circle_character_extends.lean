-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.circle_character_extends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:01:32.944893+00:00
-- url     : https://prove2.me/submissions/41687d5f-dcbb-40e0-b25b-903c233be16f

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_circle_pow_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : CircleCharExtends := by
  intro A _ H χ
  have : DivisibleBy (Additive Circle) ℤ :=
    divisibleByOfSMulRightSurj (Additive Circle) ℤ fun {n} hn a => by
      obtain ⟨b, hb⟩ := circle_pow_surjective hn a.toMul
      exact ⟨Additive.ofMul b, congrArg Additive.ofMul hb⟩
  obtain ⟨ψ, hψ⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive H.subtype) (fun a b hab => by
      have : (a.toMul : A) = (b.toMul : A) := congrArg Additive.toMul hab
      exact congrArg Additive.ofMul (Subtype.ext this))
    (MonoidHom.toAdditive χ)
  refine ⟨MonoidHom.toAdditive.symm ψ, fun h => ?_⟩
  have := DFunLike.congr_fun hψ (Additive.ofMul h)
  exact congrArg Additive.toMul this
end Formalism.IrreducibleCountingLemmas.Z
