-- Prove2me | solution 1 for Formalism.CohomologicalDescent.map_cast_le_of_map_neg_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:46:20.7176+00:00
-- url     : https://prove2.me/submissions/ce40309f-f32e-4111-b937-391ae2ee042b

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWAssembled
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MinorValuationBoundHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeChainHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent
theorem _root_.solution (l : ℕ) (hl : l.Prime) (F : Type) [Field F] [CharP F l] (a : F) (ha : a ≠ 0)
    {α β : Type} (A : Multiset α) (B : Multiset β) (f : α → ℤ) (g : β → ℤ)
    (h : Multiset.map (fun x => -a * ((f x : ℤ) : F)) A ≤
      Multiset.map (fun y => -a * ((g y : ℤ) : F)) B) :
    Multiset.map (fun x => ((f x : ℤ) : ZMod l)) A ≤ Multiset.map (fun y => ((g y : ℤ) : ZMod l)) B := by
  haveI := Fact.mk hl
  let φ : ZMod l →+* F := ZMod.castHom (dvd_refl l) F
  have hφ : Function.Injective φ := φ.injective
  have hψ : Function.Injective (fun z : ZMod l => -a * φ z) := fun z w hzw =>
    hφ (mul_left_cancel₀ (neg_ne_zero.2 ha) hzw)
  rw [← Multiset.map_le_map_iff hψ, Multiset.map_map, Multiset.map_map]
  simpa [Function.comp_def, φ, map_intCast] using h
end Formalism.CohomologicalDescent
