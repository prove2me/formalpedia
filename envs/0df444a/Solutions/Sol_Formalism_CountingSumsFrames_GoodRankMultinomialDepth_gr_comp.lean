-- Prove2me | solution 1 for Formalism.CountingSumsFrames.GoodRankMultinomialDepth.gr_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:13.740026+00:00
-- url     : https://prove2.me/submissions/702b4f85-51d2-48c7-be89-c0eddb55361b

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_LemmaS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.GoodRankMultinomialDepth
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.CountingSumsFrames.GoodRankMultinomialDepth
theorem _root_.solution {A A' B ι : Type} [AddCommGroup A] [Module O A] [AddCommGroup A'] [Module O A']
    [AddCommGroup B] [Module O B] {π : O} {f : A →ₗ[O] B} {D : ℕ} (w : A' →ₗ[O] A)
    (h : GR ι π (f ∘ₗ w) D) : GR ι π f D := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨w ∘ₗ u, v, by rw [← huv]; rfl⟩
end Formalism.CountingSumsFrames.GoodRankMultinomialDepth
