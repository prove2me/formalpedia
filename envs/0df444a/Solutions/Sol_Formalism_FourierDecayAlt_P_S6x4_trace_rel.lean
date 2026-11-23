-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x4.trace_rel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:38.341321+00:00
-- url     : https://prove2.me/submissions/22f52231-30ba-4b51-8f38-7e80138df9a3

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitPrimeToDifferent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x4
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.S6x4
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E) :
    algebraMap (maximalRealSubfield E) E (Algebra.trace (maximalRealSubfield E) E x)
      = x + complexConj E x := by
  classical
  rw [trace_eq_sum_automorphisms]
  have hu : (Finset.univ : Finset (E ≃ₐ[maximalRealSubfield E] E)) = {1, complexConj E} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      Algebra.IsQuadraticExtension.finrank_eq_two,
      Finset.card_pair (complexConj_ne_one E).symm]
  rw [hu, Finset.sum_pair (complexConj_ne_one E).symm]
  rfl
end Formalism.FourierDecayAlt.P.S6x4
