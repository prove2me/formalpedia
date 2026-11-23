-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.sum_eq_zero_of_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:38.765628+00:00
-- url     : https://prove2.me/submissions/c6dfb196-aba8-4083-9b61-2c3c7062e982

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution {α : Type} (E : Finset α) (Φ : α → ℂ) (S : α → α)
    (hS : Function.Injective S) (hE : ∀ q ∈ E, S q ∈ E) (ζ : ℂ) (hζ : ζ ≠ 1)
    (hΦ : ∀ q ∈ E, Φ (S q) = ζ * Φ q) : ∑ q ∈ E, Φ q = 0 := by
  classical
  have him : E.image S = E := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx
      exact hE q hq
    · rw [Finset.card_image_of_injective _ hS]
  have h1 : ∑ q ∈ E, Φ q = ζ * ∑ q ∈ E, Φ q := by
    conv_lhs => rw [← him]
    rw [Finset.sum_image (fun a _ b _ h => hS h), Finset.mul_sum]
    exact Finset.sum_congr rfl hΦ
  have h2 : (1 - ζ) * ∑ q ∈ E, Φ q = 0 := by
    rw [sub_mul, one_mul, ← h1, sub_self]
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (sub_eq_zero.1 h).symm hζ
  · exact h
end Formalism.FourierDecayAlt.P.A5x9
