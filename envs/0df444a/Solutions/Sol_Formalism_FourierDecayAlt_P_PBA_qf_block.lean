-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.qf_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:19:05.051805+00:00
-- url     : https://prove2.me/submissions/2ca18ea9-1ba9-44ba-9150-037ba1b0de73

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
variable {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β)
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution (a : α → α → ℂ) (w : α → β → ℂ) (b : β → β → ℂ) (c : α ⊕ β → ℂ) :
    (qf (Y₁.disjSum Y₂) (blockK a w b) c).re =
      (qf Y₁ a (fun p => c (.inl p))).re + (qf Y₂ b (fun q => c (.inr q))).re +
        2 * (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * w p q * c (.inr q)).re := by
  have hconj : (∑ x ∈ Y₂, ∑ y ∈ Y₁, conj (c (.inr x)) * conj (w y x) * c (.inl y)) =
      conj (∑ p ∈ Y₁, ∑ q ∈ Y₂, conj (c (.inl p)) * w p q * c (.inr q)) := by
    rw [Finset.sum_comm]
    simp only [map_sum, map_mul, Complex.conj_conj]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  simp only [qf, Finset.sum_disjSum, blockK, Finset.sum_add_distrib]
  rw [hconj]
  simp only [Complex.add_re, Complex.conj_re]
  ring
end Formalism.FourierDecayAlt.P.PBA
