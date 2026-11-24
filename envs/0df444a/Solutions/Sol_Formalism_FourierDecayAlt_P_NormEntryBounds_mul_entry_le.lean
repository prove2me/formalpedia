-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NormEntryBounds.mul_entry_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:30.470115+00:00
-- url     : https://prove2.me/submissions/a297a7c4-3cc5-4c1f-b57f-ce2cc3104883

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZhatSectionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormEntryBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2 C2x5 HermitianXiVector UnipotentSums EntryMinorBounds
open Formalism.FourierDecayAlt.P.NormEntryBounds
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.NormEntryBounds
theorem _root_.solution (A M : B.Mat k r) (a b : ℝ) (ha : ∀ i j, ‖A i j‖ ≤ a) (hb : ∀ i j, ‖M i j‖ ≤ b)
    (hb0 : 0 ≤ b) (i j : Fin (2 * r + k + 1)) :
    ‖(A * M) i j‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (a * b) := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have ht : ∀ p, ‖A i p * M p j‖ ≤ a * b := by
    intro p
    rw [norm_mul]
    exact mul_le_mul (ha i p) (hb p j) (norm_nonneg _) (le_trans (norm_nonneg _) (ha i p))
  calc ∑ p, ‖A i p * M p j‖ ≤ ∑ _p : Fin (2 * r + k + 1), a * b := Finset.sum_le_sum (fun p _ => ht p)
    _ = ((2 * r + k + 1 : ℕ) : ℝ) * (a * b) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
end Formalism.FourierDecayAlt.P.NormEntryBounds
