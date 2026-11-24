-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NormEntryBounds.gN_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:29.722629+00:00
-- url     : https://prove2.me/submissions/edac4e7c-92c2-494d-8fba-8f414581f97b

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
theorem _root_.solution (g : B.Mat k r) (E : ℝ) (hE : 0 ≤ E) (h : ∀ i j, ‖g i j‖ ≤ E) :
    B.gN g ≤ ((2 * r + k + 1 : ℕ) : ℝ) * E := by
  unfold B.gN
  rw [show ((2 * r + k + 1 : ℕ) : ℝ) * E = Real.sqrt ((((2 * r + k + 1 : ℕ) : ℝ) * E) ^ 2) by
    rw [Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  have hs : ∀ i j, Complex.normSq (g i j) ≤ E ^ 2 := by
    intro i j; rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
  calc ∑ i, ∑ j, Complex.normSq (g i j) ≤ ∑ _i : Fin (2 * r + k + 1), ∑ _j : Fin (2 * r + k + 1), E ^ 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hs i j))
    _ = (((2 * r + k + 1 : ℕ) : ℝ) * E) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
end Formalism.FourierDecayAlt.P.NormEntryBounds
