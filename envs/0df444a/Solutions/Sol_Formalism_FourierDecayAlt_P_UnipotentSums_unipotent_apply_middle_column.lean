-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentSums.unipotent_apply_middle_column
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:17:30.487845+00:00
-- url     : https://prove2.me/submissions/680c3150-0fc3-4eec-b4c3-5b8219669cba

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentSums

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
open Formalism.FourierDecayAlt.P.UnipotentSums
open C2x5 C2x6 FlagSpanVanishing HermitianXiVector
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.UnipotentSums
theorem _root_.solution (vX : Matrix (Fin r) (Fin r) ℂ) (p j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    C2.mX k r vX p j = if p = j then 1 else 0 := by
  have hne : ∀ h : p.val < r ∨ r + k < p.val, p ≠ j := fun h he => by rw [he] at h; omega
  simp only [C2.mX]
  by_cases h1 : p.val < r
  · rw [dif_pos h1, dif_neg (show ¬ j.val < r by omega), if_neg (hne (Or.inl h1))]
  · by_cases h2 : r + k < p.val
    · rw [dif_neg h1, dif_pos h2, dif_neg (show ¬ r + k < j.val by omega), if_neg (hne (Or.inr h2))]
    · rw [dif_neg h1, dif_neg h2]
end Formalism.FourierDecayAlt.P.UnipotentSums
