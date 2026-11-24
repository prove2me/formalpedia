-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentSums.mX_col_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:17:28.993797+00:00
-- url     : https://prove2.me/submissions/c0d34ff1-3890-4065-96aa-7f6ddebfb95c

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
theorem _root_.solution (vX : Matrix (Fin r) (Fin r) ℂ) (p : Fin (2 * r + k + 1)) (c : Fin r) :
    C2.mX k r vX p (eI k r c) = if hp : p.val < r then vX ⟨p.val, hp⟩ c else 0 := by
  have hc := c.isLt
  simp only [C2.mX]
  by_cases h1 : p.val < r
  · rw [dif_pos h1, dif_pos h1, dif_pos (show (eI k r c).val < r from hc)]
    rfl
  · rw [dif_neg h1, dif_neg h1]
    by_cases h2 : r + k < p.val
    · rw [dif_pos h2, dif_neg (show ¬ r + k < (eI k r c).val from by show ¬ r + k < c.val; omega)]
    · rw [dif_neg h2, if_neg]
      intro h
      apply h1
      rw [h]
      exact hc
end Formalism.FourierDecayAlt.P.UnipotentSums
