-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentSums.unipotent_apply_middle_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:07:55.818084+00:00
-- url     : https://prove2.me/submissions/33af1e66-7387-4334-af79-c7dc1ee4d874

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
theorem _root_.solution (vX : Matrix (Fin r) (Fin r) ℂ) (i j : Fin (2 * r + k + 1)) (hi1 : r ≤ i.val) (hi2 : i.val ≤ r + k) :
    C2.mX k r vX i j = if i = j then 1 else 0 := by
  simp only [C2.mX]
  rw [dif_neg (show ¬ i.val < r by omega), dif_neg (show ¬ r + k < i.val by omega)]
end Formalism.FourierDecayAlt.P.UnipotentSums
