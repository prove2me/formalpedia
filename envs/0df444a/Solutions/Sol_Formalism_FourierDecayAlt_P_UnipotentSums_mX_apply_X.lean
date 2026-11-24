-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentSums.mX_apply_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:12:40.637151+00:00
-- url     : https://prove2.me/submissions/cfbfed13-f894-4ae3-a16c-29ccd94134e9

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
theorem _root_.solution (vX : Matrix (Fin r) (Fin r) ℂ) (c : Fin r) (j : Fin (2 * r + k + 1)) :
    C2.mX k r vX (eI k r c) j = if hj : j.val < r then vX c ⟨j.val, hj⟩ else 0 := by
  simp only [C2.mX]
  rw [dif_pos (show (eI k r c).val < r from c.isLt)]
  rfl
end Formalism.FourierDecayAlt.P.UnipotentSums
