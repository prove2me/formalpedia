-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentSums.sig_esI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:12:43.103022+00:00
-- url     : https://prove2.me/submissions/557613c9-d2ba-409b-a874-e0a1106c271f

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
theorem _root_.solution (c : Fin r) : GBasic.sig k r (esI k r c) = eI k r c := by
  have hc := c.isLt
  unfold GBasic.sig
  split_ifs with h
  · exact Fin.ext (by show 2 * r + k - (2 * r + k - c.val) = c.val; omega)
  · exact absurd (Or.inr (by show r + k < 2 * r + k - c.val; omega)) h
end Formalism.FourierDecayAlt.P.UnipotentSums
