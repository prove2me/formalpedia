-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentSums.sig_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:08:03.614289+00:00
-- url     : https://prove2.me/submissions/804d5ca3-0975-4c05-a7bc-c9a8d0c76d3e

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
theorem _root_.solution (c : Fin r) : GBasic.sig k r (eI k r c) = esI k r c := by
  unfold GBasic.sig
  split_ifs with h
  · rfl
  · exact absurd (Or.inl c.isLt) h
end Formalism.FourierDecayAlt.P.UnipotentSums
