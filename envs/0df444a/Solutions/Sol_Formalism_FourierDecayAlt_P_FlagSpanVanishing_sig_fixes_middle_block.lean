-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FlagSpanVanishing.sig_fixes_middle_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:29:23.200836+00:00
-- url     : https://prove2.me/submissions/61d7e262-4215-4916-952f-220fd631888e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_mid


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
open Formalism.FourierDecayAlt.P.FlagSpanVanishing
open C2x5 C2x7
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FlagSpanVanishing
theorem _root_.solution (x : Fin (2 * r + k + 1)) (hx : r ≤ x.val ∧ x.val ≤ r + k) : GBasic.sig k r x = x :=
  GBasic.sig_mid k r x hx.1 hx.2
end Formalism.FourierDecayAlt.P.FlagSpanVanishing
