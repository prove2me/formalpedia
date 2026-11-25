-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.star_sgn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:43:56.859906+00:00
-- url     : https://prove2.me/submissions/09b19645-c651-487f-9be5-e452c397f82d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DpsiIsDerivation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangularFactorMiddleRow
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (p : Fin (2 * r + k + 1)) : star (WeylGroupFacts.sgn k r p) = WeylGroupFacts.sgn k r p := by
  unfold WeylGroupFacts.sgn; split_ifs <;> simp
end Formalism.FourierDecayAlt.P.SignAntidiagonal
