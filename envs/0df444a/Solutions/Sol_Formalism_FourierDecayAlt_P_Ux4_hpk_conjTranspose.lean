-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.hpk_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:17:36.327184+00:00
-- url     : https://prove2.me/submissions/54d61b51-a757-4872-98f7-a5d019710251

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux4
theorem _root_.solution (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Hpk]
  by_cases hab : a = b
  · subst hab
    split_ifs <;> simp
  · have hba : b ≠ a := Ne.symm hab
    have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
    simp only [hab, hba, and_false, if_false]
    split_ifs <;> first | (exfalso; omega) | simp
end Formalism.FourierDecayAlt.P.Ux4
