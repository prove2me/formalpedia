-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x6.herm_ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:17:07.68343+00:00
-- url     : https://prove2.me/submissions/c71708a3-e498-4b8c-9f43-81f87719b7fc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_hzz_real
import Theorems.Thm_Formalism_QuantumDeterminants_ggBlockA


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
open Formalism.FourierDecayAlt.P.C2x6
open C2x5
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x6
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a b : Fin (r + 1)) :
    herm (Hpk k r) (fvec k r z b) (fvec k r z a) = C2.Adiag k r z a b := by
  rw [ggBlockA k r z hz a b, hzz_real]
  simp only [C2.Adiag, ggLastU, Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r
  · subst ha hb; simp
  · simp [ha, hb, Ne.symm hb, show a ≠ b from fun h => hb (h ▸ ha)]
  · simp [ha, hb, show a ≠ b from fun h => ha (h ▸ hb)]
  · by_cases hab : a = b
    · subst hab; simp [ha]
    · simp [ha, hab]
end Formalism.FourierDecayAlt.P.C2x6
