-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.zhat_apply_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:50:46.457273+00:00
-- url     : https://prove2.me/submissions/567ed3c4-ad60-4074-b7c0-24c5fceea5ed

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_hpk_row
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_row


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux3
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (a b : Fin (r + 1)) (ha : a.val < r) (hb : b.val < r) :
    Zhat k r z z' g a b = g ⟨2 * r + k - a.val, by omega⟩ ⟨b.val, by omega⟩ := by
  unfold Zhat fvec herm
  rw [dif_pos ha, dif_pos hb]
  have hstar : star (bvec (eI k r ⟨a.val, ha⟩)) = bvec (eI k r ⟨a.val, ha⟩) := by
    ext i; simp only [bvec, Pi.star_apply, Pi.single_apply]; split_ifs <;> simp
  rw [hstar]
  simp only [bvec, eI]
  rw [Matrix.mulVec_single, single_dotProduct, one_mul, Matrix.mulVec, dotProduct]
  simp_rw [hpk_row k r a.val ha]
  simp
end Formalism.FourierDecayAlt.P.Ux3
