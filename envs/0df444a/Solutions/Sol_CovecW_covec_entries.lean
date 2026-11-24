-- Prove2me | solution 1 for CovecW.covec_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:05:09.048799+00:00
-- url     : https://prove2.me/submissions/44e5dcbd-a9ba-49e3-a781-73634ce34c33

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianCovectors_HermBvecLeft
import Theorems.Thm_CovecW_Hpk_mul_eI
import Theorems.Thm_CovecW_Hpk_mul_esI
import Theorems.Thm_CovecW_mul_Hpk_eI
import Theorems.Thm_CovecW_mulVec_bvec
import Theorems.Thm_CovecW_herm_bvec_left
import Theorems.Thm_CovecW_zhat_lo
import Theorems.Thm_CovecW_inv_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CovecW
open Formalism.QuantumDeterminants
namespace CovecW
theorem _root_.solution : Formalism.FourierDecayAlt.C3.XiYZhat := by
  intro k r z z' g a b hg
  refine ⟨(zhat_lo k r z z' g a b).symm, ?_⟩
  rw [zhat_lo, herm_bvec_left, Hpk_mul_eI, mulVec_bvec, inv_eq k r g hg]
  beta_reduce
  rw [Matrix.mul_assoc, Hpk_mul_esI, mul_Hpk_eI, Matrix.conjTranspose_apply]
end CovecW
