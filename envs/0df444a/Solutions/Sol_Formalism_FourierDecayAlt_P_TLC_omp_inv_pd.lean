-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TLC.omp_inv_pd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:29:07.329944+00:00
-- url     : https://prove2.me/submissions/631be04f-bcb9-4dbd-b466-4753a7618134

import Definitions.Def_Formalism_HermitianCurvature_StatementTL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OmpCofLPd
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_star_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TLC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TLC
theorem _root_.solution (q s : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => (Hpk k r * gᴴ * Hpk k r) q s) := by
  simp only [Matrix.mul_apply, conjTranspose_apply]
  refine pd_sum _ fun u _ => pd_mono (show 1 + 0 ≤ 1 by omega) (pd_mul ?_ (pd_const _ 0))
  exact pd_sum _ fun t _ => pd_mono (show 0 + 1 ≤ 1 by omega) (pd_mul (pd_const _ 0) (pd_star_entry _ _))
end Formalism.FourierDecayAlt.P.TLC
