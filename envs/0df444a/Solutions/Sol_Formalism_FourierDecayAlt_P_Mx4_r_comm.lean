-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.r_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:42.65422+00:00
-- url     : https://prove2.me/submissions/85bd1042-d22a-470d-8dcc-a420b49090fe

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_up_square
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_corner
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_prod_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_prod_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (P : Par) (hP : P.OK) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    sR P j * sR P l * Matrix.diagonal (fun π => rho P π j - rho P π l - 1) =
      sR P l * sR P j * Matrix.diagonal (fun π => rho P π j - rho P π l + 1) := by
  ext π2 π
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
  by_cases h : ∃ π1, Up P l π π1 ∧ Up P j π1 π2
  · obtain ⟨π1, h1, h2⟩ := h
    obtain ⟨π3, h3, h4⟩ := up_square P l j hjl π π1 π2 h1 h2
    rw [prod_one P l j π π1 π2 h1 h2, prod_one P j l π π3 π2 h3 h4]
    exact (corner P hP l j hl hj hjl π π1 π3 h1 h3).1
  · have h' : ¬ ∃ π3, Up P j π π3 ∧ Up P l π3 π2 :=
      fun ⟨π3, h3, h4⟩ => h (up_square P j l hjl.symm π π3 π2 h3 h4)
    rw [prod_zero h, prod_zero h', zero_mul, zero_mul]
end Formalism.FourierDecayAlt.P.Mx4
