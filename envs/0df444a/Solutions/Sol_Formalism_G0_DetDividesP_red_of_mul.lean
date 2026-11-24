-- Prove2me | solution 1 for Formalism.G0.DetDividesP.red_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:39.514973+00:00
-- url     : https://prove2.me/submissions/5ff1c756-9869-423f-ae55-308f62c0f1ea

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_aeval_ptA_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution (hr : 0 < r) (A : Fin r → ι) (G' : MvPolynomial (ι × Fin r) K) (n : ℕ)
    (h : Red A (detLetters (K := K) A * G') (n + 1)) : Red A G' n := by
  intro L _ _ g x hx
  have h1 := h L g x hx
  rw [map_mul, aeval_ptA_det hr, pow_succ, mul_comm (C _) X, mul_assoc, mul_comm (X ^ n) X] at h1
  have h2 := (mul_dvd_mul_iff_left (X_ne_zero : (X : L[X]) ≠ 0)).mp h1
  exact (IsUnit.dvd_mul_left (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hx))).mp h2
end Formalism.G0.DetDividesP
