-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_gC_mul_gI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:08.026273+00:00
-- url     : https://prove2.me/submissions/ed8777f7-65a0-4fb3-b01f-bf4e72dda897

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) : qs_gC n * qs_gI n = 1 := by
  have h1 : qs_gC n = (genMat ℤ n).map (algebraMap _ (GLCoord ℤ n)) := rfl
  have h2 : qs_gI n = (((detU n)⁻¹ : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) •
      ((genMat ℤ n).adjugate).map (algebraMap _ (GLCoord ℤ n)) := by
    ext a b; simp [qs_gI, ginvC]
  rw [h1, h2, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
  ext a b
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact (detU n).inv_mul
  · simp [Matrix.one_apply_ne hab]
end Formalism.InvariantFactorPaths.ColumnFamilies
