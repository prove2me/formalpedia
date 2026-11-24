-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_det_zpow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:33:03.873773+00:00
-- url     : https://prove2.me/submissions/a129c5c1-5e58-4a64-a5f3-a21126703e54

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_prod_castLE
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_mem_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_evGLR_det

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
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (z : ℤ) : (((qhDet R n) ^ z : (GLCoord R n)ˣ) : GLCoord R n) ∈ inducedSections R (fun _ : Fin n => z) := by
  rw [qh_mem_iff]
  intro R' _ _ b g u hb hu
  have h1 : ∀ h : GL (Fin n) R', evGLR h (((qhDet R n) ^ z : (GLCoord R n)ˣ) : GLCoord R n) =
      (((Units.map (evGLR h : GLCoord R n →+* R').toMonoidHom (qhDet R n)) ^ z : R'ˣ) : R') := by
    intro h
    rw [← map_zpow]; rfl
  have h2 : Units.map (evGLR (b * g) : GLCoord R n →+* R').toMonoidHom (qhDet R n) =
      (∏ a, u a) * Units.map (evGLR g : GLCoord R n →+* R').toMonoidHom (qhDet R n) := by
    ext
    simp only [Units.coe_map, Units.val_mul, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [qh_evGLR_det, qh_evGLR_det, Units.val_mul, Matrix.det_mul,
      Matrix.det_of_isLowerTriangular _ (fun i j hij => hb i j hij)]
    simp [hu]
  rw [h1, h1, h2, mul_zpow, Finset.prod_zpow, Units.val_mul]
end Formalism.InvariantFactorPaths.ColumnFamilies
