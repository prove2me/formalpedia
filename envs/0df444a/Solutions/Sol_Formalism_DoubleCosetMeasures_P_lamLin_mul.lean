-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.lamLin_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:32.459722+00:00
-- url     : https://prove2.me/submissions/4a39f249-91d6-4459-a318-55009c153d82

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_lastCoord_upUni
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_lamLin_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) R) (Z : Matrix (Fin n) (Fin n) K)
    (hA : (A.map R.subtype).det = 1) (hup : IsUpUni (B.map R.subtype)) (v : Fin n → R) :
    lamLin R (A.map R.subtype * Z * B.map R.subtype) (A *ᵥ v) = lamLin R Z v := by
  have hAinv : (A.map R.subtype)⁻¹ * A.map R.subtype = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [hA]; exact isUnit_one)
  have hBd : (B.map R.subtype).det = 1 := by
    rw [Matrix.det_of_upperTriangular hup.1]
    exact Finset.prod_eq_one (fun i _ => hup.2 i)
  have hBinv : B.map R.subtype * (B.map R.subtype)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by rw [hBd]; exact isUnit_one)
  have hlast : ∀ w : Fin n → K, lastCoord R ((B.map R.subtype)⁻¹ *ᵥ w) = lastCoord R w := by
    intro w
    rw [← lastCoord_upUni R hup ((B.map R.subtype)⁻¹ *ᵥ w), Matrix.mulVec_mulVec, hBinv,
      Matrix.one_mulVec]
  rw [lamLin_apply, lamLin_apply, coeLin_mulVec, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hAinv, Matrix.mul_one,
    ← Matrix.mulVec_mulVec, hlast]
end Formalism.DoubleCosetMeasures.P
