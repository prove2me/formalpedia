-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.inv_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:57.309554+00:00
-- url     : https://prove2.me/submissions/65eed9ec-4710-4d79-b5aa-7b49c2d313a0

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_isInt_adjugate


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution {n : ℕ} {Z : Matrix (Fin n) (Fin n) K} (hZ : IsInt R Z) {x : K}
    (hx : x * Ring.inverse Z.det ∈ R) (a b : Fin n) : x * Z⁻¹ a b ∈ R := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
  exact R.mul_mem hx (Formalism.DoubleCosetMeasures.P.isInt_adjugate R hZ a b)
end Formalism.FourierDecayAlt.P.KernelScalingBack
