-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.isInt_mul_DG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:41.523903+00:00
-- url     : https://prove2.me/submissions/690d5383-5765-4cde-b2ae-d7f7215970ea

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack

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
variable {K : Type} [CommRing K] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution (R : Subring K) (d : Fin n → Kˣ)
    (hd : ∀ b, ((d b : Kˣ) : K) ∈ R ∧ (((d b)⁻¹ : Kˣ) : K) ∈ R) (Z : Matrix (Fin n) (Fin n) K) :
    IsInt R (Z * ((DG d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ IsInt R Z := by
  constructor
  · intro h a b
    have h1 := h a b
    rw [DG_coe, mul_diagonal] at h1
    have h2 : Z a b = Z a b * ((d b : Kˣ) : K) * (((d b)⁻¹ : Kˣ) : K) := by
      rw [mul_assoc, Units.mul_inv, mul_one]
    rw [h2]
    exact R.mul_mem h1 (hd b).2
  · intro h a b
    rw [DG_coe, mul_diagonal]
    exact R.mul_mem (h a b) (hd b).1
end Formalism.FourierDecayAlt.P.KernelScalingBack
