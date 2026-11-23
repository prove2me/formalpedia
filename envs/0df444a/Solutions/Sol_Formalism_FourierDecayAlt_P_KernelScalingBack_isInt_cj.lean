-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.isInt_cj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:22:45.983828+00:00
-- url     : https://prove2.me/submissions/28aa0b30-0205-4252-bf11-6ece0b106e0c

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
    (hd : ∀ b, ((d b : Kˣ) : K) ∈ R ∧ (((d b)⁻¹ : Kˣ) : K) ∈ R) (g : GL (Fin n) K) :
    IsInt R ((cj d g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ↔
      IsInt R (g : Matrix (Fin n) (Fin n) K) := by
  constructor
  · intro h a b
    rw [entry_back d]
    exact R.mul_mem (R.mul_mem (hd a).1 (h a b)) (hd b).2
  · intro h a b
    rw [cj_apply]
    exact R.mul_mem (R.mul_mem (hd a).2 (h a b)) (hd b).1
end Formalism.FourierDecayAlt.P.KernelScalingBack
