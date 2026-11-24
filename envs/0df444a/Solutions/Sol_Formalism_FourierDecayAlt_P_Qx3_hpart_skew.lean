-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.hpart_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:25:01.578366+00:00
-- url     : https://prove2.me/submissions/4ef56285-549e-43c3-949a-733caa3d285c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hsq : H * H = 1) (hh : Hᴴ = H) :
    (hpart1 H Z)ᴴ * H + H * hpart1 H Z = 0 ∧ (hpart2 H Z)ᴴ * H + H * hpart2 H Z = 0 := by
  have hinv : H⁻¹ = H := Matrix.inv_eq_right_inv hsq
  have e1 : H * Z * H * H = H * Z := by rw [Matrix.mul_assoc, hsq, Matrix.mul_one]
  have e2 : H * (H * Zᴴ * H) = Zᴴ * H := by
    rw [Matrix.mul_assoc H Zᴴ H, ← Matrix.mul_assoc H H, hsq, Matrix.one_mul]
  have e3 : (H * Zᴴ * H)ᴴ = H * Z * H := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hh,
      Matrix.mul_assoc]
  constructor
  · unfold hpart1
    rw [hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, e3, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sub_mul, Matrix.mul_sub, e1, e2]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]
    simp
  · unfold hpart2
    rw [hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, e3, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_add, e1, e2]
    have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
      simp [Complex.conj_I]
    rw [this, neg_smul, add_comm (Zᴴ * H) (H * Z), neg_add_cancel]
end Formalism.FourierDecayAlt.P.Qx3
