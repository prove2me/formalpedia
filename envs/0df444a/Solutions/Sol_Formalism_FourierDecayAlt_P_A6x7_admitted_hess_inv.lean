-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.admitted.hess_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:29.792697+00:00
-- url     : https://prove2.me/submissions/90de80e9-c6b1-47f8-84b8-066d0b112d18

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.admitted
namespace Formalism.FourierDecayAlt.P.A6x7.admitted
theorem _root_.solution {K : Type} [CommRing K] (m : ℕ) (a : Kˣ) (c : K) (hc : ((m + 1 : ℕ) : K) * c = 1) :
    hessM m a * ((a : K) • (1 - c • Matrix.of fun _ _ => (1 : K))) = 1 := by
  unfold hessM
  have hJ : (Matrix.of fun _ _ => (1 : K) : Matrix (Fin m) (Fin m) K) *
      (Matrix.of fun _ _ => (1 : K)) = (m : K) • Matrix.of fun _ _ => (1 : K) := by
    ext i j; simp [Matrix.mul_apply]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.inv_mul, one_smul, Matrix.add_mul,
    Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hJ, smul_smul]
  have : (1 : K) - c - c * (m : K) = 0 := by push_cast at hc; linear_combination -hc
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
    mul_one]
  linear_combination this
end Formalism.FourierDecayAlt.P.A6x7.admitted
