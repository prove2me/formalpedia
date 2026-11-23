-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.orbZ_fm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:22:45.814797+00:00
-- url     : https://prove2.me/submissions/c81c1bdf-aa45-4714-a1c1-5c26d35b331c

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K) (S : List ℕ) (T c : ℕ → Kˣ)
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution (p : lowW K S T × upUniG K S.sum) :
    orbZ ((S, T * c) : Point K) (fm S T c p) = orbZ ((S, T) : Point K) p *
      ((DG (dg S c) : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) := by
  show ((p.1.1 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) * pt S (T * c) *
      ((cj (dg S c) p.2.1 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) =
    ((p.1.1 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) * pt S T *
      ((p.2.1 : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) *
      ((DG (dg S c) : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K)
  rw [pt_scale]
  unfold cj
  rw [Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((DG (dg S c) : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K),
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
end Formalism.FourierDecayAlt.P.KernelScalingBack
