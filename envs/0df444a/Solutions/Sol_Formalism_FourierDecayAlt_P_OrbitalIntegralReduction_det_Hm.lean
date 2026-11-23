-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.det_Hm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:26.335963+00:00
-- url     : https://prove2.me/submissions/49138b2c-c223-4891-9679-1f4ff2a31daa

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hs_L_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hs_L_mul
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {A : Type} [CommRing A]
variable {K : Type} [CommRing K] {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution {m : ℕ} (t c : K) (ξ : Fin m → K) (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hu : IsUpUni u) : (Hm t c ξ u).det = (-1) ^ m * (c * t ^ m) := by
  rw [hs_L_mul, Matrix.det_mul, hs_L_det, one_mul, Matrix.det_succ_row_zero,
    Finset.sum_eq_single (Fin.last m)]
  · have hT : ((Hm t c 0 u).submatrix Fin.succ (Fin.last m).succAbove).IsUpperTriangular := by
      intro i j hij
      have hij' : j < i := hij
      have : u i.castSucc j.castSucc = 0 := hu.1 (by simpa using hij')
      simp [Hm, this]
    rw [Matrix.det_of_isUpperTriangular hT]
    simp [Hm, hu.2]
    ring
  · intro j _ hj
    simp [Hm, hj]
  · simp
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
