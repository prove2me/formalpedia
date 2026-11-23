-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.sg_units
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:16.536823+00:00
-- url     : https://prove2.me/submissions/3a01d85f-89f2-4152-8bad-c5357b2f6918

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hs_sg_succ
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
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (e : Fin (n + 1) → A)
    (he : ∀ i, M i i * e i = 1) :
    sg M = (∏ i, M i i) * ∑ i : Fin n, M i.castSucc i.succ * e i.castSucc * e i.succ := by
  induction n with
  | zero => simp [sg]
  | succ n ih =>
    have := ih (M.submatrix Fin.succ Fin.succ) (fun i => e i.succ) (fun i => he i.succ)
    rw [hs_sg_succ, this, Fin.prod_univ_succ (fun i => M i i), Fin.sum_univ_succ,
      Fin.prod_univ_succ (fun i : Fin (n + 1) => M i.succ i.succ)]
    simp only [Matrix.submatrix_apply, Fin.succ_castSucc, Fin.castSucc_zero]
    have h3 : (Fin.succ (0 : Fin (n + 1))) = 1 := rfl
    rw [h3]
    have e0 := he 0
    have e1 := he 1
    rw [Fin.prod_univ_succ (fun i : Fin (n + 1) => M i.succ i.succ), h3]
    linear_combination (-(M 0 1 * ∏ k : Fin n, M k.succ.succ k.succ.succ) * (M 1 1 * e 1)) * e0 -
      (M 0 1 * ∏ k : Fin n, M k.succ.succ k.succ.succ) * e1
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
