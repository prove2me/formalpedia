-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.hess_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:58.040869+00:00
-- url     : https://prove2.me/submissions/bd9b1fd0-1e92-48a2-9704-800fdd048d5d

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hs_succAbove_one_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hs_succAbove_one_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hs_isHess_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hs_isHess_above
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hess_laplace
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hess_one
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
theorem _root_.solution {n : ℕ} {t : A} (M : Matrix (Fin n) (Fin n) A) (h : IsHess t M) :
    ∃ r, M.det = ∏ i, M i i - t * sg M + t ^ 2 * r := by
  induction n with
  | zero => exact ⟨0, by simp [sg]⟩
  | succ n ih =>
    cases n with
    | zero => exact ⟨0, by simp [sg]⟩
    | succ k =>
      obtain ⟨r, hr⟩ := ih (M.submatrix Fin.succ Fin.succ) (hs_isHess_succ h)
      obtain ⟨r', hr'⟩ := hess_one (M.submatrix (Fin.succAbove 1) Fin.succ) (hs_isHess_above h)
      refine ⟨M 0 0 * r - r', ?_⟩
      rw [hess_laplace M h, hr, hr', hs_sg_succ, Fin.prod_univ_succ (fun i => M i i),
        Fin.prod_univ_succ (fun i => (M.submatrix (Fin.succAbove 1) Fin.succ) i i)]
      simp only [Matrix.submatrix_apply, hs_succAbove_one_zero, hs_succAbove_one_succ]
      have h3 : (Fin.succ (0 : Fin (k + 1))) = 1 := rfl
      rw [h3]
      ring
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
