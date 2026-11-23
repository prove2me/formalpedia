-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.st_lowW_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:11.195587+00:00
-- url     : https://prove2.me/submissions/50ab8a88-734d-4e05-889a-fdb59d39cd0f

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_antidiagonal_block_mul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_mul_antidiagonal_block_reversed
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_low_zero
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
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
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (n : ℕ) (z : Kˣ) (g : lowW K (addBlock h0 n z).1 (addBlock h0 n z).2) :
    g = 1 := by
  apply sec_m_ext
  obtain ⟨hg, H, hH, e⟩ := g.2
  have key : ∀ (G H : Matrix (Fin n) (Fin n) K), IsLowUni G → IsLowUni H →
      G * antidiagonalBlock n z = antidiagonalBlock n z * H → G = 1 := by
    intro G H hG hH e
    ext i k
    by_cases hik : i = k
    · rw [hik, hG.2 k, Matrix.one_apply_eq]
    rw [Matrix.one_apply_ne hik]
    rcases lt_or_gt_of_ne hik with h | h
    · exact Formalism.DoubleCosetMeasures.P.Phase.low_zero hG h
    · have e1 := congrFun (congrFun e i) (Fin.rev k)
      rw [mul_antidiagonal_block_reversed, antidiagonal_block_mul_left] at e1
      simp only [Matrix.submatrix_apply, id, Matrix.smul_apply, smul_eq_mul] at e1
      rw [Formalism.DoubleCosetMeasures.P.Phase.low_zero hH (Fin.rev_lt_rev.2 h), mul_zero] at e1
      exact z.isUnit.mul_left_eq_zero.1 e1
  exact key _ H hg hH e
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
