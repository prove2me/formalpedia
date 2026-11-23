-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.fa_Hm_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:53.993187+00:00
-- url     : https://prove2.me/submissions/14f351f9-4ea3-47a7-ac86-33d57124ee3b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
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
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution {m : ℕ} (t c : K) (ξ : Fin m → K) (u r : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hr : IsUpUni r) : Hm t c ξ (u * r) = Hm t c ξ u * r := by
  have hlast : ∀ j, r (Fin.last m) j = if j = Fin.last m then 1 else 0 := by
    intro j
    split_ifs with h
    · rw [h]; exact hr.2 _
    · exact hr.1 (lt_of_le_of_ne (Fin.le_last j) h)
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp only [Hm, Fin.cases_zero, Matrix.mul_apply, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    · simp [hlast]
  · simp only [Hm, Fin.cases_succ, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => by ring
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
