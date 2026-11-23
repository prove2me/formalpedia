-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.hs_L_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:37.791328+00:00
-- url     : https://prove2.me/submissions/0d13ca2a-386d-40b2-83dc-1f643fd7d29b

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
variable {A : Type} [CommRing A]
variable {K : Type} [CommRing K] {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution {m : ℕ} (t c : K) (ξ : Fin m → K) (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    Hm t c ξ u = hs_L ξ * Hm t c 0 u := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i' => ?_) i
  · have h1 : ∀ k : Fin m, hs_L ξ 0 k.succ = ξ (Fin.rev k) := by
      intro k
      have : (0 : Fin (m + 1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
      simp [hs_L, this]
    have h0 : hs_L ξ 0 0 = 1 := by simp [hs_L]
    simp only [h1, h0, Hm, Fin.cases_zero, Fin.cases_succ, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, zero_add, one_mul]
    ring
  · have h0 : hs_L ξ i'.succ 0 = 0 := by simp [hs_L, Fin.succ_ne_zero]
    have h1 : ∀ k : Fin m, hs_L ξ i'.succ k.succ = if i' = k then 1 else 0 := by
      intro k
      simp [hs_L, Fin.succ_ne_zero]
    simp only [h0, h1, zero_mul, zero_add, Hm, Fin.cases_succ, ite_mul, one_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
