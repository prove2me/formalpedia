-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.lu_mul_EE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:58.204843+00:00
-- url     : https://prove2.me/submissions/aecf7a6a-0005-45e3-9c75-190d6655eb92

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_lu_EE_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_lu_sum_pairs
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
theorem _root_.solution {n : ℕ} {u : Matrix (Fin n) (Fin n) K} (hu : IsUpUni u) (r : Pr n → K) :
    u * EE r = EE (lu_M u *ᵥ r) := by
  ext i j
  rw [Matrix.mul_apply]
  have e1 : ∑ k, u i k * EE r k j = ∑ k : Fin n, if h : k < j then u i k * r ⟨(k, j), h⟩ else 0 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : k < j
    · rw [lu_EE_lt r h, dif_pos h]
    · rw [lu_EE_not_lt r h, dif_neg h, mul_zero]
  rw [e1]
  by_cases hij : i < j
  · rw [lu_EE_lt _ hij, ← lu_sum_pairs j (fun p => u i p.1.1 * r p)]
    simp only [Matrix.mulVec, dotProduct, lu_M]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  · rw [lu_EE_not_lt _ hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h : k < j
    · rw [dif_pos h]
      have : u i k = 0 := hu.1 (lt_of_lt_of_le h (not_lt.1 hij))
      rw [this, zero_mul]
    · rw [dif_neg h]
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
