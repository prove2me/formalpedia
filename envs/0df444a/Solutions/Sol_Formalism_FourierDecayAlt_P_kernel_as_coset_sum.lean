-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.kernel_as_coset_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:00.14337+00:00
-- url     : https://prove2.me/submissions/4347c318-3e35-43bb-a8c0-6b5ebc45288e

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_kernel_quotient_finite
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.KpFromBB := by
  classical
  intro K _ _ _ R ψ hD w w'
  have hfin := kernel_quotient_finite K R ψ hD w w'
  unfold Kp
  rw [← finsum_comp_equiv (Equiv.prodComm (Cos R w') (Cos R w))]
  rw [finsum_curry]
  · refine finsum_congr fun q' => ?_
    unfold bbZ
    by_cases h : IsInt R (orbZ w' (rep R q'))
    · rw [if_pos h, finsum_mul]
      refine finsum_congr fun q => ?_
      by_cases h2 : IsInt R (orbZ w (rep R q))
      · simp only [pairTerm, Equiv.prodComm_apply, Prod.swap_prod_mk, h, h2, and_self, if_true]
        rfl
      · simp only [pairTerm, Equiv.prodComm_apply, Prod.swap_prod_mk, h, h2, false_and, if_false,
          zero_mul]
    · simp [pairTerm, h]
  · have := hfin.preimage ((Equiv.prodComm (Cos R w') (Cos R w)).injective.injOn)
    exact this
end Formalism.FourierDecayAlt.P
