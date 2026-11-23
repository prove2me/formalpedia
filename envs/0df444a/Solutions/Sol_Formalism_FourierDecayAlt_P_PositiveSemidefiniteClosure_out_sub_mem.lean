-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.out_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:12.63626+00:00
-- url     : https://prove2.me/submissions/c2c8f81f-579a-467b-ba47-36706b0fa1d3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedVectorChoices
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
set_option maxHeartbeats 400000
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
namespace Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
theorem _root_.solution {K : Type} [CommRing K] (Λ : AddSubgroup K) (z : K) :
    (Quotient.out ((z : K) : K ⧸ Λ) : K) - z ∈ Λ := by
  have h : ((Quotient.out ((z : K) : K ⧸ Λ) : K) : K ⧸ Λ) = (z : K ⧸ Λ) := QuotientAddGroup.out_eq' _
  rw [QuotientAddGroup.eq] at h
  have := Λ.neg_mem h
  simpa [sub_eq_add_neg, add_comm] using this
end Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
