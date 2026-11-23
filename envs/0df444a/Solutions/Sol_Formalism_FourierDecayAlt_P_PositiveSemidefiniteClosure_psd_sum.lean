-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.psd_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:20.301686+00:00
-- url     : https://prove2.me/submissions/54d40747-37d3-4d0c-9df3-94d404886137

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedVectorChoices
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_psd_add
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_isPSD_zero
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
theorem _root_.solution {X ι : Type} {F : Finset X} (T : Finset ι) (k : ι → X → X → ℂ)
    (h : ∀ i ∈ T, IsPSD F (k i)) : IsPSD F (fun x y => ∑ i ∈ T, k i x y) := by
  classical
  induction T using Finset.induction_on with
  | empty => exact A5x6.isPSD_zero F _ (fun _ _ _ _ => by simp)
  | insert i T hi ih =>
    have h1 := psd_add (h i (Finset.mem_insert_self i T))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    exact psd_congr (fun x _ y _ => by rw [Finset.sum_insert hi]) h1
end Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
