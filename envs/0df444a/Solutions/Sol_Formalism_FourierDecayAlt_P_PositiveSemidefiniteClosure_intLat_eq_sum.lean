-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.intLat_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:27.432002+00:00
-- url     : https://prove2.me/submissions/636fa7e3-02ed-43df-926b-90d1cca5bfea

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
open Classical
namespace Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
theorem _root_.solution {K : Type} [CommRing K] (R : Subring K) (Λ : AddSubgroup K) (Om : Set K)
    (hfin : {y : K ⧸ Λ | (Quotient.out y : K) ∈ Om}.Finite) (g : K → ℂ) :
    intLat R Λ Om g = (volL R Λ : ℂ) * ∑ y ∈ hfin.toFinset, g (Quotient.out y) := by
  unfold intLat
  congr 1
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · apply Finset.sum_congr rfl
    intro y hy
    rw [Set.Finite.mem_toFinset] at hy
    exact if_pos hy
  · intro y hy
    by_contra hyT
    apply hy
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hyT
    exact if_neg hyT
end Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
