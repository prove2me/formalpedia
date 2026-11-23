-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.uGram_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:49.658719+00:00
-- url     : https://prove2.me/submissions/a04d0f9d-1001-4493-9591-b5f7568fc67c

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
theorem _root_.solution {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ)
    (cr : K ⧸ R.toAddSubgroup → Kˣ) (S : Set K) (h h' : Point K) (t t' : Kˣ)
    (T : Finset (K ⧸ R.toAddSubgroup))
    (hT : ∀ x, x ∉ T → Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) = 0) :
    uGram R ψ m cr S h h' t t' =
      ((modK R ((t : K) * (t' : K)) ^ (m * (m + 1) / 2) : ℝ) : ℂ) *
        ∑ x ∈ T.filter (fun x => (cr x : K) ∈ S),
          Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) := by
  unfold uGram
  congr 1
  rw [finsum_eq_sum_of_support_subset (s := T), Finset.sum_filter]
  intro x hx
  by_contra hxT
  apply hx
  simp only [Finset.mem_coe] at hxT
  show (if (cr x : K) ∈ S then Kp R ψ (pt2 h m t (cr x)) (pt2 h' m t' (cr x)) else 0) = 0
  rw [hT x hxT]; simp
end Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
