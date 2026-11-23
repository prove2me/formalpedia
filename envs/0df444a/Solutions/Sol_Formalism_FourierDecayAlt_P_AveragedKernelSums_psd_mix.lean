-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AveragedKernelSums.psd_mix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:54.782163+00:00
-- url     : https://prove2.me/submissions/91f8e13d-305f-47b1-85f9-4f5de841a8f6

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
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



set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.AveragedKernelSums
open Formalism.FourierDecayAlt.P.A5x6
namespace Formalism.FourierDecayAlt.P.AveragedKernelSums
theorem _root_.solution {X Y : Type} (F : Finset X) (B : Finset Y) (e : Y → ℂ)
    (k : X × Y → X × Y → ℂ) (h : IsPSD (F ×ˢ B) k) :
    IsPSD F (fun x x' => ∑ b ∈ B, ∑ b' ∈ B, e b * conj (e b') * k (x, b) (x', b')) := by
  intro a
  have E : ∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) *
        (∑ b ∈ B, ∑ b' ∈ B, e b * conj (e b') * k (x, b) (y, b')) =
      ∑ q ∈ F ×ˢ B, ∑ q' ∈ F ×ˢ B, (a q.1 * e q.2) * conj (a q'.1 * e q'.2) * k q q' := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Finset.sum_product]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [map_mul]; ring
  rw [E]
  exact h _
end Formalism.FourierDecayAlt.P.AveragedKernelSums
