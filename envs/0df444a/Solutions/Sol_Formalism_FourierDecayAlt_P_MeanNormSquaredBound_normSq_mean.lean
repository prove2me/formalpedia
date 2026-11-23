-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MeanNormSquaredBound.normSq_mean
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:58.613336+00:00
-- url     : https://prove2.me/submissions/36d0a9d7-3ecd-4bfd-a4b3-2e619cdc6673

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanNormSquaredBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanNormSquaredBound_inner_sum_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanNormSquaredBound_normSq_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_MeanNormSquaredBound_sum_sum_sum_sum_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.MeanNormSquaredBound
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.MeanNormSquaredBound
theorem _root_.solution {X α : Type} (L : E →ₗ[ℂ] E) (k : ℂ) (hk : conj k = k) (P : Finset α)
    (c : α → ℂ) (F : Finset X) (a : X → ℂ) (u : X → α → E) :
    ((‖L (k • ∑ p ∈ P, c p • ∑ h ∈ F, a h • u h p)‖ ^ 2 : ℝ) : ℂ) =
      ∑ h ∈ F, ∑ h' ∈ F, a h * conj (a h') *
        (k ^ 2 * ∑ p ∈ P, ∑ p' ∈ P, c p * conj (c p') * inner ℂ (L (u h' p')) (L (u h p))) := by
  have h1 : L (k • ∑ p ∈ P, c p • ∑ h ∈ F, a h • u h p) =
      ∑ p ∈ P, (k * c p) • ∑ h ∈ F, a h • L (u h p) := by
    simp only [map_smul, map_sum, Finset.smul_sum, smul_smul, mul_assoc]
  rw [h1, normSq_sum]
  simp only [inner_sum_sum, Finset.mul_sum]
  rw [sum_sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ =>
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
  rw [map_mul, hk]
  ring
end Formalism.FourierDecayAlt.P.MeanNormSquaredBound
