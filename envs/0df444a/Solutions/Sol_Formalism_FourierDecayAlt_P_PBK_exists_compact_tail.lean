-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.exists_compact_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:02.454218+00:00
-- url     : https://prove2.me/submissions/d47786f4-b186-4d2e-a156-8d36b4ab8df2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockPSDCongr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (μ : Measure ℂ) [NullSingletonClass μ] (φ : ℂ → ℝ) (hφ : Integrable φ μ) (η : ℝ) (hη : 0 < η) :
    ∃ K : Set ℂ, IsCompact K ∧ (0 : ℂ) ∉ K ∧ ∫ D in Kᶜ, φ D ∂μ < η := by
  let K : ℕ → Set ℂ := fun n => {D | ((n : ℝ) + 1)⁻¹ ≤ ‖D‖ ∧ ‖D‖ ≤ (n : ℝ) + 1}
  have hKc : ∀ n, IsCompact (K n) := fun n => by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := (n : ℝ) + 1)).subset fun D hD => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hD.2
  have hK0 : ∀ n, (0 : ℂ) ∉ K n := fun n h => by
    have h1 := h.1
    rw [norm_zero] at h1
    exact absurd h1 (not_le.mpr (by positivity))
  have hmono : Monotone K := by
    intro m n hmn D hD
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have h : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
    exact ⟨le_trans (inv_anti₀ (by positivity) h) hD.1, hD.2.trans h⟩
  have hKm : ∀ n, MeasurableSet (K n)ᶜ := fun n => (hKc n).isClosed.measurableSet.compl
  have hanti : Antitone fun n => (K n)ᶜ := fun m n h => Set.compl_subset_compl.mpr (hmono h)
  have hinter : ⋂ n, (K n)ᶜ = {0} := by
    ext D
    simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      by_contra hD
      obtain ⟨n, hn⟩ := exists_nat_ge (max ‖D‖ ‖D‖⁻¹)
      have hpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
      apply h n
      refine ⟨?_, ?_⟩
      · have h1 : ‖D‖⁻¹ ≤ (n : ℝ) + 1 :=
          (le_max_right _ _).trans (hn.trans (le_add_of_nonneg_right zero_le_one))
        exact inv_le_of_inv_le₀ hpos h1
      · exact (le_max_left _ _).trans (hn.trans (le_add_of_nonneg_right zero_le_one))
    · rintro rfl n
      exact hK0 n
  have ht := tendsto_setIntegral_of_antitone hKm hanti ⟨0, hφ.integrableOn⟩
  have h0 : ∫ x in ({0} : Set ℂ), φ x ∂μ = 0 := by
    rw [Measure.restrict_eq_zero.mpr (measure_singleton 0), integral_zero_measure]
  rw [hinter, h0] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hη)).exists
  exact ⟨K n, hKc n, hK0 n, hn⟩
end Formalism.FourierDecayAlt.P.PBK
