-- Prove2me | solution 1 for ConnesGreen.canonical_quartet_arithmetic_sign_cut
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T04:43:15.532038+00:00
-- url     : https://prove2.me/submissions/18716b1c-869e-4be4-98f9-3d1fbb524791

import Theorems.Thm_ConnesGreen_canonical_quartet_last_inner_half_window
import Theorems.Thm_ConnesGreen_canonical_negative_tests_after_half_cut
import Theorems.Thm_ConnesGreen_canonicalPicardMarker_lower_iff_restored_weil_actor_bound
import Definitions.Def_ConnesGreen_original_quartet
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
import Definitions.Def_ConnesGreen_small_support_constants
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative ConnesRZQuartet
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
private lemma half_iff_restored (T : ℝ) (hT : 0 < T) (S : Finset CriticalZeros) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S ↔
    ∀ g : ℝ → ℂ, SupportedTest T g →
      0 ≤ (weilDistribution (conv g (starInv g))).re +
        ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 := by
  rw [canonicalPicardMarker_lower_iff_restored_weil_actor_bound T hT S (1 / 2)
    (by norm_num) (by norm_num)]
  apply forall_congr'
  intro g
  apply imp_congr_right
  intro hg
  norm_num
  constructor <;> intro h <;> linarith
theorem solution
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        (∀ g : ℝ → ℂ, SupportedTest T g →
          0 ≤ (weilDistribution (conv g (starInv g))).re +
            ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
              (sourceEmbed T (problemOneL g))‖ ^ 2) ↔ T ≤ c) ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
            (sourceEmbed T (problemOneL g))‖ ^ 2 <
              -(weilDistribution (conv g (starInv g))).re ∧
          (weilDistribution (conv g (starInv g))).re < 0 := by
  obtain ⟨c, hrc, hcut⟩ := canonical_quartet_last_inner_half_window ρ hoff
  refine ⟨c, hrc, ?_, ?_⟩
  · intro T hT
    exact (half_iff_restored T hT (quartet ρ)).symm.trans (hcut T hT)
  · intro T hT hcT
    obtain ⟨g, hg, _, hbackground⟩ := canonical_negative_tests_after_half_cut (quartet ρ) c hcut T hT hcT
    refine ⟨g, hg, hbackground, ?_⟩
    have hn := sq_nonneg ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
      (sourceEmbed T (problemOneL g))‖
    linarith
