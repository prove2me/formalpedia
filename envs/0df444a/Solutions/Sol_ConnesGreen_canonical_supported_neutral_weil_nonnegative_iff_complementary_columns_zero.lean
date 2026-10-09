-- Prove2me | solution 1 for ConnesGreen.canonical_supported_neutral_weil_nonnegative_iff_complementary_columns_zero
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T13:46:10.453601+00:00
-- url     : https://prove2.me/submissions/dd808daa-6607-4540-9fcd-069bc6c9209e

import Theorems.Thm_ConnesGreen_canonical_signed_actor_arithmetic
import Definitions.Def_ConnesGreen_RG0_original_actors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
private theorem partition_helper (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (h : Physical t) :
    ‖(ContinuousLinearMap.adjoint (canonicalSelectedSynthesis t ht S)) h‖ ^ 2 +
      ‖(ContinuousLinearMap.adjoint (canonicalBackgroundSynthesis t ht S)) h‖ ^ 2 =
      ‖(ContinuousLinearMap.adjoint (canonicalNegativeSynthesis t ht)) h‖ ^ 2 := by
  rw [canonicalSelectedSynthesis, canonicalBackgroundSynthesis, canonicalNegativeSynthesis,
    columnSynthesis_adjoint_norm_sq, columnSynthesis_adjoint_norm_sq,
    columnSynthesis_adjoint_norm_sq]
  have hs : Summable (fun ρ : CriticalZeros =>
      ‖⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, h⟫_ℂ‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun ρ => ?_) ((canonical_actor_columns_summable t ht).2.mul_right (‖h‖ ^ 2))
    simpa only [mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _)
        (norm_inner_le_norm (𝕜 := ℂ)
          (negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) h) 2
  exact hs.tsum_subtype_add_tsum_subtype_compl (S : Set CriticalZeros)

theorem balance_helper (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest t g)
    (hn : ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 -
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 = 0) :
    (weilDistribution (conv g (starInv g))).re = -‖(canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 := by
  have hf := canonical_signed_actor_arithmetic t ht g hg
  have hp := partition_helper t ht S (sourceEmbed t (problemOneL g))
  linarith
theorem background_helper (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest t g)
    (hn : ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 -
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 = 0) :
    0 ≤ (weilDistribution (conv g (starInv g))).re ↔ (canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g)) = 0 := by
  have he := balance_helper t ht S g hg hn
  constructor
  · intro hw
    have hz : ‖(canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ = 0 := by
      nlinarith [norm_nonneg ((canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g)))]
    exact norm_eq_zero.mp hz
  · intro hz
    rw [hz] at he
    simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero, he] using (le_refl (0 : ℝ))
private theorem background_columns_helper (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (x : Physical t) :
    (canonicalBackgroundSynthesis t ht S).adjoint x = 0 ↔
      ∀ ρ : {ρ : CriticalZeros // ρ ∉ S},
        ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1, x⟫_ℂ = 0 := by
  have he : ∀ ρ : {ρ : CriticalZeros // ρ ∉ S},
      ((canonicalBackgroundSynthesis t ht S).adjoint x) ρ =
        ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1, x⟫_ℂ := by
    intro ρ
    rw [canonicalBackgroundSynthesis, columnSynthesis_adjoint_coordinate]
  constructor
  · intro hz ρ
    rw [← he ρ, hz]
    rfl
  · intro hs
    apply lp.ext
    funext ρ
    change ((canonicalBackgroundSynthesis t ht S).adjoint x) ρ = 0
    exact (he ρ).trans (hs ρ)
theorem solution (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest t g)
    (hn : ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 -
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 = 0) :
    0 ≤ (weilDistribution (conv g (starInv g))).re ↔
    ∀ ρ : {ρ : CriticalZeros // ρ ∉ S},
      ⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1,
        sourceEmbed t (problemOneL g)⟫_ℂ = 0 := by
  rw [background_helper t ht S g hg hn]
  exact background_columns_helper t ht S (sourceEmbed t (problemOneL g))
