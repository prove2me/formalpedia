-- Prove2me | solution 1 for ConnesGreen.canonical_quartet_uniform_restored_arithmetic_margin
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T03:25:26.902078+00:00
-- url     : https://prove2.me/submissions/be8ddd38-0d45-4311-a022-16bd401e5a03

import Theorems.Thm_ConnesGreen_canonical_quartet_selected_mellin_witness
import Theorems.Thm_ConnesGreen_canonical_actor_test_norms_window_independent
import Theorems.Thm_ConnesGreen_canonical_signed_actor_arithmetic
import Definitions.Def_ConnesGreen_original_quartet
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative ConnesRZQuartet
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
private theorem amr_partition_helper (t : ℝ) (ht : 0 < t)
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

private lemma restored_positive_energy (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (g : ℝ → ℂ) (hg : SupportedTest t g) :
    (weilDistribution (conv g (starInv g))).re +
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
      ‖(canonicalBackgroundSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 =
      ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 := by
  have h := canonical_signed_actor_arithmetic t ht g hg
  have hp := amr_partition_helper t ht S (sourceEmbed t (problemOneL g))
  linarith
private lemma supported_mono {t T : ℝ} {g : ℝ → ℂ}
    (hg : SupportedTest t g) (htT : t ≤ T) : SupportedTest T g := by
  refine ⟨hg.1, ?_⟩
  intro x hx
  obtain ⟨hl, hr⟩ := hg.2 hx
  constructor <;> linarith
private lemma scalar_margin (p a : ℝ) (hp : 0 ≤ p) (hpa : p < a) :
    ∃ η m : ℝ, 0 < η ∧ η < 1 / 2 ∧ 0 < m ∧
      m ≤ a - ((1 / 2 - η)⁻¹ - 1) * p := by
  let κ := 1 + (a - p) / (2 * (p + 1))
  have hden : 0 < 2 * (p + 1) := by positivity
  have hκ : 1 < κ := by dsimp [κ]; have := div_pos (sub_pos.mpr hpa) hden; linarith
  have hgap : 0 < a - κ * p := by
    dsimp [κ]
    field_simp
    nlinarith
  let β := (κ + 1)⁻¹
  have hβ : 0 < β := inv_pos.mpr (by linarith)
  have hβhalf : β < 1 / 2 := by
    dsimp [β]
    have hh := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) (by linarith : 2 < κ + 1)
    simpa only [one_div] using hh
  refine ⟨1 / 2 - β, (a - κ * p) / 2, by linarith, by linarith, by linarith, ?_⟩
  have he : (1 / 2 - (1 / 2 - β))⁻¹ - 1 = κ := by
    have hb : 1 / 2 - (1 / 2 - β) = β := by ring
    rw [hb]; dsimp [β]; rw [inv_inv]; ring
  rw [he]
  linarith
theorem solution
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ t : ℝ, ∃ ht : 0 < t, ∃ g : ℝ → ℂ, SupportedTest t g ∧
      (∀ τ ∈ quartet ρ, mellinHat g τ.1 = packetValues ρ.1 τ.1) ∧
      (weilDistribution (conv g (starInv g))).re < -(1 / 2) ∧
      ∃ η m : ℝ, 0 < η ∧ η < 1 / 2 ∧ 0 < m ∧
        ∀ T : ℝ, ∀ hT : 0 < T, t ≤ T → SupportedTest T g ∧
          m ≤ ‖(canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
            (sourceEmbed T (problemOneL g))‖ ^ 2 -
            ((1 / 2 - η)⁻¹ - 1) *
              ((weilDistribution (conv g (starInv g))).re +
                ‖(canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
                  (sourceEmbed T (problemOneL g))‖ ^ 2 +
                ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
                  (sourceEmbed T (problemOneL g))‖ ^ 2) := by
  obtain ⟨t, ht, g, hg, hpacket, hneg, _, hW⟩ := canonical_quartet_selected_mellin_witness ρ hoff
  let p := ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2
  let a := ‖(canonicalSelectedSynthesis t ht (quartet ρ)).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2
  have hpa : p < a := by change p - a < 0 at hneg; linarith
  obtain ⟨η, m, hη, hηhalf, hm, hmargin⟩ := scalar_margin p a (sq_nonneg _) hpa
  refine ⟨t, ht, g, hg, hpacket, hW, η, m, hη, hηhalf, hm, ?_⟩
  intro T hT htT
  have hgT := supported_mono hg htT
  refine ⟨hgT, ?_⟩
  rw [restored_positive_energy T hT (quartet ρ) g hgT]
  obtain ⟨hpT, haT⟩ := canonical_actor_test_norms_window_independent t T ht hT (quartet ρ) g hg hgT
  rw [hpT, haT]
  exact hmargin
