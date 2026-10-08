-- Prove2me | solution 1 for ConnesGreen.canonical_uniform_marker_gap_of_supported_negative_test
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T06:03:52.296856+00:00
-- url     : https://prove2.me/submissions/5a1128d2-3524-4af7-9eb3-862a64b1a88a

import Theorems.Thm_ConnesGreen_actual_physical_test_norm
import Theorems.Thm_ConnesGreen_canonical_actor_test_norms_window_independent
import Theorems.Thm_WeilDefect_MarkerStability_negative_margin_forbids_marker_lower
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open WeilDefect.MarkerStability
private theorem scalar_margin (p b E : ℝ) (hp : 0 ≤ p) (hE : 0 ≤ E) (hd : p < b) :
    ∃ κ : ℝ, 1 < κ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ → κ * (p + ε * E) < b := by
  let d := b - p
  have hd0 : 0 < d := sub_pos.mpr hd
  have hn : 0 < 2 * (p + 1) := by positivity
  let q := d / (2 * (p + 1))
  have hq : 0 < q := div_pos hd0 hn
  have heq : q * (p + 1) = d / 2 := by
    dsimp [q]
    field_simp
  have hqp : q * p < d / 2 := by nlinarith
  let κ := 1 + q
  have hκ : 1 < κ := by dsimp [κ]; linarith
  have hκpos : 0 < κ := by linarith
  have hr : 0 < b - κ * p := by dsimp [κ, d] at *; nlinarith
  have hden : 0 < κ * (E + 1) := by positivity
  refine ⟨κ, hκ, (b - κ * p) / (κ * (E + 1)), div_pos hr hden, ?_⟩
  intro ε hε he
  have hb := (lt_div_iff₀ hden).mp he
  nlinarith

private theorem test_mono {t T : ℝ} {g : ℝ → ℂ}
    (hg : SupportedTest t g) (htT : t ≤ T) : SupportedTest T g := by
  refine ⟨hg.1, ?_⟩
  intro x hx
  obtain ⟨hl, hr⟩ := hg.2 hx
  constructor <;> linarith
theorem solution (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros)
    (g : ℝ → ℂ) (hg : SupportedTest t g)
    (hn : ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 -
      ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 < 0):
    ∃ β δ : ℝ, 0 < β ∧ β < 1 / 2 ∧ 0 < δ ∧
      ∀ T : ℝ, ∀ hT : 0 < T, t ≤ T → ∀ ε : ℝ, 0 < ε → ε < δ →
        ¬ β • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalRegularizedMarker T hT S ε := by
  let p := ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2
  let b := ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2
  let E := (∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) + (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2)
  have hp : 0 ≤ p := sq_nonneg _
  have hE : 0 ≤ E := add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
    (mul_nonneg (by norm_num) (integral_nonneg (fun _ => sq_nonneg _)))
  have hd : p < b := by change p - b < 0 at hn; linarith
  obtain ⟨κ, hκ, δ, hδ, hreserve⟩ := scalar_margin p b E hp hE hd
  have hκpos : 0 < κ := by linarith
  have hβ : 0 < (κ + 1)⁻¹ := inv_pos.mpr (by linarith)
  have hβhalf : (κ + 1)⁻¹ < (1 / 2 : ℝ) := by
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) (by linarith : 2 < κ + 1)
    simpa only [one_div] using h
  refine ⟨(κ + 1)⁻¹, δ, hβ, hβhalf, hδ, ?_⟩
  intro T hT htT ε hε heδ
  have hgT := test_mono hg htT
  obtain ⟨hpT, hbT⟩ := canonical_actor_test_norms_window_independent t T ht hT S g hg hgT
  apply negative_margin_forbids_marker_lower (canonicalPositiveSynthesis T hT)
    (canonicalSelectedSynthesis T hT S) (sourceEmbed T (problemOneL g)) κ ε hκpos hε
  rw [hpT, hbT, actual_physical_test_norm T hT g hgT]
  exact hreserve ε hε heδ
