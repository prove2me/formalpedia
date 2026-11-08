-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_uniform_prefix_upcross_reserve_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:50:43.172295+00:00
-- url     : https://prove2.me/submissions/3f873c9e-67c1-47da-9c6d-749304859d06

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_path_value_le_of_strict_prefix_le
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_record_grid_clocks_eventually_ge_horizon
import Theorems.Thm_AvramDividend_Classical_avram_f18_original_stopped_postpayment_reserve_upper_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The original upcross localiser bounds both the source and paid reserve on every prefix. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ n) :
    ∃ rhoLoc : ℕ → Ω → ℝ≥0,
      (∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (rhoLoc k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, rhoLoc k ω ≤ ρ ω) ∧
      (∀ k ω (t : ℝ≥0), t ≤ rhoLoc k ω →
        X.X t ω ≤ (k : ℝ) + 1 ∧
        (if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω then
           x + X.X t ω - rightLimit D t ω else riskProcess X x D t ω) ≤
             x + ((k : ℝ) + 1)) ∧
      (∀ ω, ∀ᶠ k : ℕ in atTop, rhoLoc k ω = ρ ω) := by
  classical
  let S : ℕ → Ω → ℝ≥0∞ := fun k ω => twoSidedExitUpTime X ((k : ℝ) + 1) ω
  let rhoLoc : ℕ → Ω → ℝ≥0 :=
    fun k ω => (min (ρ ω : ℝ≥0∞) (S k ω)).toNNReal
  have hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k) := by
    intro k; exact upperPassage_stopping_rightCont_filtration X ((k : ℝ) + 1)
  have hCoe (k : ℕ) (ω : Ω) : (rhoLoc k ω : ℝ≥0∞) =
      min (ρ ω : ℝ≥0∞) (S k ω) := by
    have hle : min (ρ ω : ℝ≥0∞) (S k ω) ≤ (ρ ω : ℝ≥0∞) := min_le_left _ _
    have hfinite : min (ρ ω : ℝ≥0∞) (S k ω) ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
    exact ENNReal.coe_toNNReal hfinite
  have hStop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (rhoLoc k ω : WithTop ℝ≥0)) := by
    intro k
    have hMin : IsStoppingTime 𝓕.rightCont (fun ω => min (ρ ω : WithTop ℝ≥0) (S k ω)) := by
      intro t
      have hset : {ω : Ω | min (ρ ω : WithTop ℝ≥0) (S k ω) ≤ t} =
          {ω : Ω | (ρ ω : WithTop ℝ≥0) ≤ t} ∪ {ω : Ω | S k ω ≤ t} := by
        ext ω; exact (min_le_iff : min (ρ ω : WithTop ℝ≥0) (S k ω) ≤ t ↔
          (ρ ω : WithTop ℝ≥0) ≤ t ∨ S k ω ≤ t)
      rw [hset]; exact (hρstop t).union (hSstop k t)
    have heq : (fun ω => (rhoLoc k ω : WithTop ℝ≥0)) =
        (fun ω => min (ρ ω : WithTop ℝ≥0) (S k ω)) := by
      funext ω; exact hCoe k ω
    rw [heq]; exact hMin
  have hLe (k : ℕ) (ω : Ω) : rhoLoc k ω ≤ ρ ω := by
    apply ENNReal.coe_le_coe.mp; rw [hCoe]; exact min_le_left _ _
  have hPrefix (k : ℕ) (ω : Ω) (t : ℝ≥0)
      (ht : t ≤ rhoLoc k ω) : X.X t ω ≤ (k : ℝ) + 1 := by
    apply path_value_le_of_strict_prefix_le X ((k : ℝ) + 1) (by positivity) ω t
    intro s hs; by_contra hfail
    have hbad : (k : ℝ) + 1 < X.X s ω := lt_of_not_ge hfail
    have hhitle : S k ω ≤ (s : ℝ≥0∞) := by
      dsimp [S, twoSidedExitUpTime]; exact iInf_le_of_le s (iInf_le_of_le hbad le_rfl)
    have hclockle : (rhoLoc k ω : ℝ≥0∞) ≤ S k ω := by rw [hCoe]; exact min_le_right _ _
    have hscoe : (s : ℝ≥0∞) < (rhoLoc k ω : ℝ≥0∞) :=
      ENNReal.coe_lt_coe.mpr (lt_of_lt_of_le hs ht)
    exact (not_lt_of_ge (le_trans hclockle hhitle)) hscoe
  refine ⟨rhoLoc, hStop, hLe, ?_, ?_⟩
  · intro k ω t ht
    exact ⟨hPrefix k ω t ht,
      avram_f18_original_stopped_postpayment_reserve_upper_bound
        X x D hD ω t ((k : ℝ) + 1) (hPrefix k ω t ht)⟩
  · intro ω
    obtain ⟨N, hN⟩ := firstUpcrossing_record_grid_clocks_eventually_ge_horizon
      X ω n 1 1 (by norm_num)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hSge : (n : ℝ≥0∞) ≤ S k ω := by simpa [S, twoSidedExitUpTime, mul_one, add_comm] using hN k hk
    apply ENNReal.coe_injective; rw [hCoe]
    exact min_eq_left (le_trans (ENNReal.coe_le_coe.mpr (hρle ω)) hSge)
