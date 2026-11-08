-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_any_clock_upcross_localisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:11:56.422523+00:00
-- url     : https://prove2.me/submissions/e2d8048d-d35b-4fe3-97b1-fcb7481969c6

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_path_value_le_of_strict_prefix_le
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_record_grid_clocks_eventually_ge_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Source-exact upward-exit stopping clocks for a bounded arbitrary original clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ n) :
    ∃ rhoLoc : ℕ → Ω → ℝ≥0,
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (rhoLoc k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, rhoLoc k ω ≤ ρ ω) ∧
      (∀ k ω, X.X (rhoLoc k ω) ω ≤ (k : ℝ) + 1) ∧
      (∀ ω, ∀ᶠ k : ℕ in atTop, rhoLoc k ω = ρ ω) := by
  classical
  let S : ℕ → Ω → ℝ≥0∞ :=
    fun k ω => twoSidedExitUpTime X ((k : ℝ) + 1) ω
  let rhoLoc : ℕ → Ω → ℝ≥0 :=
    fun k ω => (min (ρ ω : ℝ≥0∞) (S k ω)).toNNReal
  have hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k) := by
    intro k
    exact upperPassage_stopping_rightCont_filtration X ((k : ℝ) + 1)
  have hCoe (k : ℕ) (ω : Ω) :
      (rhoLoc k ω : ℝ≥0∞) = min (ρ ω : ℝ≥0∞) (S k ω) := by
    have hle : min (ρ ω : ℝ≥0∞) (S k ω) ≤ (ρ ω : ℝ≥0∞) := min_le_left _ _
    have hfinite : min (ρ ω : ℝ≥0∞) (S k ω) ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
    exact ENNReal.coe_toNNReal hfinite
  have hStop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (rhoLoc k ω : WithTop ℝ≥0)) := by
    intro k
    have hMin : IsStoppingTime 𝓕.rightCont (fun ω => min (ρ ω : WithTop ℝ≥0) (S k ω)) := by
      intro t
      have hset : {ω : Ω | min (ρ ω : WithTop ℝ≥0) (S k ω) ≤ (t : WithTop ℝ≥0)} =
          {ω : Ω | (ρ ω : WithTop ℝ≥0) ≤ t} ∪ {ω : Ω | S k ω ≤ t} := by
        ext ω
        exact (min_le_iff : min (ρ ω : WithTop ℝ≥0) (S k ω) ≤ (t : WithTop ℝ≥0) ↔
          (ρ ω : WithTop ℝ≥0) ≤ t ∨ S k ω ≤ t)
      rw [hset]; exact (hρstop t).union (hSstop k t)
    have heq : (fun ω => (rhoLoc k ω : WithTop ℝ≥0)) = (fun ω => min (ρ ω : WithTop ℝ≥0) (S k ω)) := by
      funext ω; exact hCoe k ω
    rw [heq]
    exact hMin
  have hLe (k : ℕ) (ω : Ω) : rhoLoc k ω ≤ ρ ω := by
    apply ENNReal.coe_le_coe.mp
    rw [hCoe]; exact min_le_left _ _
  have hBound (k : ℕ) (ω : Ω) : X.X (rhoLoc k ω) ω ≤ (k : ℝ) + 1 := by
    apply path_value_le_of_strict_prefix_le X ((k : ℝ) + 1)
      (by positivity) ω (rhoLoc k ω)
    intro t ht
    by_contra hfail
    have hbad : (k : ℝ) + 1 < X.X t ω := lt_of_not_ge hfail
    have hhitle : S k ω ≤ (t : ℝ≥0∞) := by
      dsimp [S, twoSidedExitUpTime]
      exact iInf_le_of_le t (iInf_le_of_le hbad le_rfl)
    have hclockle : (rhoLoc k ω : ℝ≥0∞) ≤ S k ω := by
      rw [hCoe]; exact min_le_right _ _
    have htcoe : (t : ℝ≥0∞) < (rhoLoc k ω : ℝ≥0∞) :=
      ENNReal.coe_lt_coe.mpr ht
    exact (not_lt_of_ge (le_trans hclockle hhitle)) htcoe
  refine ⟨rhoLoc, hStop, hLe, hBound, ?_⟩
  intro ω
  obtain ⟨N, hN⟩ :=
    firstUpcrossing_record_grid_clocks_eventually_ge_horizon X ω n 1 1 (by norm_num)
  filter_upwards [eventually_ge_atTop N] with k hk
  have hSge : (n : ℝ≥0∞) ≤ S k ω := by
    have h := hN k hk
    simpa [S, twoSidedExitUpTime, mul_one, add_comm] using h
  apply ENNReal.coe_injective
  rw [hCoe]
  exact min_eq_left (le_trans (ENNReal.coe_le_coe.mpr (hρle ω)) hSge)
