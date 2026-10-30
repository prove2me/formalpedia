-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_uncapped_barrier_killed_future_reward_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:57:04.18293+00:00
-- url     : https://prove2.me/submissions/5e6ab016-1f8f-4238-8544-a71a67214917

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_capped_barrier_killed_future_reward_factor
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The true killed first-upcrossing prefix factors from an arbitrary measurable future Lévy path reward, with no artificial finite time cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hx : 0 ≤ x) (ha : 0 < a) (hxa : x ≤ a)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    let T := twoSidedExitUpTime X (a - x)
    let R := ruinTime X x (barrierStrategy X x a)
    (∫⁻ ω, if T ω < R ω then
      discount ((T ω).toNNReal) * reward (fun t : ℝ≥0 =>
          X.X ((T ω).toNNReal + t) ω - X.X ((T ω).toNNReal) ω) else 0 ∂P) =
      (∫⁻ ω, if T ω < R ω then discount ((T ω).toNNReal) else 0 ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
  classical
  let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X (a - x)
  let R : Ω → ℝ≥0∞ := ruinTime X x (barrierStrategy X x a)
  let A (n : ℕ) : Set Ω := {ω | T ω < R ω ∧ T ω ≤ (n : ℝ≥0∞)}
  let τ (n : ℕ) (ω : Ω) : ℝ≥0 := (min (T ω) (n : ℝ≥0∞)).toNNReal
  let F (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
    if ω ∈ A n then discount (τ n ω) * reward (fun t : ℝ≥0 => X.X (τ n ω + t) ω - X.X (τ n ω) ω) else 0
  let G (n : ℕ) (ω : Ω) : ℝ≥0∞ := if ω ∈ A n then discount (τ n ω) else 0
  have hTstop : IsStoppingTime 𝓕.rightCont T := upperPassage_stopping_rightCont_filtration X (a - x)
  have hD : IsDividendStrategy 𝓕 (barrierStrategy X x a) := barrierStrategy_isDividendStrategy_nonnegative_barrier X x a hx ha.le
  have hRstop : IsStoppingTime 𝓕.rightCont R := ruinTime_stopping_rightCont_filtration X x _ hD
  have hTm : Measurable T := hTstop.measurable.mono hTstop.measurableSpace_le le_rfl
  have hRm : Measurable R := hRstop.measurable.mono hRstop.measurableSpace_le le_rfl
  have hAm (n : ℕ) : MeasurableSet (A n) := (measurableSet_lt hTm hRm).inter (measurableSet_le hTm measurable_const)
  have hτm (n : ℕ) : Measurable (τ n) := ENNReal.measurable_toNNReal.comp (hTm.min measurable_const)
  have hFm (n : ℕ) : Measurable (F n) := by
    have hp := avram_ws01e_b_randomAge_whole_shiftedPath_measurable X (τ n) (hτm n)
    exact Measurable.ite (hAm n) ((hd.comp (hτm n)).mul (hr.comp hp)) measurable_const
  have hGm (n : ℕ) : Measurable (G n) := Measurable.ite (hAm n) (hd.comp (hτm n)) measurable_const
  have hτeq (n : ℕ) (ω : Ω) (hn : ω ∈ A n) : τ n ω = (T ω).toNNReal := by
    change (min (T ω) (n : ℝ≥0∞)).toNNReal = _
    rw [min_eq_left hn.2]
  have hAmono (n m : ℕ) (hnm : n ≤ m) (ω : Ω) (hn : ω ∈ A n) : ω ∈ A m := by
    refine ⟨hn.1, le_trans hn.2 ?_⟩
    exact_mod_cast hnm
  have hFmono : Monotone F := by
    intro n m hnm ω
    by_cases hn : ω ∈ A n
    · have hm := hAmono n m hnm ω hn
      simp only [F, if_pos hn, if_pos hm, hτeq n ω hn, hτeq m ω hm, le_refl]
    · simp only [F, if_neg hn]
      exact bot_le
  have hGmono : Monotone G := by
    intro n m hnm ω
    by_cases hn : ω ∈ A n
    · have hm := hAmono n m hnm ω hn
      simp only [G, if_pos hn, if_pos hm, hτeq n ω hn, hτeq m ω hm, le_refl]
    · simp only [G, if_neg hn]
      exact bot_le
  have hEvent (ω : Ω) (h : T ω < R ω) :
      ∃ n : ℕ, ω ∈ A n := by
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_lt (lt_of_lt_of_le h le_top))
    exact ⟨n, h, le_of_lt hn⟩
  have hFsup (ω : Ω) :
      (⨆ n : ℕ, F n ω) = (if T ω < R ω then discount ((T ω).toNNReal) *
        reward (fun t : ℝ≥0 => X.X ((T ω).toNNReal + t) ω - X.X ((T ω).toNNReal) ω)
        else 0) := by
    by_cases h : T ω < R ω
    · obtain ⟨n, hn⟩ := hEvent ω h
      rw [if_pos h]
      apply le_antisymm
      · apply iSup_le
        intro k
        by_cases hk : ω ∈ A k
        · simp only [F, if_pos hk, hτeq k ω hk, le_refl]
        · simp only [F, if_neg hk]
          exact bot_le
      · exact le_iSup_of_le n (by simp only [F, if_pos hn, hτeq n ω hn, le_refl])
    · rw [if_neg h]
      have hn (n : ℕ) : ω ∉ A n := fun hh => h hh.1
      simp [F, hn]
  have hGsup (ω : Ω) : (⨆ n : ℕ, G n ω) = (if T ω < R ω then discount ((T ω).toNNReal) else 0) := by
    by_cases h : T ω < R ω
    · obtain ⟨n, hn⟩ := hEvent ω h
      rw [if_pos h]
      apply le_antisymm
      · apply iSup_le
        intro k
        by_cases hk : ω ∈ A k
        · simp only [G, if_pos hk, hτeq k ω hk, le_refl]
        · simp only [G, if_neg hk]
          exact bot_le
      · exact le_iSup_of_le n (by simp only [G, if_pos hn, hτeq n ω hn, le_refl])
    · rw [if_neg h]
      have hn (n : ℕ) : ω ∉ A n := fun hh => h hh.1
      simp [G, hn]
  have hEach (n : ℕ) : (∫⁻ ω, F n ω ∂P) = (∫⁻ ω, G n ω ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
    simpa only [F, G, A, τ, T, R, Set.mem_setOf_eq, ENNReal.coe_natCast] using
      (avram_root29_05_capped_barrier_killed_future_reward_factor X x a hx ha hxa (n : ℝ≥0) discount hd reward hr)
  change (∫⁻ ω, if T ω < R ω then discount ((T ω).toNNReal) * reward (fun t : ℝ≥0 => X.X ((T ω).toNNReal + t) ω - X.X ((T ω).toNNReal) ω)
      else 0 ∂P) =
    (∫⁻ ω, if T ω < R ω then discount ((T ω).toNNReal) else 0 ∂P) *
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P)
  calc
    _ = (∫⁻ ω, ⨆ n, F n ω ∂P) :=
      lintegral_congr (fun ω => (hFsup ω).symm)
    _ = ⨆ n, (∫⁻ ω, F n ω ∂P) := lintegral_iSup hFm hFmono
    _ = ⨆ n, (∫⁻ ω, G n ω ∂P) * (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
          congr 1; funext n; exact hEach n
    _ = (⨆ n, (∫⁻ ω, G n ω ∂P)) * (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
          rw [ENNReal.iSup_mul]
    _ = (∫⁻ ω, ⨆ n, G n ω ∂P) * (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
          rw [lintegral_iSup hGm hGmono]
    _ = _ := by
      congr 1
      exact lintegral_congr hGsup
