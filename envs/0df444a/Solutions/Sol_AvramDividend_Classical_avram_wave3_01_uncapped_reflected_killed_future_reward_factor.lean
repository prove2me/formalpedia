-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_uncapped_reflected_killed_future_reward_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:25:11.58296+00:00
-- url     : https://prove2.me/submissions/43bd6163-c038-4aac-b16e-5aa1187c11ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_killedDiscount_futureReward_factor_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_stopping_rightCont
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_in_finiteStoppedHistory
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_survival_measurable_global
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- At an uncapped original strict first record surviving actual reflected
    drawdown ruin, the complete future Lévy reward factors from past discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a b : ℝ)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    (let T := twoSidedExitUpTime X b
     let R := barrierRuinTime X a
     (∫⁻ ω, if T ω < R ω then discount ((T ω).toNNReal) *
       reward (fun t : ℝ≥0 => X.X ((T ω).toNNReal + t) ω -
         X.X ((T ω).toNNReal) ω) else 0 ∂P) =
     (∫⁻ ω, if T ω < R ω then discount ((T ω).toNNReal) else 0 ∂P) *
     (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P)) := by
  classical
  let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
  let R : Ω → ℝ≥0∞ := barrierRuinTime X a
  let A (n : ℕ) : Set Ω := {ω | T ω < R ω} ∩ {ω | T ω ≤ (n : ℝ≥0∞)}
  let τ (n : ℕ) (ω : Ω) : ℝ≥0 :=
    (min (T ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal
  let F (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
    @ite ℝ≥0∞ (ω ∈ A n) (Classical.propDecidable _) (discount (τ n ω) *
      reward (fun t : ℝ≥0 => X.X (τ n ω + t) ω - X.X (τ n ω) ω)) 0
  let G (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
    @ite ℝ≥0∞ (ω ∈ A n) (Classical.propDecidable _) (discount (τ n ω)) 0
  have hAm (n : ℕ) : MeasurableSet (A n) := by
    simpa only [A, T, R, Set.mem_setOf_eq, ENNReal.coe_natCast] using (firstRecord_capped_survival_measurable_global X a b (n : ℝ≥0))
  have hτm (n : ℕ) : Measurable (τ n) := by
    simpa only [τ, T, ENNReal.coe_natCast] using (firstRecord_truncation_clock_measurable X b (n : ℝ≥0))
  have hFm (n : ℕ) : Measurable (F n) := by
    have hp := avram_ws01e_b_randomAge_whole_shiftedPath_measurable X (τ n) (hτm n)
    exact Measurable.ite (hAm n) ((hd.comp (hτm n)).mul (hr.comp hp)) measurable_const
  have hGm (n : ℕ) : Measurable (G n) :=
    Measurable.ite (hAm n) (hd.comp (hτm n)) measurable_const
  have hτeq (n : ℕ) (ω : Ω) (hn : ω ∈ A n) : τ n ω = (T ω).toNNReal := by
    change T ω < R ω ∧ T ω ≤ (n : ℝ≥0∞) at hn
    change (min (T ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal = _
    rw [min_eq_left (by simpa only [ENNReal.coe_natCast] using hn.2)]
  have hAmono (n m : ℕ) (hnm : n ≤ m) (ω : Ω) (hn : ω ∈ A n) : ω ∈ A m := by
    change T ω < R ω ∧ T ω ≤ (n : ℝ≥0∞) at hn
    change T ω < R ω ∧ T ω ≤ (m : ℝ≥0∞)
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
    obtain ⟨n, hn⟩ :=
      ENNReal.exists_nat_gt (ne_top_of_lt (lt_of_lt_of_le h le_top))
    exact ⟨n, h, le_of_lt hn⟩
  have hFsup (ω : Ω) : (⨆ n : ℕ, F n ω) =
      (if T ω < R ω then discount ((T ω).toNNReal) *
        reward (fun t : ℝ≥0 => X.X ((T ω).toNNReal + t) ω -
          X.X ((T ω).toNNReal) ω) else 0) := by
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
      · exact le_iSup_of_le n
          (by simp only [F, if_pos hn, hτeq n ω hn, le_refl])
    · rw [if_neg h]
      have hn (n : ℕ) : ω ∉ A n := fun hh => h hh.1
      simp [F, hn]
  have hGsup (ω : Ω) : (⨆ n : ℕ, G n ω) =
      (if T ω < R ω then discount ((T ω).toNNReal) else 0) := by
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
      · exact le_iSup_of_le n
          (by simp only [G, if_pos hn, hτeq n ω hn, le_refl])
    · rw [if_neg h]
      have hn (n : ℕ) : ω ∉ A n := fun hh => h hh.1
      simp [G, hn]
  have hEach (n : ℕ) : (∫⁻ ω, F n ω ∂P) =
      (∫⁻ ω, G n ω ∂P) *
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
    have hStop := firstRecord_truncation_stopping_rightCont X b (n : ℝ≥0)
    have hStopped : MeasurableSet[(isStoppingTime_withTop_of_le_events (τ n)
          (by simpa only [τ, T, ENNReal.coe_natCast] using hStop)).measurableSpace]
          (A n) := by
      simpa only [A, τ, T, R, Set.mem_setOf_eq, Set.mem_inter_iff,
        ENNReal.coe_natCast] using
        (firstRecord_capped_survival_in_finiteStoppedHistory X a b (n : ℝ≥0))
    simpa only [F, G] using
      (levy_finiteStopping_killedDiscount_futureReward_factor_rightCont
        X (τ n) (by simpa only [τ, T, ENNReal.coe_natCast] using hStop)
        (A n) hStopped (hAm n) (hτm n) discount hd reward hr)
  change (∫⁻ ω, if T ω < R ω then discount ((T ω).toNNReal) *
    reward (fun t : ℝ≥0 => X.X ((T ω).toNNReal + t) ω -
      X.X ((T ω).toNNReal) ω) else 0 ∂P) =
    (∫⁻ ω, if T ω < R ω then discount ((T ω).toNNReal) else 0 ∂P) *
    (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P)
  calc
    _ = (∫⁻ ω, ⨆ n, F n ω ∂P) :=
      lintegral_congr (fun ω => (hFsup ω).symm)
    _ = ⨆ n, (∫⁻ ω, F n ω ∂P) := lintegral_iSup hFm hFmono
    _ = ⨆ n, (∫⁻ ω, G n ω ∂P) *
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
        congr 1
        funext n
        exact hEach n
    _ = (⨆ n, (∫⁻ ω, G n ω ∂P)) *
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
        rw [ENNReal.iSup_mul]
    _ = (∫⁻ ω, ⨆ n, G n ω ∂P) *
      (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
        rw [lintegral_iSup hGm hGmono]
    _ = _ := by
      congr 1; exact lintegral_congr hGsup
