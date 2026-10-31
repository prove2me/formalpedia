-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_uncapped_reflected_record_discount_semigroup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:13:52.918797+00:00
-- url     : https://prove2.me/submissions/2bf72936-0db8-4b9b-803a-3ec313cf5312

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_uncapped_reflected_killed_future_reward_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_fresh_reflected_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_origin_sampled_reflected_reward_eq_true
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_true_shifted_record_ruin_clock_pair
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_reflected_next_record_future_ruin_iff
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_eq_add_shifted_inf
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_shifted_sampled_reward_true_pair
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_two_record_discount_pathwise
import Theorems.Thm_AvramDividend_Classical_shiftedSup_increment_eq_sup_sub

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b c q : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hq : 0 < q) :
    (∫⁻ ω, if twoSidedExitUpTime X (b + c) ω < barrierRuinTime X a ω then
    ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (b + c) ω).toReal)))
  else 0 ∂P) =
      (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
    ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
  else 0 ∂P) *
      (∫⁻ ω, if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
    ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)))
  else 0 ∂P) := by
  classical
  let samples : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  let reward : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f =>
    let ρ : ℝ≥0∞ := ⨅ i : ℕ,
      if c < f (samples i) - f 0 then (samples i : ℝ≥0∞) else ⊤
    let σ : ℝ≥0∞ := ⨅ i : ℕ,
      if f (samples i) - f 0 -
        (⨆ j : ℕ, if samples j ≤ samples i
          then ENNReal.ofReal (f (samples j) - f 0) else 0).toReal < -a
        then (samples i : ℝ≥0∞) else ⊤
    if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0
  let discount : ℝ≥0 → ℝ≥0∞ := fun t =>
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
  have hr : Measurable reward := by
    simpa only [reward] using
      (avram_wave3_01_fresh_reflected_reward_measurable samples a c q)
  have hd : Measurable discount := by
    dsimp only [discount]
    fun_prop
  have hOrig (ω : Ω) :
      reward (fun t => X.X t ω) =
      (if twoSidedExitUpTime X c ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X c ω).toReal)))
       else 0) := by
    simpa only [reward, samples] using
      (avram_wave3_01_origin_sampled_reflected_reward_eq_true X a c q ω)
  have hDclock (ω : Ω) (u : ℝ≥0) :
      (⨅ i : {t : ℝ≥0 //
        (X.X (u + t) ω - X.X u ω) -
          sSup ((fun r : ℝ≥0 => X.X (u + r) ω - X.X u ω) '' Icc 0 t) < -a},
        (i.1 : ℝ≥0∞)) =
      (⨅ i : {t : ℝ≥0 //
        X.X (u + t) ω -
          sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Icc 0 t) < -a},
        (i.1 : ℝ≥0∞)) := by
    simp only [iInf_subtype]
    apply iInf_congr
    intro t
    have hbd : BddAbove
        ((fun r : ℝ≥0 => X.X (u + r) ω) '' Icc 0 t) := by
      obtain ⟨v, hv⟩ := levyPath_bddAbove_Icc X ω (u + t)
      refine ⟨v, ?_⟩
      rintro z ⟨r, hr, rfl⟩
      apply hv
      exact ⟨u + r, ⟨zero_le, by
        calc
          u + r = r + u := add_comm u r
          _ ≤ t + u := add_le_add_left hr.2 u
          _ = u + t := add_comm t u⟩, rfl⟩
    have hx := shiftedSup_increment_eq_sup_sub
      (fun r => X.X r ω) u t hbd
    simp only [hx]
    have heq :
        ((X.X (u + t) ω - X.X u ω) -
          (sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Icc 0 t) -
            X.X u ω) < -a) ↔
        (X.X (u + t) ω -
          sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Icc 0 t) < -a) := by
      constructor <;> intro h <;> linarith
    simp only [heq]
  have hFuture (ω : Ω) (u : ℝ≥0) :
      reward (fun t => X.X (u + t) ω - X.X u ω) =
      (let U : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 //
         c < X.X (u + t) ω - X.X u ω}, (i.1 : ℝ≥0∞)
       let D : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 //
         X.X (u + t) ω -
           sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Icc 0 t) < -a},
         (i.1 : ℝ≥0∞)
       if U < D then ENNReal.ofReal (Real.exp (-(q * U.toReal))) else 0) := by
    have hh := avram_wave3_01_shifted_sampled_reward_true_pair X a c q ω u
    simpa [reward, samples, hDclock ω u] using hh
  have hPath (ω : Ω) :
      (if twoSidedExitUpTime X (b + c) ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp
          (-(q * (twoSidedExitUpTime X (b + c) ω).toReal))) else 0) =
      (if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
        discount ((twoSidedExitUpTime X b ω).toNNReal) *
          reward (fun t => X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
            X.X ((twoSidedExitUpTime X b ω).toNNReal) ω)
       else 0) := by
    have hh := avram_wave3_01_two_record_discount_pathwise
      X a b c q ha hb hc ω
    simpa only [discount, ← hFuture] using hh
  have hFactor :=
    avram_wave3_01_uncapped_reflected_killed_future_reward_factor
      X a b discount hd reward hr
  dsimp only at hFactor
  calc
    _ = (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
          discount ((twoSidedExitUpTime X b ω).toNNReal) *
            reward (fun t => X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
              X.X ((twoSidedExitUpTime X b ω).toNNReal) ω)
          else 0 ∂P) := lintegral_congr hPath
    _ = (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
          discount ((twoSidedExitUpTime X b ω).toNNReal) else 0 ∂P) *
        (∫⁻ ω, reward (fun t => X.X t ω) ∂P) := hFactor
    _ = _ := by
      refine congrArg₂ (· * ·) ?_ ?_
      · apply lintegral_congr
        intro ω
        exact congrArg (fun z : ℝ≥0∞ =>
          if twoSidedExitUpTime X b ω < barrierRuinTime X a ω
          then z else 0) (by simp only [discount, ENNReal.coe_toNNReal_eq_toReal])
      · exact lintegral_congr hOrig
