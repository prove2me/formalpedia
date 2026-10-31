-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_reflected_record_factor_continuous_depth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T17:32:16.755143+00:00
-- url     : https://prove2.me/submissions/4574441c-ce8f-4fbb-bfe9-03f78767f9c0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_first_record_height_atomless
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_before_barrierRuin_iff_prefix_survival
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology Filter
open scoped NNReal ENNReal

/-- Continuous genuine discounted reflected-record survival under infinite variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b q : ℝ) (hb : 0 ≤ b) (hq : 0 < q)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a c : ℝ≥0, a < c →
      ∃ m : ℕ, a < times m ∧ times m < c)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ContinuousOn (fun a : ℝ =>
      ∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P) (Ioi 0) := by
  intro a ha
  have ha0 : 0 < a := ha
  let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
  let w : Ω → ℝ≥0∞ :=
    fun ω => ENNReal.ofReal (Real.exp (-(q * (T ω).toReal)))
  let F : ℝ → Ω → ℝ≥0∞ :=
    fun c ω => if T ω < barrierRuinTime X c ω then w ω else 0
  have hmeas (c : ℝ) : Measurable (F c) := by
    simpa only [F, T, w, one_mul] using
      (killed_firstRecord_discount_reward_measurable X c b 1 q)
  have hwbound (ω : Ω) : w ω ≤ 1 := by
    have ht : 0 ≤ (T ω).toReal := ENNReal.toReal_nonneg
    have hqt : 0 ≤ q * (T ω).toReal := mul_nonneg hq.le ht
    have he : Real.exp (-(q * (T ω).toReal)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr hqt)
    simpa only [w, ENNReal.ofReal_one] using
      (ENNReal.ofReal_le_ofReal he)
  have hbound (c : ℝ) : ∀ᵐ ω ∂P, F c ω ≤ 1 := by
    filter_upwards [] with ω
    dsimp [F]
    split_ifs <;> simp [hwbound]
  letI : IsProbabilityMeasure P := X.isProbability
  have hfin : ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂P ≠ ⊤ := by simp
  have hnull : P {ω : Ω | ∃ u : ℝ≥0,
      (u : ℝ≥0∞) = T ω ∧
      sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 u) = a} = 0 := by
    exact avram_wave3_01_first_record_height_atomless X b hb
      ⟨a, ha0.le⟩ ha0 times horizons hdense hpos hcofinal hjump
  have hae : ∀ᵐ ω ∂P, ¬ ∃ u : ℝ≥0,
      (u : ℝ≥0∞) = T ω ∧
      sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 u) = a := by
    exact ae_iff.mpr (by simpa only [not_not] using hnull)
  have hlim : ∀ᵐ ω ∂P,
      Tendsto (fun c : ℝ => F c ω) (nhds a) (nhds (F a ω)) := by
    filter_upwards [hae] with ω hnot
    by_cases hTop : T ω = ⊤
    · have hnever (c : ℝ) : ¬ T ω < barrierRuinTime X c ω := by
        rw [hTop]
        exact not_top_lt
      have heq : (fun c : ℝ => F c ω) = fun _ => (0 : ℝ≥0∞) := by
        funext c
        simp [F, hnever]
      simp [heq, F, hnever]
    · let u : ℝ≥0 := (T ω).toNNReal
      have hu : (u : ℝ≥0∞) = T ω := ENNReal.coe_toNNReal hTop
      let H : ℝ := sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 u)
      have hne : H ≠ a := by
        intro heq
        exact hnot ⟨u, hu, heq⟩
      have hsurv (c : ℝ) (hc : 0 < c) :
          (T ω < barrierRuinTime X c ω ↔ H ≤ c) := by
        have hp := firstUpcrossing_before_barrierRuin_iff_prefix_survival
          X c b hc hb ω u (by simpa only [T, twoSidedExitUpTime] using hu)
        have hUSC := reflectedSup_upperSemicontinuousOn_Icc X ω u
        have hIcc : (Icc (0 : ℝ≥0) u).Nonempty := ⟨0, by simp⟩
        obtain ⟨v, hv, hmax⟩ :=
          UpperSemicontinuousOn.exists_isMaxOn hIcc isCompact_Icc hUSC
        have hBdd : BddAbove
            ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 u) := by
          refine ⟨reflectedSup X v ω, ?_⟩
          rintro y ⟨t, ht, rfl⟩
          exact hmax ht
        have hNonempty : ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 u).Nonempty :=
          ⟨reflectedSup X 0 ω, ⟨0, by simp, rfl⟩⟩
        have hzero : reflectedSup X u ω = 0 :=
          firstUpcrossing_runningSup_sub_path_eq_zero X b hb ω u
            (by simpa only [T, twoSidedExitUpTime] using hu)
        rw [← hu]
        change (u : ℝ≥0∞) < barrierRuinTime X c ω ↔
          sSup ((fun t : ℝ≥0 => reflectedSup X t ω) '' Icc 0 u) ≤ c
        constructor
        · intro hs
          apply csSup_le hNonempty
          rintro y ⟨t, ht, rfl⟩
          by_cases htu : t < u
          · exact hp.mp hs t htu
          · have heq : t = u := le_antisymm ht.2 (le_of_not_gt htu)
            subst t
            change reflectedSup X u ω ≤ c
            rw [hzero]; exact hc.le
        · intro hs
          apply hp.mpr
          intro t ht
          apply le_trans (le_csSup hBdd ?_) hs
          exact ⟨t, ⟨zero_le, le_of_lt ht⟩, rfl⟩
      by_cases hlt : H < a
      · have hevent : ∀ᶠ c in nhds a, 0 < c ∧ H < c :=
          (eventually_gt_nhds ha0).and (eventually_gt_nhds hlt)
        have heq : (fun c : ℝ => F c ω) =ᶠ[nhds a] fun _ => w ω := by
          filter_upwards [hevent] with c ⟨hc, hHc⟩
          simp [F, (hsurv c hc).mpr hHc.le]
        have hnow : F a ω = w ω := by
          simp [F, (hsurv a ha0).mpr hlt.le]
        rw [hnow]
        exact tendsto_const_nhds.congr' heq.symm
      · have hgt : a < H := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
        have hevent : ∀ᶠ c in nhds a, 0 < c ∧ c < H :=
          (eventually_gt_nhds ha0).and (eventually_lt_nhds hgt)
        have heq : (fun c : ℝ => F c ω) =ᶠ[nhds a] fun _ => 0 := by
          filter_upwards [hevent] with c ⟨hc, hcH⟩
          simp [F, not_le.mpr hcH, (hsurv c hc).not]
        have hnow : F a ω = 0 := by
          simp [F, not_le.mpr hgt, (hsurv a ha0).not]
        rw [hnow]
        exact tendsto_const_nhds.congr' heq.symm
  have hcont : ContinuousAt (fun c : ℝ => ∫⁻ ω, F c ω ∂P) a :=
    tendsto_lintegral_filter_of_dominated_convergence
      (fun _ : Ω => (1 : ℝ≥0∞))
      (Filter.Eventually.of_forall hmeas)
      (Filter.Eventually.of_forall hbound) hfin hlim
  exact hcont.continuousWithinAt
