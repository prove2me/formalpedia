-- Prove2me | solution 1 for AvramDividend.Classical.levy_true_terminal_esscher_exp_clock_first_passage_mass_ws01d
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:15:34.60914+00:00
-- url     : https://prove2.me/submissions/92a1d67e-6621-4d4f-97e2-64ddd636f9bf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_levy_capped_first_record_true_terminal_esscher_exp_clock_mass_ws01d
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
/-- Uncapped first-passage mass for the genuine random-terminal Esscher likelihood
and the independent real exponential clock, with its non-strict boundary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b)
    (p : ℝ) (hp : 0 < p)
    (phi q : ℝ) (hphi : 0 ≤ phi) (hroot : X.ψ phi = q) :
    (∫⁻ z : Ω × ℝ,
      if twoSidedExitUpTime X b z.1 < (⊤ : ℝ≥0∞) ∧
        ((twoSidedExitUpTime X b z.1).toNNReal : ℝ) ≤ z.2 then
        ENNReal.ofReal (Real.exp
          (phi * X.X z.2.toNNReal z.1 - (z.2.toNNReal : ℝ) * q))
      else 0 ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    (∫⁻ ω : Ω, if twoSidedExitUpTime X b ω < (⊤ : ℝ≥0∞) then
      ENNReal.ofReal (Real.exp
        (phi * b - (p + q) * (twoSidedExitUpTime X b ω).toReal))
      else 0 ∂P) := by
  let T : Ω → ℝ≥0∞ := fun ω => twoSidedExitUpTime X b ω
  let age (n : ℕ) (ω : Ω) : ℝ≥0 := (min (T ω) (n : ℝ≥0∞)).toNNReal
  let A (n : ℕ) : Set Ω := {ω | T ω < (n : ℝ≥0∞)}
  let B (n : ℕ) : Set (Ω × ℝ) :=
    {z | z.1 ∈ A n ∧ (age n z.1 : ℝ) ≤ z.2}
  let L : Ω × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (phi * X.X z.2.toNNReal z.1 - (z.2.toNNReal : ℝ) * q))
  let F (n : ℕ) (z : Ω × ℝ) : ℝ≥0∞ := if z ∈ B n then L z else 0
  let G (n : ℕ) (ω : Ω) : ℝ≥0∞ := if ω ∈ A n then
    ENNReal.ofReal (Real.exp (phi * b - (p + q) * (age n ω : ℝ))) else 0
  have hT : Measurable T := chat08_upper_passage_clock_measurable X b
  have hAge (n : ℕ) : Measurable (age n) := firstRecord_truncation_clock_measurable X b (n : ℝ≥0)
  have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_lt hT measurable_const
  have hB (n : ℕ) : MeasurableSet (B n) := by
    dsimp [B]; exact (hA n).preimage measurable_fst |>.inter
      (measurableSet_le ((hAge n).coe_nnreal_real.comp measurable_fst) measurable_snd)
  have hX : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) := chat04_levy_joint_time_state_measurable X
  have ht : Measurable (fun z : Ω × ℝ => z.2.toNNReal) := measurable_real_toNNReal.comp measurable_snd
  have hL : Measurable L := by
    dsimp [L]; exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul (hX.comp (ht.prodMk measurable_fst))).sub
          (ht.coe_nnreal_real.mul measurable_const)))
  have hF (n : ℕ) : Measurable (F n) := hL.ite (hB n) measurable_const
  have hG (n : ℕ) : Measurable (G n) := by
    dsimp [G]
    exact (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        (measurable_const.sub (measurable_const.mul (hAge n).coe_nnreal_real)))).ite (hA n) measurable_const
  have hBsub : Monotone B := by
    intro n m hnm z hz
    have han : T z.1 < (n : ℝ≥0∞) := hz.1
    have ham : T z.1 < (m : ℝ≥0∞) := lt_of_lt_of_le han (by exact_mod_cast hnm)
    refine ⟨ham, ?_⟩
    simpa only [age, min_eq_left (le_of_lt han), min_eq_left (le_of_lt ham)]
      using hz.2
  have hFmono : Monotone F := by
    intro n m hnm z
    by_cases hz : z ∈ B n
    · have hm := hBsub hnm hz
      simp [F, hz, hm]
    · simp only [F, if_neg hz]; exact bot_le
  have hGmono : Monotone G := by
    intro n m hnm ω
    by_cases hn : ω ∈ A n
    · have htn : T ω < (n : ℝ≥0∞) := hn
      have hm : ω ∈ A m := (show T ω < (m : ℝ≥0∞) from lt_of_lt_of_le htn (by exact_mod_cast hnm))
      have htm : T ω < (m : ℝ≥0∞) := hm
      have hh : age n ω = age m ω := by
        simp only [age, min_eq_left (le_of_lt htn), min_eq_left (le_of_lt htm)]
      simp only [G, if_pos hn, if_pos hm, hh, le_refl]
    · simp only [G, if_neg hn]; exact bot_le
  have hFsup (z : Ω × ℝ) :
      (⨆ n : ℕ, F n z) =
      (if T z.1 < (⊤ : ℝ≥0∞) ∧ ((T z.1).toNNReal : ℝ) ≤ z.2
        then L z else 0) := by
    by_cases h : T z.1 < (⊤ : ℝ≥0∞) ∧ ((T z.1).toNNReal : ℝ) ≤ z.2
    · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_lt h.1)
      have hz : z ∈ B n := by
        refine ⟨hn, ?_⟩
        simpa only [age, min_eq_left (le_of_lt hn)] using h.2
      rw [if_pos h]
      apply le_antisymm
      · exact iSup_le (fun n => by by_cases ht : z ∈ B n <;> simp [F, ht])
      · exact le_iSup_of_le n (by simp [F, hz])
    · rw [if_neg h]
      have hn (n : ℕ) : z ∉ B n := by
        intro hz
        have hfin : T z.1 < (⊤ : ℝ≥0∞) := lt_of_lt_of_le hz.1 le_top
        have htime : ((T z.1).toNNReal : ℝ) ≤ z.2 := by
          have han : T z.1 < (n : ℝ≥0∞) := hz.1
          simpa only [age, min_eq_left (le_of_lt han)] using hz.2
        exact h ⟨hfin, htime⟩
      simp [F, hn]
  have hGsup (ω : Ω) :
      (⨆ n : ℕ, G n ω) =
      (if T ω < (⊤ : ℝ≥0∞) then
        ENNReal.ofReal (Real.exp (phi * b - (p + q) * (T ω).toReal))
        else 0) := by
    by_cases h : T ω < (⊤ : ℝ≥0∞)
    · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_lt h)
      rw [if_pos h]; apply le_antisymm
      · apply iSup_le
        intro k
        by_cases hk : ω ∈ A k
        · have heq : age k ω = (T ω).toNNReal := by
            have htk : T ω < (k : ℝ≥0∞) := hk
            simp only [age, min_eq_left (le_of_lt htk)]
          simp only [G, if_pos hk, heq, ENNReal.toReal, le_refl]
        · simp only [G, if_neg hk]; exact bot_le
      · apply le_iSup_of_le n
        have hAn : ω ∈ A n := hn
        simp only [G, if_pos hAn, age, min_eq_left (le_of_lt hn), ENNReal.toReal, le_refl]
    · have hn (n : ℕ) : ω ∉ A n := by
        intro hh; exact h (lt_of_lt_of_le hh le_top)
      simp [h, G, hn]
  have hEach (n : ℕ) :
      (∫⁻ z : Ω × ℝ, F n z ∂(P.prod (ProbabilityTheory.expMeasure p))) =
      (∫⁻ ω : Ω, G n ω ∂P) := by
    simpa only [F, G, L, B, A, age, T, Set.mem_setOf_eq, ENNReal.coe_natCast] using
      (levy_capped_first_record_true_terminal_esscher_exp_clock_mass_ws01d
        X b hb (n : ℝ≥0) p hp phi q hphi hroot)
  change (∫⁻ z : Ω × ℝ,
      if T z.1 < (⊤ : ℝ≥0∞) ∧ ((T z.1).toNNReal : ℝ) ≤ z.2
      then L z else 0 ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    (∫⁻ ω : Ω, if T ω < (⊤ : ℝ≥0∞) then
      ENNReal.ofReal (Real.exp (phi * b - (p + q) * (T ω).toReal))
      else 0 ∂P)
  calc
    _ = (∫⁻ z : Ω × ℝ, ⨆ n, F n z
        ∂(P.prod (ProbabilityTheory.expMeasure p))) :=
      lintegral_congr (fun z => (hFsup z).symm)
    _ = ⨆ n, (∫⁻ z : Ω × ℝ, F n z
        ∂(P.prod (ProbabilityTheory.expMeasure p))) :=
      lintegral_iSup hF hFmono
    _ = ⨆ n, (∫⁻ ω : Ω, G n ω ∂P) := by congr 1; funext n; exact hEach n
    _ = (∫⁻ ω : Ω, ⨆ n, G n ω ∂P) := (lintegral_iSup hG hGmono).symm
    _ = _ := lintegral_congr hGsup
