-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_hjb_finite_clock_budget_to_full
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:42:18.161389+00:00
-- url     : https://prove2.me/submissions/a816aa59-f787-408c-b053-f11823d75e1f

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_strict_exit_event_iSup
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (u d v : Ω → ℝ≥0∞)
    (hu : Measurable u) (hd : Measurable d) (hv : Measurable v)
    (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hfinite : ∀ n : ℕ,
      a * (∫⁻ ω, if u ω < d ω ∧ u ω ≤ (n : ℝ≥0∞) then v ω else 0 ∂P).toReal ≤ c) :
    a * (∫⁻ ω, if u ω < d ω then v ω else 0 ∂P).toReal ≤ c := by
  let f : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    if u ω < d ω ∧ u ω ≤ (n : ℝ≥0∞) then v ω else 0
  have hmeas : ∀ n : ℕ, Measurable (f n) := by
    intro n
    exact Measurable.ite
      ((measurableSet_lt hu hd).inter (measurableSet_le hu measurable_const))
      hv measurable_const
  have hmono : Monotone f := by
    intro n m hnm ω
    dsimp [f]
    by_cases hn : u ω < d ω ∧ u ω ≤ (n : ℝ≥0∞)
    · have hm : u ω < d ω ∧ u ω ≤ (m : ℝ≥0∞) := by
        refine ⟨hn.1, hn.2.trans ?_⟩
        exact_mod_cast hnm
      simp only [if_pos hn, if_pos hm]
      exact le_rfl
    · by_cases hm : u ω < d ω ∧ u ω ≤ (m : ℝ≥0∞)
      · simp only [if_neg hn, if_pos hm]
        exact bot_le
      · simp only [if_neg hn, if_neg hm]
        exact le_rfl
  have hpoint (ω : Ω) :
      (⨆ n : ℕ, f n ω) = if u ω < d ω then v ω else 0 := by
    simpa only [f] using
      (AvramDividend.Classical.avram_p4_f6_hjb_strict_exit_event_iSup (u ω) (d ω) (v ω))
  have hMCT :
      (∫⁻ ω, if u ω < d ω then v ω else 0 ∂P) =
        ⨆ n : ℕ, (∫⁻ ω, f n ω ∂P) := by
    calc
      _ = ∫⁻ ω, (⨆ n : ℕ, f n ω) ∂P := by
        congr 1
        funext ω
        exact (hpoint ω).symm
      _ = _ := MeasureTheory.lintegral_iSup hmeas hmono
  let I : ℕ → ℝ≥0∞ := fun n => ∫⁻ ω, f n ω ∂P
  by_cases htop : (∫⁻ ω, if u ω < d ω then v ω else 0 ∂P) = ⊤
  · simpa [htop] using hc
  · have hFn : ∀ n : ℕ, I n ≠ ⊤ := by
      intro n
      have hle : I n ≤ (∫⁻ ω, if u ω < d ω then v ω else 0 ∂P) := by
        rw [hMCT]
        exact le_iSup I n
      exact ne_top_of_le_ne_top htop hle
    have hsup : a * (⨆ n : ℕ, (I n).toReal) ≤ c := by
      rcases lt_or_eq_of_le ha with hpos | hzero
      · have hdiv : (⨆ n : ℕ, (I n).toReal) ≤ c / a := by
          apply ciSup_le
          intro n
          apply (le_div_iff₀ hpos).2
          calc
            (I n).toReal * a = a * (I n).toReal := mul_comm _ _
            _ ≤ c := hfinite n
        calc
          a * (⨆ n : ℕ, (I n).toReal) = (⨆ n : ℕ, (I n).toReal) * a := mul_comm _ _
          _ ≤ c := (le_div_iff₀ hpos).1 hdiv
      · subst a
        simpa using hc
    rw [hMCT, ENNReal.toReal_iSup hFn]
    exact hsup
