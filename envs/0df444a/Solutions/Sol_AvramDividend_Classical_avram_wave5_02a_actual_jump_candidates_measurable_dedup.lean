-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02a_actual_jump_candidates_measurable_dedup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:35:07.073233+00:00
-- url     : https://prove2.me/submissions/11a8363f-bd50-4064-bdee-bf18e4cc7562

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℕ → Ω → ℝ≥0) (hT : ∀ n, Measurable (T n)) :
    let A : ℕ → Set Ω := fun n => {ω |
      0 < T n ω ∧
      X.X (T n ω) ω -
        Function.leftLim (fun u : ℝ≥0 => X.X u ω) (T n ω) ≠ 0 ∧
      ∀ m < n, T m ω ≠ T n ω}
    (∀ n, MeasurableSet (A n)) ∧
    (∀ ω n m, ω ∈ A n → ω ∈ A m → n ≠ m → T n ω ≠ T m ω) := by
  dsimp
  constructor
  · intro n
    have hj : Measurable (fun ω =>
        X.X (T n ω) ω -
          Function.leftLim (fun u : ℝ≥0 => X.X u ω) (T n ω)) :=
      (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp
        ((hT n).prodMk measurable_id)
    have hp : MeasurableSet {ω | (0 : ℝ≥0) < T n ω} :=
      measurableSet_lt measurable_const (hT n)
    have hn : MeasurableSet {ω |
        X.X (T n ω) ω -
          Function.leftLim (fun u : ℝ≥0 => X.X u ω) (T n ω) ≠ 0} :=
      (measurableSet_eq_fun hj measurable_const).compl
    have hd : MeasurableSet {ω | ∀ m < n, T m ω ≠ T n ω} := by
      simp only [setOf_forall]
      exact MeasurableSet.iInter fun m =>
        MeasurableSet.iInter fun _ => (measurableSet_eq_fun (hT m) (hT n)).compl
    exact hp.inter (hn.inter hd)
  · intro ω n m hn hm hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact fun heq => (hm.2.2 n h) heq
    · exact fun heq => (hn.2.2 m h) heq.symm
