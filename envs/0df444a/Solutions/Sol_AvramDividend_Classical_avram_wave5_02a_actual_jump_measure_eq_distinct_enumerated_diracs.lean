-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02a_actual_jump_measure_eq_distinct_enumerated_diracs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:50:59.987386+00:00
-- url     : https://prove2.me/submissions/d2a4ce57-fa5a-4d1a-ba55-b14d7c006802

import Mathlib
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
    (T : ℕ → Ω → ℝ≥0) (A : ℕ → Set Ω)
    (hActive : ∀ ω n, ω ∈ A n → 0 < T n ω ∧
      X.X (T n ω) ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) (T n ω) ≠ 0)
    (hInject : ∀ ω n m, ω ∈ A n → ω ∈ A m → T n ω = T m ω → n = m)
    (hCover : ∀ ω u, 0 < u →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
      ∃ n, ω ∈ A n ∧ T n ω = u) :
    ∀ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) =
      Measure.sum (fun n => (A n).indicator
        (fun _ => Measure.dirac (T n ω, X.X (T n ω) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) (T n ω))) ω) := by
  classical
  intro ω
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let S : Set ℝ≥0 := {u | 0 < u ∧ j u ≠ 0}
  let F : ℝ≥0 → ℝ≥0 × ℝ := fun u => (u, j u)
  have hj : Measurable j :=
    (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp
      (measurable_id.prodMk measurable_const)
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_eq_fun hj measurable_const).compl
  have hF : Measurable F := measurable_id.prodMk hj
  change (Measure.count.restrict S).map F = _
  apply Measure.ext
  intro E hE
  let B : Set ℝ≥0 := F ⁻¹' E ∩ S
  let N : Set ℕ := {n | ω ∈ A n ∧ F (T n ω) ∈ E}
  have hN : MeasurableSet N := MeasurableSet.of_discrete
  have hpre : MeasurableSet (F ⁻¹' E) := hE.preimage hF
  have hmap : ((Measure.count.restrict S).map F) E = (B.encard : ℝ≥0∞) := by
    rw [Measure.map_apply hF hE, Measure.restrict_apply hpre,
      Measure.count_apply (hpre.inter hS)]
  have hsum : (Measure.sum (fun n => (A n).indicator
      (fun _ => Measure.dirac (F (T n ω))) ω)) E = (N.encard : ℝ≥0∞) := by
    rw [Measure.sum_apply _ hE]
    calc
      (∑' n, ((A n).indicator (fun _ => Measure.dirac (F (T n ω))) ω) E) =
          ∫⁻ n, N.indicator (fun _ => (1 : ℝ≥0∞)) n ∂Measure.count := by
        rw [lintegral_count]
        apply tsum_congr
        intro n
        by_cases h : ω ∈ A n <;> by_cases h' : F (T n ω) ∈ E <;>
          simp [N, Set.indicator, h, h', Measure.dirac_apply]
      _ = Measure.count N := lintegral_indicator_one hN
      _ = (N.encard : ℝ≥0∞) := Measure.count_apply hN
  have hBij : Function.Bijective (fun n : N => (⟨T n.1 ω, by
      obtain ⟨ha, he⟩ := n.2
      exact ⟨he, hActive ω n.1 ha⟩⟩ : B)) := by
    constructor
    · intro n m heq
      apply Subtype.ext
      apply hInject ω n.1 m.1 n.2.1 m.2.1
      exact congrArg Subtype.val heq
    · intro u
      obtain ⟨he, hp, hjump⟩ := u.2
      obtain ⟨n, han, hnu⟩ := hCover ω u.1 hp hjump
      refine ⟨⟨n, han, ?_⟩, ?_⟩
      · simpa [hnu] using he
      · apply Subtype.ext
        exact hnu
  have hcard : N.encard = B.encard :=
    Set.encard_congr (Equiv.ofBijective _ hBij)
  rw [hmap, hsum, hcard]
