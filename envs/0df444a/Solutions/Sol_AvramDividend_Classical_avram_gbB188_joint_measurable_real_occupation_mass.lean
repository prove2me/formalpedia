-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB188_joint_measurable_real_occupation_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T19:17:40.874382+00:00
-- url     : https://prove2.me/submissions/a3e2d4d3-b1a5-4e16-a3b4-9249cac99540

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (Y : Ω → ℝ → ℝ)
    (hY : Measurable (fun z : Ω × ℝ => Y z.1 z.2))
    (n : ℕ) :
    Measurable (fun z : Ω × ℝ =>
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ Y z.1 t = z.2}) := by
  let s : Set ((Ω × ℝ) × ℝ) :=
    {z | 0 < z.2 ∧ z.2 < (n : ℝ) ∧ Y z.1.1 z.2 = z.1.2}
  have hω : Measurable (fun z : (Ω × ℝ) × ℝ => z.1.1) :=
    measurable_fst.comp measurable_fst
  have ht : Measurable (fun z : (Ω × ℝ) × ℝ => z.2) :=
    measurable_snd
  have hlevel : Measurable (fun z : (Ω × ℝ) × ℝ => z.1.2) :=
    measurable_snd.comp measurable_fst
  have hval : Measurable (fun z : (Ω × ℝ) × ℝ => Y z.1.1 z.2) :=
    hY.comp (hω.prodMk ht)
  have hs : MeasurableSet s := by
    have htime : MeasurableSet {z : (Ω × ℝ) × ℝ |
        0 < z.2 ∧ z.2 < (n : ℝ)} := by
      exact ht measurableSet_Ioo
    have heq : MeasurableSet {z : (Ω × ℝ) × ℝ |
        Y z.1.1 z.2 = z.1.2} := by
      have hh : MeasurableSet {z : (Ω × ℝ) × ℝ |
          Y z.1.1 z.2 - z.1.2 = (0 : ℝ)} := by
        exact (hval.sub hlevel) (measurableSet_singleton 0)
      simpa only [sub_eq_zero] using hh
    have hset : ({z : (Ω × ℝ) × ℝ | 0 < z.2 ∧ z.2 < (n : ℝ)} ∩
        {z : (Ω × ℝ) × ℝ | Y z.1.1 z.2 = z.1.2}) = s := by
      ext z
      simp only [s, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]
    exact hset ▸ (htime.inter heq)
  have hMass := measurable_measure_prodMk_left (ν := (volume : Measure ℝ)) hs
  simpa only [s, Set.preimage_setOf_eq] using hMass
