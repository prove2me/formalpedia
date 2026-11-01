-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_joint_measurable_leftLim_of_joint_and_leftLimits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:26:28.90698+00:00
-- url     : https://prove2.me/submissions/ef93767f-03da-4109-9da9-b24fdc27548f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_prejump_fractional_left_time_mesh

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical
noncomputable section

/-- Joint measurability transfers to strict left limits, retaining the time-zero section. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (F : ℝ≥0 → Ω → ℝ)
    (hJoint : Measurable (fun z : ℝ≥0 × Ω => F z.1 z.2))
    (hzero : Measurable (fun ω : Ω =>
      Function.leftLim (fun s : ℝ≥0 => F s ω) (0 : ℝ≥0)))
    (hleft : ∀ ω t, 0 < t → ∃ l : ℝ,
      Tendsto (fun s : ℝ≥0 => F s ω) (𝓝[<] t) (𝓝 l)) :
    Measurable (fun z : ℝ≥0 × Ω =>
      Function.leftLim (fun s : ℝ≥0 => F s z.2) z.1) := by
  obtain ⟨hMeas, hLim, hLt⟩ :=
    AvramDividend.Classical.avram_wave4_04b_prejump_fractional_left_time_mesh
  let c : ℕ → ℝ≥0 → ℝ≥0 :=
    fun n t => t - t * (1 / 2 : ℝ≥0) ^ (n + 1)
  have hcMeas (n : ℕ) : Measurable (c n) := by
    simpa only [c] using hMeas n
  have hcLim (t : ℝ≥0) : Tendsto (fun n => c n t) atTop (𝓝 t) := by
    simpa only [c] using hLim t
  have hcLt (t : ℝ≥0) (ht : 0 < t) (n : ℕ) : c n t < t := by
    simpa only [c] using hLt t ht n
  let A : Set (ℝ≥0 × Ω) := {z | z.1 = 0}
  have hA : MeasurableSet A := by
    simpa [A] using (measurableSet_eq_fun measurable_fst measurable_const :
      MeasurableSet {z : ℝ≥0 × Ω | z.1 = 0})
  let G : ℕ → ℝ≥0 × Ω → ℝ := fun n z =>
    if z ∈ A then Function.leftLim (fun s : ℝ≥0 => F s z.2) 0
    else F (c n z.1) z.2
  have hG (n : ℕ) : Measurable (G n) := by
    have hfirst : Measurable (fun z : ℝ≥0 × Ω =>
        Function.leftLim (fun s : ℝ≥0 => F s z.2) 0) :=
      hzero.comp measurable_snd
    have hsecond : Measurable (fun z : ℝ≥0 × Ω => F (c n z.1) z.2) :=
      hJoint.comp
        (Measurable.prodMk ((hcMeas n).comp measurable_fst) measurable_snd)
    exact Measurable.ite hA hfirst hsecond
  refine measurable_of_tendsto_metrizable hG ?_
  rw [tendsto_pi_nhds]
  rintro ⟨t, ω⟩
  by_cases ht : t = 0
  · subst t
    simpa [G, A] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => Function.leftLim
        (fun s : ℝ≥0 => F s ω) 0) atTop
        (𝓝 (Function.leftLim (fun s : ℝ≥0 => F s ω) 0)))
  · have htpos : 0 < t := pos_iff_ne_zero.mpr ht
    letI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
    obtain ⟨l, hl⟩ := hleft ω t htpos
    have heq : Function.leftLim (fun s : ℝ≥0 => F s ω) t = l :=
      leftLim_eq_of_tendsto hl
    rw [heq]
    have hc : Tendsto (fun n => c n t) atTop (𝓝[<] t) :=
      tendsto_nhdsWithin_iff.2
        ⟨hcLim t, Eventually.of_forall (fun n => hcLt t htpos n)⟩
    have hcomp : Tendsto (fun n : ℕ => F (c n t) ω) atTop (𝓝 l) := by
      simpa only [Function.comp_def] using hl.comp hc
    simpa [G, A, ht] using hcomp
