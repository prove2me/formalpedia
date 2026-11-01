-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_actual_levy_prejump_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:51:48.855758+00:00
-- url     : https://prove2.me/submissions/b9842bf1-e355-497e-b6cc-d149f2230f77

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun z : ℝ≥0 × Ω =>
      Function.leftLim (fun s : ℝ≥0 => X.X s z.2) z.1) := by
  have hX : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    rightContinuous_measurable_sections_joint_evaluation X.X
      (fun t => (X.adapted t).mono (𝓕.le t) le_rfl) X.rightCont
  have hAdapt : StronglyAdapted 𝓕.rightCont
      (fun t ω => Function.leftLim (fun s : ℝ≥0 => X.X s ω) t) :=
    avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits X.X
      (by intro t; exact ((X.adapted t).mono
        (𝓕.le_rightCont t) le_rfl).stronglyMeasurable)
      (by intro ω t ht; exact X.leftLim ω t ht)
  have hzero : Measurable (fun ω : Ω =>
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) (0 : ℝ≥0)) :=
    (hAdapt 0).measurable.mono (𝓕.rightCont.le 0) le_rfl
  let q : ℕ → ℝ≥0 := fun n => (1 / 2 : ℝ≥0) ^ (n + 1)
  let c : ℕ → ℝ≥0 → ℝ≥0 := fun n t => t - t * q n
  have hq : Tendsto q atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ≥0) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact hp.comp (tendsto_add_atTop_nat 1)
  have hcMeas (n : ℕ) : Measurable (c n) := by
    dsimp [c]
    exact measurable_id.sub (measurable_id.mul_const (q n))
  have hcLim (t : ℝ≥0) : Tendsto (fun n => c n t) atTop (𝓝 t) := by
    have hsmall : Tendsto (fun n => t * q n) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hq
    convert tendsto_const_nhds.sub hsmall using 1 <;> simp [c]
  have hcLt (t : ℝ≥0) (ht : 0 < t) (n : ℕ) : c n t < t := by
    have hp : 0 < q n := by dsimp [q]; positivity
    exact tsub_lt_self ht (mul_pos ht hp)
  let A : Set (ℝ≥0 × Ω) := {z | z.1 = 0}
  have hA : MeasurableSet A := by
    simpa [A] using (measurableSet_eq_fun measurable_fst measurable_const :
      MeasurableSet {z : ℝ≥0 × Ω | z.1 = 0})
  let G : ℕ → ℝ≥0 × Ω → ℝ := fun n z =>
    if z ∈ A then Function.leftLim (fun s : ℝ≥0 => X.X s z.2) 0
    else X.X (c n z.1) z.2
  have hG (n : ℕ) : Measurable (G n) := by
    have hfirst : Measurable (fun z : ℝ≥0 × Ω =>
        Function.leftLim (fun s : ℝ≥0 => X.X s z.2) 0) :=
      hzero.comp measurable_snd
    have hsecond : Measurable (fun z : ℝ≥0 × Ω => X.X (c n z.1) z.2) :=
      hX.comp (Measurable.prodMk ((hcMeas n).comp measurable_fst) measurable_snd)
    exact Measurable.ite hA hfirst hsecond
  refine measurable_of_tendsto_metrizable hG ?_
  rw [tendsto_pi_nhds]
  rintro ⟨t, ω⟩
  by_cases ht : t = 0
  · subst t
    simpa [G, A] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => Function.leftLim
        (fun s : ℝ≥0 => X.X s ω) 0) atTop
        (𝓝 (Function.leftLim (fun s : ℝ≥0 => X.X s ω) 0)))
  · have htpos : 0 < t := pos_iff_ne_zero.mpr ht
    letI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
    obtain ⟨l, hl⟩ := X.leftLim ω t htpos
    have heq : Function.leftLim (fun s : ℝ≥0 => X.X s ω) t = l :=
      leftLim_eq_of_tendsto hl
    rw [heq]
    have hc : Tendsto (fun n => c n t) atTop (𝓝[<] t) :=
      tendsto_nhdsWithin_iff.2
        ⟨hcLim t, Eventually.of_forall (fun n => hcLt t htpos n)⟩
    have hcomp : Tendsto (fun n : ℕ => X.X (c n t) ω) atTop (𝓝 l) := by
      simpa only [Function.comp_def] using hl.comp hc
    simpa [G, A, ht] using hcomp
