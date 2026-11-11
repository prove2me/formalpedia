-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise35_original_dyadic_finite_simple_condexp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:47:52.573569+00:00
-- url     : https://prove2.me/submissions/8d21b308-df74-48f0-8139-7353166c80a3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise17_original_finite_simple_mark_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
/-- Exact integrability and original-filtration centring of dyadic marked cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ C k i)
      let M : ℕ → Ω → ℝ := fun k ω =>
        ∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
            ((J k i ω).toReal -
              (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
      (∀ k, Integrable (M k) P) ∧
      (∀ k, P[M k | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ))) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro n s t hst
  let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  let C : ℕ → ℕ → Set ℝ := fun k i =>
    B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
  let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ C k i)
  let M : ℕ → Ω → ℝ := fun k ω =>
    ∑ i ∈ Finset.range (2 ^ k),
      (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
        ((J k i ω).toReal -
          (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
  have hCmeas (k i : ℕ) : MeasurableSet (C k i) := by
    dsimp [C, B]
    exact measurableSet_Ioc.inter measurableSet_Ioc
  have hBsub : B ⊆ Iio (0 : ℝ) := by
    intro z hz
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact lt_of_le_of_lt hz.2 (neg_lt_zero.mpr hp)
  have hCfinite (k i : ℕ) : X.ν (C k i) < ⊤ := by
    have hs : C k i ⊆ Iio (0 : ℝ) := fun z hz => hBsub hz.1
    exact lt_of_le_of_lt (measure_mono hs) (lt_top_iff_ne_top.mpr hFinite)
  have hJmeas (k i : ℕ) : Measurable (J k i) := by
    have h := avram_p2_f_weighted_original_intrinsic_rectangle_measurable
      X s (t - s) (C k i) (hCmeas k i)
    simpa only [J, add_tsub_cancel_of_le hst] using h
  have hJint (k i : ℕ) : Integrable (fun ω => (J k i ω).toReal) P := by
    have hRate := avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
      X s t hst (C k i) (hCmeas k i)
    have h := avram_p2_e_compensator_finite_nu_count_real_integrable
      X s t hst (C k i) (hCmeas k i) (hCfinite k i) hRate
    simpa only [J] using h
  have hMInt (k : ℕ) : Integrable (M k) P := by
    unfold M
    apply integrable_finset_sum
    intro i hi
    exact ((hJint k i).sub (integrable_const _)).const_mul _
  have hMZero (k : ℕ) : P[M k | 𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ)) := by
    by_cases heq : s = t
    · subst t
      have hz : M k = fun _ => (0 : ℝ) := by
        funext ω
        simp [M, J]
      simpa [hz] using (condExp_zero (μ := P) (m := 𝓕.rightCont s))
    · have hlt : s < t := lt_of_le_of_ne hst heq
      let q : ℝ≥0 := 1 / 2
      let r : ℕ → ℝ≥0 := fun j => s + (t - s) * q ^ j
      have hq : 0 < q := by norm_num [q]
      have hqle : q ≤ 1 := by norm_num [q]
      have hδpos : 0 < t - s := tsub_pos_iff_lt.mpr hlt
      have hsr : ∀ j, s < r j := by
        intro j
        have hpos : 0 < (t - s) * q ^ j := mul_pos hδpos (pow_pos hq _)
        exact lt_add_of_pos_right s hpos
      have hrt : ∀ j, r j ≤ t := by
        intro j
        have hp : q ^ j ≤ 1 := by
          induction j with
          | zero => simp
          | succ j ih =>
            calc
              q ^ (j + 1) = q ^ j * q := pow_succ q j
              _ ≤ 1 * 1 := mul_le_mul ih hqle (by positivity) (by positivity)
              _ = 1 := one_mul 1
        calc
          r j = s + (t - s) * q ^ j := rfl
          _ ≤ s + (t - s) :=
            add_le_add_right (by simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ≥0) ≤ t - s))) s
          _ = t := add_tsub_cancel_of_le hst
      have hq0 : Tendsto (fun j : ℕ => q ^ j) atTop (𝓝 (0 : ℝ≥0)) :=
        NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num [q])
      have hδ0 : Tendsto (fun j => (t - s) * q ^ j) atTop (𝓝 (0 : ℝ≥0)) := by
        simpa using (tendsto_const_nhds.mul hq0 :
          Tendsto (fun j : ℕ => (t - s) * q ^ j) atTop (𝓝 ((t - s) * 0)))
      have hShort : Tendsto (fun j => r j - s) atTop (𝓝 (0 : ℝ≥0)) := by
        simpa only [r, add_tsub_cancel_left] using hδ0
      have hr : Tendsto r atTop (𝓝 s) := by
        simpa only [r, add_zero] using
          (tendsto_const_nhds.add hδ0 :
            Tendsto (fun j : ℕ => s + (t - s) * q ^ j) atTop (𝓝 (s + 0)))
      have hLong : Tendsto (fun j => t - r j) atTop (𝓝 (t - s)) := by
        have hrReal : Tendsto (fun j => (r j : ℝ)) atTop (𝓝 (s : ℝ)) :=
          NNReal.tendsto_coe.mpr hr
        have hReal :=
          (tendsto_const_nhds.sub hrReal :
            Tendsto (fun j : ℕ => (t : ℝ) - (r j : ℝ)) atTop (𝓝 ((t : ℝ) - (s : ℝ))))
        have hCoe : (fun j : ℕ => ((t - r j : ℝ≥0) : ℝ)) =
            (fun j : ℕ => (t : ℝ) - (r j : ℝ)) := by
          funext j
          exact NNReal.coe_sub (hrt j)
        have hCoeLim : ((t - s : ℝ≥0) : ℝ) = (t : ℝ) - (s : ℝ) :=
          NNReal.coe_sub hst
        apply NNReal.tendsto_coe.mp
        rw [hCoe, hCoeLim]
        exact hReal
      let J' : ℕ → ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun i a b ω =>
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc a b ×ˢ C k i)
      have h := avram_anoise17_original_finite_simple_mark_condexp_zero
        X s t r hsr hrt hShort hLong
        (Finset.range (2 ^ k)) (fun i => C k i)
        (by intro i hi; exact hCmeas k i)
        (by intro i hi; exact ne_top_of_lt (hCfinite k i))
        J' (by intro i hi a b ω; rfl)
        (by intro i hi; simpa only [J', J] using hJmeas k i)
        (fun i => -1 + (i : ℝ) / (2 : ℝ) ^ k)
      simpa only [M, J, J'] using h
  exact ⟨hMInt, hMZero⟩
