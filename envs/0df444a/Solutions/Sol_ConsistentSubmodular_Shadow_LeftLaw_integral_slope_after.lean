-- Prove2me | solution 1 for ConsistentSubmodular.Shadow.LeftLaw.integral_slope_after
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:29.626328+00:00
-- url     : https://prove2.me/submissions/6523c93e-732e-4ffa-a1c0-562e9138f2b1

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals
import Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_inv_continuous
import Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_inv_right

section

noncomputable section

open scoped BigOperators Topology

open MeasureTheory Filter Set

namespace ConsistentSubmodular.Shadow

/-- A bounded measurable function is integrable on every bounded interval. -/
theorem intervalIntegrable_of_bounded {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b := by
  constructor <;>
  exact Measure.integrableOn_of_bounded (by simp) hf.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)

namespace LeftLaw

variable {ι : Type*} [Fintype ι] (L : LeftLaw ι)

theorem cdf_le_one (x : ℝ) : L.cdf x ≤ 1 := by
  rw [← L.prob_sum]
  exact Finset.sum_le_sum fun j _ => by split_ifs; exacts [le_rfl, L.prob_nonneg j]

theorem cdf_mono : Monotone L.cdf := fun x y hxy => Finset.sum_le_sum fun j _ => by
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.trans hxy) h2
  · exact L.prob_nonneg j
  · exact le_rfl

theorem cdf_low_pos : 0 < L.cdf L.low := by
  obtain ⟨j, hj, hjl⟩ := L.atom
  calc 0 < L.prob j := lt_of_le_of_ne (L.prob_nonneg j) (Ne.symm hj)
    _ = if L.left j ≤ L.low then L.prob j else 0 := (if_pos hjl).symm
    _ ≤ L.cdf L.low := Finset.single_le_sum
        (f := fun j => if L.left j ≤ L.low then L.prob j else 0)
        (fun i _ => by split_ifs; exacts [L.prob_nonneg i, le_rfl])
        (Finset.mem_univ j)

theorem cdf_pos {x : ℝ} (hx : L.low ≤ x) : 0 < L.cdf x :=
  L.cdf_low_pos.trans_le (L.cdf_mono hx)

theorem pos_part_sub {a b c : ℝ} (hab : a ≤ b) :
    max 0 (b - c) - max 0 (a - c) = max 0 (b - max a c) := by
  simp only [max_def]
  split_ifs <;> linarith

/-- Fubini (8): `Σ_j p_j |[a, b] ∩ [ℓ_j, ∞)| = H(b) - H(a)`. -/
theorem ramp_sub {a b : ℝ} (hab : a ≤ b) :
    L.ramp b - L.ramp a = ∑ j, L.prob j * max 0 (b - max a (L.left j)) := by
  rw [ramp, ramp, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [← mul_sub, pos_part_sub hab]

theorem ramp_low : L.ramp L.low = 0 := Finset.sum_eq_zero fun j _ => by
  by_cases h : L.prob j = 0
  · simp [h]
  · rw [max_eq_left (by linarith [L.low_le j h]), mul_zero]

theorem ramp_sub_ge {a b : ℝ} (hab : a ≤ b) : L.cdf a * (b - a) ≤ L.ramp b - L.ramp a := by
  rw [L.ramp_sub hab, cdf, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs with h
  · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr hab)]
  · rw [zero_mul]
    exact mul_nonneg (L.prob_nonneg j) (le_max_left _ _)

theorem ramp_strictMonoOn : StrictMonoOn L.ramp (Ici L.low) := by
  intro a ha b _ hab
  have h := L.ramp_sub_ge hab.le
  have hc := L.cdf_pos ha
  nlinarith [mul_pos hc (sub_pos.mpr hab)]

theorem ramp_continuous : Continuous L.ramp :=
  continuous_finset_sum _ fun _ _ =>
    continuous_const.mul (continuous_const.max (continuous_id.sub continuous_const))

/-- `H` maps `[low, ∞)` onto `[0, ∞)`. -/
theorem exists_ramp_eq {y : ℝ} (hy : 0 ≤ y) : ∃ x ∈ Ici L.low, L.ramp x = y := by
  have hc := L.cdf_low_pos
  have hle : L.low ≤ L.low + y / L.cdf L.low := le_add_of_nonneg_right (div_nonneg hy hc.le)
  have hhigh : y ≤ L.ramp (L.low + y / L.cdf L.low) := by
    have h := L.ramp_sub_ge hle
    rwa [L.ramp_low, sub_zero, add_sub_cancel_left, mul_div_cancel₀ _ hc.ne'] at h
  obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hle L.ramp_continuous.continuousOn
    ⟨by rw [L.ramp_low]; exact hy, hhigh⟩
  exact ⟨x, hx.1, hxy⟩

theorem inv_spec (y : ℝ) : L.inv y ∈ Ici L.low ∧ L.ramp (L.inv y) = max y 0 :=
  Function.invFunOn_pos (L.exists_ramp_eq (le_max_right y 0))

theorem low_le_inv (y : ℝ) : L.low ≤ L.inv y := (L.inv_spec y).1

theorem inv_mono : Monotone L.inv := by
  intro y y' h
  by_contra hlt
  have := L.ramp_strictMonoOn (L.low_le_inv y') (L.low_le_inv y) (lt_of_not_ge hlt)
  rw [(L.inv_spec y).2, (L.inv_spec y').2] at this
  exact absurd (max_le_max h le_rfl) (not_le.mpr this)

theorem hasDerivWithinAt_inv {y : ℝ} (hy : 0 ≤ y) :
    HasDerivWithinAt L.inv (L.slope y) (Ioi y) y := by
  have haff : HasDerivAt (fun t => L.inv y + (t - y) * L.slope y) (L.slope y) y := by
    simpa using (((hasDerivAt_id y).sub_const y).mul_const (L.slope y)).const_add (L.inv y)
  exact (haff.hasDerivWithinAt.congr_of_eventuallyEq (L.inv_right hy) (by simp)).mono
    Ioi_subset_Ici_self

theorem slope_antitone : Antitone L.slope := fun _ _ h =>
  one_div_le_one_div_of_le (L.cdf_pos (L.low_le_inv _)) (L.cdf_mono (L.inv_mono h))

theorem one_le_slope (y : ℝ) : 1 ≤ L.slope y := by
  rw [slope, le_div_iff₀ (L.cdf_pos (L.low_le_inv y)), one_mul]
  exact L.cdf_le_one _

theorem slope_le (y : ℝ) : L.slope y ≤ 1 / L.cdf L.low :=
  one_div_le_one_div_of_le L.cdf_low_pos (L.cdf_mono (L.low_le_inv y))

theorem slope_measurable : Measurable L.slope := L.slope_antitone.measurable

theorem abs_slope_le (y : ℝ) : |L.slope y| ≤ 1 / L.cdf L.low := by
  rw [abs_of_nonneg (zero_le_one.trans (L.one_le_slope y))]
  exact L.slope_le y

/-- `X(b) - X(a) = ∫_a^b g` for `0 ≤ a ≤ b`. -/
theorem integral_slope {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ y in a..b, L.slope y = L.inv b - L.inv a :=
  intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab L.inv_continuous.continuousOn
    (fun _ hy => L.hasDerivWithinAt_inv (ha.trans hy.1.le))
    (intervalIntegrable_of_bounded L.slope_measurable L.abs_slope_le a b)

end LeftLaw

end ConsistentSubmodular.Shadow

end

end

section

open scoped BigOperators Topology
open MeasureTheory Filter Set
open ConsistentSubmodular ConsistentSubmodular.Shadow
open ConsistentSubmodular.Shadow.LeftLaw
variable {ι : Type*} [Fintype ι] (L : LeftLaw ι)

theorem solution {S Y : ℝ} (hS : 0 ≤ S) (hSY : S ≤ Y) :
    ∫ y in (0 : ℝ)..Y, L.slope (y + 1) * (if S ≤ y then 1 else 0) =
      L.inv (Y + 1) - L.inv (S + 1) := by
  have hmeas : Measurable fun y : ℝ => L.slope (y + 1) * (if S ≤ y then (1 : ℝ) else 0) :=
    (L.slope_measurable.comp (measurable_add_const 1)).mul
      (Measurable.ite measurableSet_Ici measurable_const measurable_const)
  have hbound : ∀ y, |L.slope (y + 1) * (if S ≤ y then (1 : ℝ) else 0)| ≤ 1 / L.cdf L.low := by
    intro y
    split_ifs
    · rw [mul_one]; exact L.abs_slope_le _
    · rw [mul_zero, abs_zero]; exact (one_div_pos.mpr L.cdf_low_pos).le
  have hint := intervalIntegrable_of_bounded hmeas hbound
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 S) (hint S Y)]
  have h1 : ∫ y in (0 : ℝ)..S, L.slope (y + 1) * (if S ≤ y then 1 else 0) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_,
      intervalIntegral.integral_zero]
    filter_upwards [(Set.countable_singleton S).ae_notMem volume] with y hy hmem
    rw [Set.uIoc_of_le hS] at hmem
    have hlt : y < S := lt_of_le_of_ne hmem.2 (by simpa using hy)
    simp [not_le.mpr hlt]
  have h2 : ∫ y in S..Y, L.slope (y + 1) * (if S ≤ y then 1 else 0) =
      ∫ y in S..Y, L.slope (y + 1) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hSY] at hy
    simp [hy.1]
  rw [h1, h2, zero_add, intervalIntegral.integral_comp_add_right,
    L.integral_slope (by linarith) (by linarith)]

end
