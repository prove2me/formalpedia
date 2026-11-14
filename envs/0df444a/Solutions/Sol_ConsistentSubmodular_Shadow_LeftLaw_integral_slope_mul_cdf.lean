-- Prove2me | solution 1 for ConsistentSubmodular.Shadow.LeftLaw.integral_slope_mul_cdf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:38:12.552192+00:00
-- url     : https://prove2.me/submissions/34d393f6-cd59-4a6f-b9c3-e7b7cfb6cd74

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals
import Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_integral_slope_after

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

theorem ramp_nonneg (x : ℝ) : 0 ≤ L.ramp x :=
  Finset.sum_nonneg fun j _ => mul_nonneg (L.prob_nonneg j) (le_max_left _ _)

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

theorem ramp_inv {y : ℝ} (hy : 0 ≤ y) : L.ramp (L.inv y) = y := by
  rw [(L.inv_spec y).2, max_eq_left hy]

theorem inv_mono : Monotone L.inv := by
  intro y y' h
  by_contra hlt
  have := L.ramp_strictMonoOn (L.low_le_inv y') (L.low_le_inv y) (lt_of_not_ge hlt)
  rw [(L.inv_spec y).2, (L.inv_spec y').2] at this
  exact absurd (max_le_max h le_rfl) (not_le.mpr this)

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

/-- `Pr[H(ℓ_J) ≤ y] = W(X(y)) = 1 / g(y)` for `y ≥ 0`. -/
theorem cdf_inv {y : ℝ} (hy : 0 ≤ y) :
    L.cdf (L.inv y) = ∑ j, if L.ramp (L.left j) ≤ y then L.prob j else 0 := by
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hp : L.prob j = 0
  · simp [hp]
  · have h2 := L.ramp_strictMonoOn.le_iff_le (L.low_le j hp) (L.low_le_inv y)
    rw [L.ramp_inv hy] at h2
    simp only [h2]

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

theorem solution {Y : ℝ} (hY : 0 ≤ Y)
    (hS : ∀ j, L.prob j ≠ 0 → L.ramp (L.left j) ≤ Y) :
    ∫ y in (0 : ℝ)..Y, L.slope (y + 1) * L.cdf (L.inv y) =
      ∑ j, L.prob j * (L.inv (Y + 1) - L.inv (L.ramp (L.left j) + 1)) := by
  have hcongr : Set.EqOn (fun y => L.slope (y + 1) * L.cdf (L.inv y))
      (fun y => ∑ j, L.prob j * (L.slope (y + 1) *
        (if L.ramp (L.left j) ≤ y then 1 else 0))) (Set.uIcc 0 Y) := by
    intro y hy
    rw [Set.uIcc_of_le hY] at hy
    simp only [L.cdf_inv hy.1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul]
    by_cases hp : L.prob j = 0
    · simp [hp]
    · rw [L.integral_slope_after (L.ramp_nonneg _) (hS j hp)]
  · intro j _
    refine intervalIntegrable_of_bounded (C := |L.prob j| * (1 / L.cdf L.low)) ?_ (fun y => ?_) 0 Y
    · exact measurable_const.mul ((L.slope_measurable.comp (measurable_add_const 1)).mul
        (Measurable.ite measurableSet_Ici measurable_const measurable_const))
    · rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      split_ifs
      · rw [mul_one]; exact L.abs_slope_le _
      · rw [mul_zero, abs_zero]; exact (one_div_pos.mpr L.cdf_low_pos).le

end
