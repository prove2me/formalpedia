-- Prove2me | solution 1 for ConsistentSubmodular.Shadow.LeftLaw.integral_adaptation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:39:37.075377+00:00
-- url     : https://prove2.me/submissions/b965e9d6-107a-416a-8d27-74bff8daa06e

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals
import Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_integral_slope_mul_cdf

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

theorem cdf_nonneg (x : ℝ) : 0 ≤ L.cdf x :=
  Finset.sum_nonneg fun j _ => by split_ifs; exacts [L.prob_nonneg j, le_rfl]

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

/-- Beyond every left endpoint, `H(x) = x - B`. -/
theorem ramp_of_ge {x : ℝ} (hx : ∀ j, L.left j ≤ x) : L.ramp x = x - L.mean := by
  rw [ramp, mean]
  calc ∑ j, L.prob j * max 0 (x - L.left j) = ∑ j, (L.prob j * x - L.prob j * L.left j) :=
        Finset.sum_congr rfl fun j _ => by rw [max_eq_right (sub_nonneg.mpr (hx j))]; ring
    _ = x - ∑ j, L.prob j * L.left j := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, L.prob_sum, one_mul]

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

theorem inv_ramp {x : ℝ} (hx : L.low ≤ x) : L.inv (L.ramp x) = x :=
  L.ramp_strictMonoOn.injOn (L.low_le_inv _) hx (L.ramp_inv (L.ramp_nonneg x))

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

theorem sum_prob_mul_sub (a : ℝ) (b : ι → ℝ) :
    ∑ j, L.prob j * (a - b j) = a - ∑ j, L.prob j * b j := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, L.prob_sum, one_mul]

/-- Beyond every left endpoint, `Y = H(X(Y)) = X(Y) - B`. -/
theorem inv_eq_of_ge {Y : ℝ} (hY : 0 ≤ Y) (hX : ∀ j, L.left j ≤ L.inv Y) :
    L.inv Y = Y + L.mean := by
  have h := L.ramp_of_ge hX
  rw [L.ramp_inv hY] at h
  linarith

theorem inv_add_one {Y : ℝ} (hY : 0 ≤ Y) (hX : ∀ j, L.left j ≤ L.inv Y) :
    L.inv (Y + 1) = L.inv Y + 1 := by
  have h : L.ramp (L.inv Y + 1) = Y + 1 := by
    rw [L.ramp_of_ge fun j => (hX j).trans (by linarith), L.inv_eq_of_ge hY hX]
    ring
  rw [← h, L.inv_ramp (by linarith [L.low_le_inv Y])]

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
    (hS : ∀ j, L.prob j ≠ 0 → L.ramp (L.left j) ≤ Y) (hX : ∀ j, L.left j ≤ L.inv Y) :
    ∫ y in (0 : ℝ)..Y, (1 - L.slope (y + 1) * L.cdf (L.inv y)) =
      ∑ j, L.prob j * (L.inv (L.ramp (L.left j) + 1) - L.left j) - 1 := by
  have hint : IntervalIntegrable (fun y => L.slope (y + 1) * L.cdf (L.inv y)) volume 0 Y := by
    refine intervalIntegrable_of_bounded (f := fun y => L.slope (y + 1) * L.cdf (L.inv y))
      (C := 1 / L.cdf L.low) ((L.slope_measurable.comp (measurable_add_const 1)).mul
        (L.cdf_mono.comp L.inv_mono).measurable) (fun y => ?_) 0 Y
    rw [abs_mul, abs_of_nonneg (L.cdf_nonneg _)]
    calc |L.slope (y + 1)| * L.cdf (L.inv y) ≤ (1 / L.cdf L.low) * 1 :=
          mul_le_mul (L.abs_slope_le _) (L.cdf_le_one _) (L.cdf_nonneg _)
            (one_div_pos.mpr L.cdf_low_pos).le
      _ = 1 / L.cdf L.low := mul_one _
  rw [intervalIntegral.integral_sub intervalIntegrable_const hint, intervalIntegral.integral_const,
    L.integral_slope_mul_cdf hY hS, L.sum_prob_mul_sub, L.inv_add_one hY hX,
    L.inv_eq_of_ge hY hX, smul_eq_mul, mul_one, sub_zero]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [mean]
  ring

end
