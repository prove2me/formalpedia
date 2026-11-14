-- Prove2me | solution 1 for ConsistentSubmodular.Shadow.LeftLaw.core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:41:13.456231+00:00
-- url     : https://prove2.me/submissions/48c7e6f1-0813-4a91-af01-2ab631e26109

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals
import Theorems.Thm_ConsistentSubmodular_Shadow_chain_bound
import Theorems.Thm_ConsistentSubmodular_Shadow_integral_sum_shift
import Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_inv_continuous
import Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_inv_right
import Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_integral_adaptation

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

theorem cdf_eq_one {x : ℝ} (hx : ∀ j, L.left j ≤ x) : L.cdf x = 1 := by
  rw [← L.prob_sum]
  exact Finset.sum_congr rfl fun j _ => if_pos (hx j)

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

theorem ramp_mono : Monotone L.ramp := fun a b hab => by
  have h := L.ramp_sub hab
  have : 0 ≤ ∑ j, L.prob j * max 0 (b - max a (L.left j)) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (L.prob_nonneg j) (le_max_left _ _)
  linarith

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

theorem inv_zero : L.inv 0 = L.low := by
  rw [← L.ramp_low, L.inv_ramp le_rfl]

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

theorem div_slope (x y : ℝ) : x / L.slope y = x * L.cdf (L.inv y) := by
  rw [slope, div_div_eq_mul_div, div_one]

/-- Beyond every left endpoint, `Y = H(X(Y)) = X(Y) - B`. -/
theorem inv_eq_of_ge {Y : ℝ} (hY : 0 ≤ Y) (hX : ∀ j, L.left j ≤ L.inv Y) :
    L.inv Y = Y + L.mean := by
  have h := L.ramp_of_ge hX
  rw [L.ramp_inv hY] at h
  linarith

theorem measurable_adaptation :
    Measurable fun y => 1 - L.slope (y + 1) * L.cdf (L.inv y) :=
  measurable_const.sub ((L.slope_measurable.comp (measurable_add_const 1)).mul
    (L.cdf_mono.comp L.inv_mono).measurable)

theorem abs_adaptation_le (y : ℝ) :
    |1 - L.slope (y + 1) * L.cdf (L.inv y)| ≤ 1 + 1 / L.cdf L.low := by
  have h1 := L.one_le_slope (y + 1)
  have h2 := L.slope_le (y + 1)
  have h3 := L.cdf_nonneg (L.inv y)
  have h4 := L.cdf_le_one (L.inv y)
  rw [abs_le]
  constructor <;> nlinarith

/-- Identity (10): `∫_0^Y (g - 1) = B - low` once `X(Y)` lies beyond every left endpoint. -/
theorem integral_slope_sub_one {Y : ℝ} (hY : 0 ≤ Y) (hX : ∀ j, L.left j ≤ L.inv Y) :
    ∫ y in (0 : ℝ)..Y, (L.slope y - 1) = L.mean - L.low := by
  rw [intervalIntegral.integral_sub
      (intervalIntegrable_of_bounded L.slope_measurable L.abs_slope_le 0 Y) intervalIntegrable_const,
    L.integral_slope le_rfl hY, intervalIntegral.integral_const, L.inv_zero,
    L.inv_eq_of_ge hY hX, smul_eq_mul, mul_one, sub_zero]
  ring

theorem intervalIntegrable_sum_shift {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hC : ∀ x, |φ x| ≤ C) (N : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun s => ∑ j ∈ Finset.range N, φ (s + j)) volume a b := by
  refine intervalIntegrable_of_bounded (C := N * C)
    (Finset.measurable_sum _ fun j _ => hφ.comp (measurable_add_const _)) (fun s => ?_) a b
  calc |∑ j ∈ Finset.range N, φ (s + j)| ≤ ∑ j ∈ Finset.range N, |φ (s + j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range N, C := Finset.sum_le_sum fun j _ => hC _
    _ = N * C := by simp

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

theorem solution {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hchain : ConsistentSubmodular.Shadow.ChainHypothesis α)
    (hlow : 0 ≤ L.low) (r : ι → ℝ) (hr : ∀ j, L.prob j ≠ 0 → L.left j ≤ r j)
    (hM : ∀ j, L.prob j ≠ 0 → L.ramp (r j) - L.ramp (L.left j) ≤ 1) :
    α * (L.mean + ∑ j, L.prob j * (r j - L.left j)) ≤ L.mean + 1 := by
  -- `U` bounds every left endpoint, and beyond `N ≥ H(U)` we have `X ≥ U` and `g = 1`.
  have hUl : ∀ j, L.left j ≤ |L.low| + ∑ i, |L.left i| := fun j => by
    have := Finset.single_le_sum (f := fun i => |L.left i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ j)
    linarith [le_abs_self (L.left j), abs_nonneg L.low]
  have hUlow : L.low ≤ |L.low| + ∑ i, |L.left i| := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg (L.left i)
    linarith [le_abs_self L.low]
  set U := |L.low| + ∑ i, |L.left i|
  set N : ℕ := ⌈L.ramp U⌉₊
  have hN : L.ramp U ≤ N := Nat.le_ceil _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hbeyond : ∀ y : ℝ, (N : ℝ) ≤ y → ∀ j, L.left j ≤ L.inv y := fun y hy j =>
    calc L.left j ≤ U := hUl j
      _ = L.inv (L.ramp U) := (L.inv_ramp hUlow).symm
      _ ≤ L.inv y := L.inv_mono (hN.trans hy)
  have hS : ∀ j, L.prob j ≠ 0 → L.ramp (L.left j) ≤ N := fun j _ =>
    (L.ramp_mono (hUl j)).trans hN
  -- The extension (9): `r_j ≤ X(H(ℓ_j) + 1)`.
  have hext : ∑ j, L.prob j * (r j - L.left j) ≤
      ∑ j, L.prob j * (L.inv (L.ramp (L.left j) + 1) - L.left j) := by
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hp : L.prob j = 0
    · simp [hp]
    · refine mul_le_mul_of_nonneg_left (sub_le_sub_right ?_ _) (L.prob_nonneg j)
      calc r j = L.inv (L.ramp (r j)) := (L.inv_ramp ((L.low_le j hp).trans (hr j hp))).symm
        _ ≤ L.inv (L.ramp (L.left j) + 1) := L.inv_mono (by linarith [hM j hp])
  -- The chain bound for `g(s), g(s + 1), …, g(s + N) = 1` at every `s ∈ [0, 1]`.
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      α * ∑ j ∈ Finset.range N, (1 - L.slope (s + j + 1) * L.cdf (L.inv (s + j))) ≤
        (1 - α) * (1 + ∑ j ∈ Finset.range N, (L.slope (s + j) - 1)) := by
    intro s hs
    have h := ConsistentSubmodular.Shadow.chain_bound hα0 hchain (N := N) (d := fun j => L.slope (s + j))
      (fun j _ => L.slope_antitone (by push_cast; linarith))
      (by simp only [ConsistentSubmodular.Shadow.LeftLaw.slope]; rw [L.cdf_eq_one (hbeyond _ (by linarith [hs.1])), div_one])
    have hsum : ∑ j ∈ Finset.range N, (1 - L.slope (s + j + 1) * L.cdf (L.inv (s + j))) =
        ∑ j ∈ Finset.range N, (1 - L.slope (s + ↑(j + 1)) / L.slope (s + j)) :=
      Finset.sum_congr rfl fun j _ => by rw [L.div_slope, Nat.cast_succ, add_assoc]
    rw [hsum]
    exact h
  have hm₁ := L.measurable_adaptation
  have hm₂ : Measurable fun y => L.slope y - 1 := L.slope_measurable.sub measurable_const
  have hb₂ : ∀ y, |L.slope y - 1| ≤ 1 / L.cdf L.low + 1 := fun y => by
    have := L.abs_slope_le y
    calc |L.slope y - 1| ≤ |L.slope y| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ 1 / L.cdf L.low + 1 := by rw [abs_one]; linarith
  have hint := intervalIntegral.integral_mono_on zero_le_one
    ((ConsistentSubmodular.Shadow.LeftLaw.intervalIntegrable_sum_shift hm₁ L.abs_adaptation_le N 0 1).const_mul α)
    ((IntervalIntegrable.add intervalIntegrable_const
      (ConsistentSubmodular.Shadow.LeftLaw.intervalIntegrable_sum_shift hm₂ hb₂ N 0 1)).const_mul (1 - α)) hpoint
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add intervalIntegrable_const
      (ConsistentSubmodular.Shadow.LeftLaw.intervalIntegrable_sum_shift hm₂ hb₂ N 0 1),
    ConsistentSubmodular.Shadow.integral_sum_shift hm₁ L.abs_adaptation_le N, ConsistentSubmodular.Shadow.integral_sum_shift hm₂ hb₂ N,
    L.integral_adaptation hN0 hS (hbeyond N le_rfl),
    L.integral_slope_sub_one hN0 (hbeyond N le_rfl), intervalIntegral.integral_const,
    smul_eq_mul, sub_zero, mul_one] at hint
  nlinarith [mul_le_mul_of_nonneg_left hext hα0, mul_nonneg (sub_nonneg.mpr hα1) hlow]

end
