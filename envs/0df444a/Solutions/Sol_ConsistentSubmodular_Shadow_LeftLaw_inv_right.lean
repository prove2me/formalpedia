-- Prove2me | solution 1 for ConsistentSubmodular.Shadow.LeftLaw.inv_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:11.444795+00:00
-- url     : https://prove2.me/submissions/c44970e6-38c9-44a7-b955-467fc5100d45

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals
import Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_ramp_right

section

noncomputable section

open scoped BigOperators Topology

open MeasureTheory Filter Set

namespace ConsistentSubmodular.Shadow

namespace LeftLaw

variable {ι : Type*} [Fintype ι] (L : LeftLaw ι)

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

theorem inv_ramp {x : ℝ} (hx : L.low ≤ x) : L.inv (L.ramp x) = x :=
  L.ramp_strictMonoOn.injOn (L.low_le_inv _) hx (L.ramp_inv (L.ramp_nonneg x))

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

theorem solution {y : ℝ} (hy : 0 ≤ y) :
    ∀ᶠ t in 𝓝[≥] y, L.inv t = L.inv y + (t - y) * L.slope y := by
  have hc : 0 < L.cdf (L.inv y) := L.cdf_pos (L.low_le_inv y)
  have htend : Tendsto (fun t => (t - y) / L.cdf (L.inv y)) (𝓝[≥] y) (𝓝[≥] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (((continuous_id.sub continuous_const).div_const _).tendsto' y 0
        (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : y ≤ t)
      exact div_nonneg (sub_nonneg.mpr ht) hc.le
  filter_upwards [htend.eventually (L.ramp_right (L.inv y)), self_mem_nhdsWithin] with t ht
    (hyt : y ≤ t)
  have hx' : L.low ≤ L.inv y + (t - y) / L.cdf (L.inv y) :=
    le_add_of_le_of_nonneg (L.low_le_inv y) (div_nonneg (sub_nonneg.mpr hyt) hc.le)
  have hramp : L.ramp (L.inv y + (t - y) / L.cdf (L.inv y)) = t := by
    rw [ht, L.ramp_inv hy, mul_div_cancel₀ _ hc.ne']
    ring
  calc L.inv t = L.inv (L.ramp (L.inv y + (t - y) / L.cdf (L.inv y))) := by rw [hramp]
    _ = L.inv y + (t - y) / L.cdf (L.inv y) := L.inv_ramp hx'
    _ = L.inv y + (t - y) * L.slope y := by rw [ConsistentSubmodular.Shadow.LeftLaw.slope, mul_one_div]

end
