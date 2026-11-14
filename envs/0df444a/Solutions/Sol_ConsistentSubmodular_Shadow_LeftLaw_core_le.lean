-- Prove2me | solution 1 for ConsistentSubmodular.Shadow.LeftLaw.core_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:42:54.337235+00:00
-- url     : https://prove2.me/submissions/1d3481ea-a0bf-4b88-bdb1-f12ea61aaea4

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals
import Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_core

section

noncomputable section

open scoped BigOperators Topology

open MeasureTheory Filter Set

namespace ConsistentSubmodular.Shadow

namespace LeftLaw

variable {ι : Type*} [Fintype ι] (L : LeftLaw ι)

theorem pos_part_sub {a b c : ℝ} (hab : a ≤ b) :
    max 0 (b - c) - max 0 (a - c) = max 0 (b - max a c) := by
  simp only [max_def]
  split_ifs <;> linarith

/-- Fubini (8): `Σ_j p_j |[a, b] ∩ [ℓ_j, ∞)| = H(b) - H(a)`. -/
theorem ramp_sub {a b : ℝ} (hab : a ≤ b) :
    L.ramp b - L.ramp a = ∑ j, L.prob j * max 0 (b - max a (L.left j)) := by
  rw [ramp, ramp, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [← mul_sub, pos_part_sub hab]

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

theorem solution {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hchain : ChainHypothesis α)
    (hlow : 0 ≤ L.low) (r : ι → ℝ) (hr : ∀ j, L.prob j ≠ 0 → L.left j ≤ r j) {M : ℝ}
    (hM : ∀ i, L.prob i ≠ 0 → ∑ j, L.prob j * max 0 (r i - max (L.left i) (L.left j)) ≤ M) :
    α * (L.mean + ∑ j, L.prob j * (r j - L.left j)) ≤ L.mean + M := by
  have hmean : 0 ≤ L.mean := Finset.sum_nonneg fun j _ => by
    by_cases hp : L.prob j = 0
    · simp [hp]
    · exact mul_nonneg (L.prob_nonneg j) (hlow.trans (L.low_le j hp))
  rcases lt_or_ge 0 M with hM0 | hM0
  · -- Divide every endpoint by `M`.
    have hscaled := (L.scale M hM0).core hα0 hα1 hchain (div_nonneg hlow hM0.le)
      (fun j => r j / M) (fun j hj => div_le_div_of_nonneg_right (hr j hj) hM0.le)
      (fun i hi => by
        have hle : L.left i / M ≤ r i / M := div_le_div_of_nonneg_right (hr i hi) hM0.le
        show (L.scale M hM0).ramp (r i / M) - (L.scale M hM0).ramp (L.left i / M) ≤ 1
        rw [(L.scale M hM0).ramp_sub hle]
        calc _ = (∑ j, L.prob j * max 0 (r i - max (L.left i) (L.left j))) / M := by
              rw [Finset.sum_div]
              refine Finset.sum_congr rfl fun j _ => ?_
              simp only [scale]
              rw [max_div_div_right hM0.le, ← sub_div, ← zero_div M,
                max_div_div_right hM0.le, zero_div, mul_div_assoc]
          _ ≤ M / M := div_le_div_of_nonneg_right (hM i hi) hM0.le
          _ = 1 := div_self hM0.ne')
    have hmean' : (L.scale M hM0).mean = L.mean / M := by
      simp only [mean, scale, Finset.sum_div, mul_div_assoc]
    have hC' : ∑ j, (L.scale M hM0).prob j * (r j / M - (L.scale M hM0).left j) =
        (∑ j, L.prob j * (r j - L.left j)) / M := by
      simp only [scale, Finset.sum_div, ← sub_div, mul_div_assoc]
    rw [hmean', hC'] at hscaled
    have h := mul_le_mul_of_nonneg_left hscaled hM0.le
    have e1 : M * (α * (L.mean / M + (∑ j, L.prob j * (r j - L.left j)) / M)) =
        α * (L.mean + ∑ j, L.prob j * (r j - L.left j)) := by
      field_simp
    have e2 : M * (L.mean / M + 1) = L.mean + M := by field_simp
    rw [e1, e2] at h
    exact h
  · -- `M ≤ 0`: every interval of positive probability is a point, so `C = 0`.
    have hpoint : ∀ i, L.prob i ≠ 0 → L.prob i * (r i - L.left i) ≤ M := fun i hi =>
      calc L.prob i * (r i - L.left i)
          = L.prob i * max 0 (r i - max (L.left i) (L.left i)) := by
            rw [max_self, max_eq_right (sub_nonneg.mpr (hr i hi))]
        _ ≤ ∑ j, L.prob j * max 0 (r i - max (L.left i) (L.left j)) :=
            Finset.single_le_sum (f := fun j => L.prob j * max 0 (r i - max (L.left i) (L.left j)))
              (fun j _ => mul_nonneg (L.prob_nonneg j) (le_max_left _ _)) (Finset.mem_univ i)
        _ ≤ M := hM i hi
    have hC : ∑ j, L.prob j * (r j - L.left j) = 0 := Finset.sum_eq_zero fun j _ => by
      by_cases hp : L.prob j = 0
      · simp [hp]
      · exact le_antisymm ((hpoint j hp).trans hM0)
          (mul_nonneg (L.prob_nonneg j) (sub_nonneg.mpr (hr j hp)))
    obtain ⟨i, hi, -⟩ := L.atom
    have hM0' : 0 ≤ M := (Finset.sum_nonneg fun j _ =>
      mul_nonneg (L.prob_nonneg j) (le_max_left _ _)).trans (hM i hi)
    rw [hC, add_zero]
    nlinarith

end
