-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.uniform_demand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:37.489507+00:00
-- url     : https://prove2.me/submissions/28fe551b-a537-4676-b053-6047a02ad38c

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families

open MeasureTheory ProbabilityTheory
open CohenPriceFairness.LocalWelfare

theorem solution {b p : ℝ} (hb : 0 < b) (hp : 0 ≤ p) :
    ((uniformLaw b) (Set.Ici p)).toReal = max 0 (1 - p / b) := by
  unfold uniformLaw
  rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ici, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hb.le]
  rcases le_or_gt p b with hpb | hpb
  · have : Set.Ici p ∩ Set.Icc 0 b = Set.Icc p b := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]; constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, hp.trans h1, h3⟩
    rw [this, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
    rw [max_eq_right (by rw [sub_nonneg, div_le_one hb]; exact hpb)]
    field_simp
  · have : Set.Ici p ∩ Set.Icc 0 b = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨h1, -, h3⟩; linarith
    rw [this, measure_empty, ENNReal.toReal_zero, mul_zero,
      max_eq_left (by rw [sub_nonpos, one_le_div hb]; exact hpb.le)]
