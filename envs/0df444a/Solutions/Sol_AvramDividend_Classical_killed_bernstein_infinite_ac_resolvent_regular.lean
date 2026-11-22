-- Prove2me | solution 1 for AvramDividend.Classical.killed_bernstein_infinite_ac_resolvent_regular
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T15:47:16.861497+00:00
-- url     : https://prove2.me/submissions/83d662cc-73ae-4ef0-9226-bc6024adab07
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_killed_bernstein_infinite_activity_potential_atom_zero
import Theorems.Thm_AvramDividend_Classical_killed_bernstein_potential_weighted_ac
import Theorems.Thm_AvramDividend_Classical_positive_measure_ac_of_weighted_ac_and_zero_atom
import Theorems.Thm_AvramDividend_Classical_atomless_from_weighted_measure_ac
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution (κ : Measure ℝ) [SFinite κ]
    (hκsupp : κ (Iic (0 : ℝ)) = 0)
    (k : ℝ) (hk : 0 < k)
    (hFin : ∀ s : ℝ, 0 < s →
      (∫⁻ t : ℝ, ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ) ≠ ⊤)
    (hκac : κ ≪ (volume : Measure ℝ))
    (hκinf : κ (Ioc (0 : ℝ) 1) = ⊤)
    (U : Measure ℝ) (hUsupp : U (Iio (0 : ℝ)) = 0)
    (hUmass : U Set.univ = ENNReal.ofReal (k⁻¹))
    (hULap : ∀ s : ℝ, 0 < s →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-(s * y))) ∂U) =
        (ENNReal.ofReal k +
          (∫⁻ t : ℝ,
            ENNReal.ofReal (1 - Real.exp (-(s * t))) ∂κ))⁻¹) :
    U (Iic (0 : ℝ)) = 0 ∧
    U ≪ (volume : Measure ℝ) ∧
    (∀ x : ℝ, U {x} = 0) := by
  have hZero := killed_bernstein_infinite_activity_potential_atom_zero
    κ hκsupp k hk hFin U hUsupp hUmass hULap hκinf
  have hWeighted := killed_bernstein_potential_weighted_ac
    κ hκsupp k hk hFin U hUsupp hUmass hULap hκac
  have hAC := positive_measure_ac_of_weighted_ac_and_zero_atom
    U hUsupp hZero hWeighted
  have hAtoms := atomless_from_weighted_measure_ac
    U hUsupp hZero hWeighted
  have hIic : U (Iic (0 : ℝ)) = 0 := by
    have hSet : Iic (0 : ℝ) =
        Iio (0 : ℝ) ∪ {(0 : ℝ)} := by
      ext x
      simp only [mem_Iic, mem_union, mem_Iio, mem_singleton_iff]
      constructor
      · intro hx
        rcases lt_or_eq_of_le hx with hlt | heq
        · exact Or.inl hlt
        · exact Or.inr heq
      · intro hx
        rcases hx with hlt | heq
        · exact le_of_lt hlt
        · exact heq ▸ le_rfl
    rw [hSet]
    exact measure_union_null hUsupp hZero
  exact ⟨hIic, hAC, hAtoms⟩
