-- Prove2me | solution 1 for AvramDividend.Classical.esscher_levy_shift_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T15:51:58.961567+00:00
-- url     : https://prove2.me/submissions/260f893c-42aa-4ebc-8638-7ee5ad10631e

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_strictly_above_shift
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Strict shifted-exponent increase from source-specific root secants. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q phi : ℝ) (hq : 0 < q) (hphi : 0 < phi)
    (hroot : X.ψ phi = q) :
    StrictMonoOn (fun beta : ℝ => X.ψ (phi + beta) - q) (Ici (0 : ℝ)) := by
  intro a ha b hb hab
  have ha0 : 0 ≤ a := ha
  have hu : 0 < phi + a := by linarith
  have hpos : 0 < X.ψ (phi + a) := by
    by_cases haz : a = 0
    · subst a
      simpa [hroot] using hq
    · have ha_pos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm haz)
      have hψa : q < X.ψ (phi + a) :=
        levy_psi_root_strictly_above_shift X q phi a hq hphi ha_pos hroot
      linarith
  have hd : 0 < b - a := by linarith
  have hlt := levy_psi_root_strictly_above_shift X
    (X.ψ (phi + a)) (phi + a) (b - a) hpos hu hd rfl
  have hadd : (phi + a) + (b - a) = phi + b := by ring
  rw [hadd] at hlt
  exact sub_lt_sub_right hlt q
