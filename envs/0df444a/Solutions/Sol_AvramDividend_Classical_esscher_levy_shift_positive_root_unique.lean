-- Prove2me | solution 1 for AvramDividend.Classical.esscher_levy_shift_positive_root_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:29:55.842732+00:00
-- url     : https://prove2.me/submissions/8a24f2b4-2af6-4db1-96f7-e53c3a06988f

import Mathlib.Order.Monotone.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_esscher_shift_positive_root_of_levy_secant
import Theorems.Thm_AvramDividend_Classical_esscher_levy_shift_strictMonoOn
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The positive shifted-root parameter is determined uniquely at every rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q phi p : ℝ) (hq : 0 < q) (hphi : 0 < phi)
    (hroot : X.ψ phi = q) (hp : 0 < p) :
    ∃! lambda : ℝ,
      0 < lambda ∧ X.ψ (phi + lambda) - q = p := by
  obtain ⟨lambda, hpositive, heq⟩ :=
    esscher_shift_positive_root_of_levy_secant
      X q phi p hq hphi hroot hp
  refine ⟨lambda, ⟨hpositive, heq⟩, ?_⟩
  intro mu hmu
  have hmono :
      StrictMonoOn (fun beta : ℝ => X.ψ (phi + beta) - q)
        (Ici (0 : ℝ)) :=
    esscher_levy_shift_strictMonoOn X q phi hq hphi hroot
  have hsame :
      (fun beta : ℝ => X.ψ (phi + beta) - q) mu =
        (fun beta : ℝ => X.ψ (phi + beta) - q) lambda :=
    hmu.2.trans heq.symm
  exact hmono.injOn (le_of_lt hmu.1) (le_of_lt hpositive) hsame
