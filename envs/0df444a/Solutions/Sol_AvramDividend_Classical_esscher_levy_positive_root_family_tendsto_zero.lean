-- Prove2me | solution 1 for AvramDividend.Classical.esscher_levy_positive_root_family_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:03:38.865204+00:00
-- url     : https://prove2.me/submissions/88b3ea65-8ac0-4fbc-9d9e-61c95a593439

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.NhdsWithin
import Mathlib.Order.Monotone.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_esscher_shift_positive_root_of_levy_secant
import Theorems.Thm_AvramDividend_Classical_esscher_levy_shift_strictMonoOn
import Theorems.Thm_AvramDividend_Classical_esscher_root_tendsto_zero_of_strictMonoOn
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- The canonical Lévy shifted roots admit a positive family tending to zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q phi : ℝ) (hq : 0 < q) (hphi : 0 < phi)
    (hroot : X.ψ phi = q) :
    ∃ lambda : ℝ → ℝ,
      (∀ p : ℝ, 0 < p → 0 < lambda p) ∧
      (∀ p : ℝ, 0 < p → X.ψ (phi + lambda p) - q = p) ∧
      Tendsto lambda (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhdsWithin (0 : ℝ) (Ioi 0)) := by
  classical
  let root : ℝ → ℝ := fun p =>
    if hp : 0 < p then
      Classical.choose
        (esscher_shift_positive_root_of_levy_secant X q phi p hq hphi hroot hp)
    else 0
  have hpos : ∀ p : ℝ, 0 < p → 0 < root p := by
    intro p hp
    simp only [root, dif_pos hp]
    exact (Classical.choose_spec
      (esscher_shift_positive_root_of_levy_secant X q phi p hq hphi hroot hp)).1
  have hfamily : ∀ p : ℝ, 0 < p →
      X.ψ (phi + root p) - q = p := by
    intro p hp
    simp only [root, dif_pos hp]
    exact (Classical.choose_spec
      (esscher_shift_positive_root_of_levy_secant X q phi p hq hphi hroot hp)).2
  have hzero :
      (fun beta : ℝ => X.ψ (phi + beta) - q) 0 = 0 := by
    simp [hroot]
  have hmono :
      StrictMonoOn (fun beta : ℝ => X.ψ (phi + beta) - q)
        (Ici (0 : ℝ)) :=
    esscher_levy_shift_strictMonoOn X q phi hq hphi hroot
  have htendsto := esscher_root_tendsto_zero_of_strictMonoOn
    (fun beta : ℝ => X.ψ (phi + beta) - q)
    root hzero hmono hpos hfamily
  exact ⟨root, hpos, hfamily, htendsto⟩
