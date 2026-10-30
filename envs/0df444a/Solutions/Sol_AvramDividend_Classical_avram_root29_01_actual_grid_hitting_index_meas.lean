-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_actual_grid_hitting_index_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:27:41.38021+00:00
-- url     : https://prove2.me/submissions/75413245-4780-4ed4-9a6e-f76f76743890


import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual finite-grid first-outside index for a spectrally negative
Levy path is measurable, using the discrete adapted stopping-time law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω) :
    Measurable K := by
  let Z : ℕ → Ω → ℝ := fun k ω => X.X (clock k) ω
  let Y : ℕ → Ω → ℝ := fun k ω =>
    max (Z k ω - upper) (lower - Z k ω)
  have hZ : Adapted H Z := by
    intro k
    change Measurable[H k] (X.X (clock k))
    rw [hH k]
    exact X.adapted (clock k)
  have hY : Adapted H Y := by
    intro k
    exact ((hZ k).sub measurable_const).max
      (measurable_const.sub (hZ k))
  have hτ : IsStoppingTime H (fun ω => (K ω : WithTop ℕ)) := by
    intro i
    have hhit := (hY.isStoppingTime_hittingBtwn
      (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
      (n := 0) (n' := m)) i
    convert hhit using 1
    ext ω
    simp only [Set.mem_setOf_eq, WithTop.coe_le_coe]
    rw [hK ω]
    change ((hittingBtwn Y (Set.Ioi (0 : ℝ)) 0 m ω : ℕ) : WithTop ℕ) ≤ (i : WithTop ℕ) ↔
      hittingBtwn Y (Set.Ioi (0 : ℝ)) 0 m ω ≤ i
    constructor <;> intro h <;> exact_mod_cast h
  refine measurable_to_countable' (fun k => ?_)
  change MeasurableSet {ω : Ω | K ω = k}
  have hlevel : MeasurableSet
      {ω : Ω | ((K ω : ℕ) : WithTop ℕ) = (k : WithTop ℕ)} := by
    exact hτ.measurableSpace_le _ (hτ.measurableSet_eq' k)
  have hEq : {ω : Ω |
      ((K ω : ℕ) : WithTop ℕ) = (k : WithTop ℕ)} =
      {ω : Ω | K ω = k} := by
    ext ω
    constructor
    · intro h
      exact_mod_cast h
    · intro h
      exact_mod_cast h
  rwa [hEq] at hlevel