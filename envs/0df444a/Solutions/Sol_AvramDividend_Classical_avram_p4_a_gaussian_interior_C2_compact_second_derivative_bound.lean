-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_interior_C2_compact_second_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:46:52.688773+00:00
-- url     : https://prove2.me/submissions/ac8a585d-8505-4ed6-938a-73c6ca6c6787

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

/-- Exact interior C2 regularity bounds the generator's second derivative
on each compact reserve interval strictly inside (0,C). This does not
claim a bound at ruin, at the dividend cap, or globally. -/
theorem solution
    (w : ℝ → ℝ) (C a b : ℝ)
    (ha : 0 < a) (hb : b < C)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C)) :
    ∃ K : ℝ, ∀ y ∈ Icc a b, ‖iteratedDeriv 2 w y‖ ≤ K := by
  have hsub : Icc a b ⊆ Ioo 0 C := by
    intro y hy
    exact ⟨lt_of_lt_of_le ha hy.1, lt_of_le_of_lt hy.2 hb⟩
  have huniq : UniqueDiffOn ℝ (Ioo 0 C) := isOpen_Ioo.uniqueDiffOn
  have hWithin : ContinuousOn (iteratedDerivWithin 2 w (Ioo 0 C))
      (Ioo 0 C) := hw.continuousOn_iteratedDerivWithin (by norm_num) huniq
  have heq : EqOn (iteratedDerivWithin 2 w (Ioo 0 C))
      (iteratedDeriv 2 w) (Ioo 0 C) :=
    iteratedDerivWithin_of_isOpen isOpen_Ioo
  have hcont : ContinuousOn (iteratedDeriv 2 w) (Icc a b) :=
    (hWithin.mono hsub).congr (fun y hy => (heq (hsub hy)).symm)
  exact isCompact_Icc.exists_bound_of_continuousOn hcont
