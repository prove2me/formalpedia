-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_all_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:42:02.729472+00:00
-- url     : https://prove2.me/submissions/09d8db8f-a9b5-4ed8-9aa3-a23f80ad8ec6

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Induction
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cutoffEnergyClaim_one_readable

noncomputable section
section S7DTheorem41Compact
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
/-- **The cutoff claim at every order** (BKL (95) for all `m ≥ 2`), by induction from the base case and the step. -/
theorem solution (hL : FunctionalInequalities.KLS.LogConcave.Suspension.LetwinCompactBound) {K : ℝ} (hK : 153 ≤ K)
    (hstep : ∀ m : ℕ, 3 ≤ m →
      (∀ r : ℕ, 2 ≤ r → r < m → FunctionalInequalities.KLS.BKL.Localization.CutoffEnergyClaim K (r - 1)) →
      (∀ r : ℕ, 2 ≤ r → r < m → FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBoundCompact (r - 1) (FunctionalInequalities.KLS.BKL.envelope K r)) →
      FunctionalInequalities.KLS.BKL.Localization.CutoffEnergyClaim K (m - 1))
    (hbound : ∀ d : ℕ, FunctionalInequalities.KLS.BKL.Localization.CutoffEnergyClaim K d → FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBoundCompact d (FunctionalInequalities.KLS.BKL.envelope K (d + 1))) :
    ∀ d : ℕ, 1 ≤ d → FunctionalInequalities.KLS.BKL.Localization.CutoffEnergyClaim K d := by
  intro d
  refine Nat.strong_induction_on d ?_
  intro n ih hn
  by_cases h1 : n = 1
  · subst n
    exact FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_one_readable hL (by linarith)
  · have hn2 : 2 ≤ n := by
      omega
    let m : ℕ := n + 1
    have hm : 3 ≤ m := by
      dsimp [m]
      omega
    have hs : FunctionalInequalities.KLS.BKL.Localization.CutoffEnergyClaim K (m - 1) := by
      apply hstep m hm
      · intro r hr2 hrm
        exact ih (r - 1) (by omega) (by omega)
      · intro r hr2 hrm
        have hclaim : FunctionalInequalities.KLS.BKL.Localization.CutoffEnergyClaim K (r - 1) :=
          ih (r - 1) (by omega) (by omega)
        have hb := hbound (r - 1) hclaim
        rw [Nat.sub_add_cancel (by omega)] at hb
        exact hb
    have hm_sub : m - 1 = n := by
      dsimp [m]
    rw [hm_sub] at hs
    exact hs
