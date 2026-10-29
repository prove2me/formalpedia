-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_original_clock_descending_mgf_all_beta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T01:21:23.821445+00:00
-- url     : https://prove2.me/submissions/fa69ec3f-d250-48f9-b96f-06d430433a6a

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_real_finite_strip
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_drawdown_mgf_analytic_positive
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_levy_psi_analytic_on_positive
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_levy_psi_hasDerivAt_positive
import Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_derivative_lower
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_q_root_unique
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_all_beta_wh_analytic_continuation_with_removable_root

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The original independent exponential-clock descending MGF has its
complete positive-parameter Wiener–Hopf transform and removable root. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p) :
    ∃ m : ℝ, 0 < m ∧ HasDerivAt X.ψ m lam ∧
      ∀ β : ℝ, 0 < β →
        mgf (fun z : Ω × ℝ =>
          -(runningSup X (Real.toNNReal z.2) z.1 -
            X.X (Real.toNNReal z.2) z.1))
          (P.prod (expMeasure p)) β =
        if β = lam then p / (lam * m)
        else (p / lam) * ((lam - β) / (p - X.ψ β)) := by
  rcases avram_ws01e_cr_new_levy_psi_hasDerivAt_positive
    X lam hlam with ⟨m, hmDeriv⟩
  have hm : 0 < m :=
    (esscher_levy_positive_root_derivative_lower
      X p lam m hp hlam hroot hmDeriv).2
  let L : ℝ → ℝ := fun β =>
    mgf (fun z : Ω × ℝ =>
      -(runningSup X (Real.toNNReal z.2) z.1 -
        X.X (Real.toNNReal z.2) z.1))
      (P.prod (expMeasure p)) β
  have hLAnalytic : AnalyticOnNhd ℝ L (Set.Ioi 0) := by
    simpa only [L] using
      (avram_ws01e_bt_new_original_clock_drawdown_mgf_analytic_positive
        X p hp)
  have hgAnalytic : AnalyticOnNhd ℝ X.ψ (Set.Ioi 0) :=
    avram_ws01e_bt_new_levy_psi_analytic_on_positive X
  have hgUnique : ∀ t : ℝ, 0 < t → t ≠ lam → X.ψ t ≠ p := by
    intro t ht hne heq
    exact hne (levy_psi_positive_q_root_unique
      X p t lam hp ht hlam heq hroot)
  have hStrip : ∀ t : ℝ, 0 < t → t < lam →
      L t * (p - X.ψ t) = (p / lam) * (lam - t) := by
    intro t ht htlam
    simpa only [L] using
      (avram_ws01e_bt_new_original_clock_descending_real_finite_strip
        X p hp lam hlam hroot t ht htlam)
  have hAll :=
    avram_ws01e_b_all_beta_wh_analytic_continuation_with_removable_root
      p lam m hp hlam hm L X.ψ hLAnalytic hgAnalytic
      hroot hmDeriv hgUnique hStrip
  refine ⟨m, hm, hmDeriv, ?_⟩
  intro β hβ
  simpa only [L] using hAll β hβ
