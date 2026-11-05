-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_survival_event_expected_grid_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T21:41:12.893899+00:00
-- url     : https://prove2.me/submissions/7e24bf5a-82e7-4a61-870a-00b91f6ae857

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_closed_grid_full_w_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Source-exact pre-ruin event restriction: no almost-sure survival of
   an unstopped original process is assumed. The expected source sign
   remains a separate genuine compensation/HJB obligation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Live : Ω → Prop := fun ω =>
      (u n : ℝ≥0∞) < ruinTime X x D ω
    let Y : Ω → ℝ≥0 → ℝ := fun ω t =>
      x + X.X t ω - rightLimit D t ω
    let Z : Ω → ℕ → ℝ := fun ω i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    let CashTerm : Ω → ℝ := fun ω => if Live ω then
      E (u n) * w (Y ω (u n)) +
        (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal
      else 0
    let Source : Ω → ℝ := fun ω => if Live ω then
      ∑ i ∈ Finset.range n,
        ((E (u (i + 1)) - E (u i)) * V (Y ω (u (i + 1))) +
          E (u i) * (V (Z ω i) - V (Y ω (u i))))
      else 0
    Integrable CashTerm P →
      Integrable Source P →
      Integrable (fun ω : Ω => if Live ω then w x else 0) P →
      (∫ ω, Source ω ∂P) ≤ 0 →
      (∫ ω, CashTerm ω ∂P) ≤
        (∫ ω : Ω, if Live ω then w x else 0 ∂P) := by
  classical
  intro V E Live Y Z CashTerm Source hCashInt hSourceInt hConstInt hSourceMean
  have hPath : ∀ᵐ ω ∂P,
      CashTerm ω ≤ (if Live ω then w x else 0) + Source ω := by
    apply Filter.Eventually.of_forall
    intro ω
    by_cases hlive : Live ω
    · simp only [CashTerm, Source, if_pos hlive]
      have hPre : ∀ i : ℕ, i < n →
          u (i + 1) = 0 ∨
            (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω := by
        intro i hi
        right
        exact (ENNReal.coe_le_coe.mpr (hu (Nat.succ_le_of_lt hi))).trans_lt hlive
      exact avram_p3_bv_original_closed_grid_full_w_budget
        X x hx C hC hxc q hq w hw_cont hw_smooth hw_grad
        D hD ω u n hu hu0 hPre
    · simp only [CashTerm, Source, if_neg hlive, add_zero, le_refl]
  have hExpected := integral_mono_ae hCashInt (hConstInt.add hSourceInt) hPath
  simp only [Pi.add_apply] at hExpected
  rw [integral_add hConstInt hSourceInt] at hExpected
  linarith
