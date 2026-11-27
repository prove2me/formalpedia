-- Prove2me | solution 1 for BarelyTestable.LowerBound.yao
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:25:01.010549+00:00
-- url     : https://prove2.me/submissions/a3f2c32c-2b75-4bba-9750-8e6933a0229d

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Protocol

set_option autoImplicit false

open BarelyTestable.LowerBound NonmonotoneSubmod.Shared MeasureTheory

namespace BTHelper_yao

/-- Once `run` has produced a decision, more fuel does not change it. -/
theorem run_mono {ι : Type} (A : Procedure ι) (f : Oracle ι) :
    ∀ (k : ℕ) (h : History ι) (b : Bool), (run A f k h).2 = some b →
      ∀ j, (run A f (k + j) h).2 = some b := by
  intro k
  induction k with
  | zero =>
    intro h b hk j
    cases j with
    | zero => simpa using hk
    | succ j =>
      rw [Nat.zero_add]
      simp only [run] at hk ⊢
      cases hA : A h with
      | inl b' => rw [hA] at hk; simpa using hk
      | inr x => rw [hA] at hk; simp at hk
  | succ k ih =>
    intro h b hk j
    rw [Nat.add_right_comm]
    simp only [run] at hk ⊢
    cases hA : A h with
    | inl b' => rw [hA] at hk; simpa using hk
    | inr x =>
      rw [hA] at hk
      simpa using ih _ b hk j

/-- A deterministic procedure cannot both accept and reject the same oracle. -/
theorem not_accepts_and_rejects {ι : Type} (A : Procedure ι) (f : Oracle ι) :
    Accepts A f → ¬ Rejects A f := by
  rintro ⟨k₁, h₁⟩ ⟨k₂, h₂⟩
  have e1 := run_mono A f k₁ [] true h₁ k₂
  have e2 := run_mono A f k₂ [] false h₂ k₁
  rw [Nat.add_comm] at e2
  rw [e1] at e2
  simp at e2

end BTHelper_yao

theorem solution {n : ℕ} (P : Oracle (Fin n) → Prop) (ε η : ℝ)
    (hε : 0 < ε ∧ ε < 1) (hη : 0 < η ∧ η < 1) (q : ℕ)
    {XiYes XiNo : Type} [MeasurableSpace XiYes] [MeasurableSpace XiNo]
    (Dyes : Measure XiYes) (Dno : Measure XiNo) [IsProbabilityMeasure Dyes] [IsProbabilityMeasure Dno]
    (Fyes : XiYes → Oracle (Fin n)) (Fno : XiNo → Oracle (Fin n))
    (hEvalYes : ∀ x, Measurable (fun ξ => Fyes ξ x))
    (hEvalNo : ∀ x, Measurable (fun ξ => Fno ξ x))
    (hyes : ∀ ξ, P (Fyes ξ))
    (hfar_meas : MeasurableSet {ξ | Far P ε (Fno ξ)})
    (hno : 1 - η ≤ Dno.real {ξ | Far P ε (Fno ξ)})
    (hgap : ∀ A : Procedure (Fin n), Budget A q →
      MeasurableSet {ξ | Accepts A (Fyes ξ)} → MeasurableSet {ξ | Accepts A (Fno ξ)} →
        |Dyes.real {ξ | Accepts A (Fyes ξ)} - Dno.real {ξ | Accepts A (Fno ξ)}| < 1/3 - η)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Tester (Fin n) Ω)
    (hjointYes : MeasurableSet {p : Ω × XiYes | Accepts (T.procedure p.1) (Fyes p.2)})
    (hjointNo : MeasurableSet {p : Ω × XiNo | Accepts (T.procedure p.1) (Fno p.2)})
    (hcorrect : Correct μ T P ε) :
    ¬TesterBudget T q := by
  intro hT
  set SY := {p : Ω × XiYes | Accepts (T.procedure p.1) (Fyes p.2)} with hSY
  set SN := {p : Ω × XiNo | Accepts (T.procedure p.1) (Fno p.2)} with hSN
  set F := {ξ | Far P ε (Fno ξ)} with hF
  -- the gap at every seed
  have gap : ∀ ω : Ω, |Dyes.real (Prod.mk ω ⁻¹' SY) - Dno.real (Prod.mk ω ⁻¹' SN)| < 1/3 - η :=
    fun ω => hgap (T.procedure ω) (hT ω) (hjointYes.preimage measurable_prodMk_left)
      (hjointNo.preimage measurable_prodMk_left)
  have hΩ : Nonempty Ω := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := measure_univ (μ := μ)
    rw [Set.univ_eq_empty_iff.mpr hne, measure_empty] at this
    exact zero_ne_one this
  obtain ⟨ω₀⟩ := hΩ
  have hc : 0 < 1/3 - η := lt_of_le_of_lt (abs_nonneg _) (gap ω₀)
  -- Yes side
  have yes_lb : ENNReal.ofReal (2/3) ≤ (μ.prod Dyes) SY := by
    rw [Measure.prod_apply_symm hjointYes]
    calc ENNReal.ofReal (2/3) = ∫⁻ _ : XiYes, ENNReal.ofReal (2/3) ∂Dyes := by simp
      _ ≤ _ := by
        apply lintegral_mono
        intro ξ
        have h1 := hcorrect.1 (Fyes ξ) (hyes ξ)
        show ENNReal.ofReal (2/3) ≤ μ {ω | Accepts (T.procedure ω) (Fyes ξ)}
        rw [← ofReal_measureReal (measure_ne_top _ _)]
        exact ENNReal.ofReal_le_ofReal h1
  -- No side
  have no_ub : (μ.prod Dno) SN ≤ ENNReal.ofReal (1/3) + ENNReal.ofReal η := by
    rw [Measure.prod_apply_symm hjointNo, ← lintegral_add_compl _ hfar_meas]
    gcongr
    · calc ∫⁻ ξ in F, μ ((fun x => (x, ξ)) ⁻¹' SN) ∂Dno
            ≤ ∫⁻ _ in F, ENNReal.ofReal (1/3) ∂Dno := by
              apply setLIntegral_mono' hfar_meas
              intro ξ hξ
              have hR := hcorrect.2 (Fno ξ) hξ
              have hsub : (fun x => (x, ξ)) ⁻¹' SN ⊆
                  {ω | Rejects (T.procedure ω) (Fno ξ)}ᶜ := by
                intro ω hω hr
                exact BTHelper_yao.not_accepts_and_rejects _ _ hω hr
              have hmeasR := T.reject_measurable (Fno ξ)
              have h2 : μ.real ((fun x => (x, ξ)) ⁻¹' SN) ≤ 1/3 := by
                calc μ.real ((fun x => (x, ξ)) ⁻¹' SN)
                    ≤ μ.real {ω | Rejects (T.procedure ω) (Fno ξ)}ᶜ :=
                      measureReal_mono hsub
                  _ = 1 - μ.real {ω | Rejects (T.procedure ω) (Fno ξ)} := by
                      rw [measureReal_compl hmeasR, probReal_univ]
                  _ ≤ 1/3 := by linarith
              rw [← ofReal_measureReal (measure_ne_top _ _)]
              exact ENNReal.ofReal_le_ofReal h2
        _ = ENNReal.ofReal (1/3) * Dno F := by simp
        _ ≤ ENNReal.ofReal (1/3) * 1 := by gcongr; exact prob_le_one
        _ = ENNReal.ofReal (1/3) := mul_one _
    · calc ∫⁻ ξ in Fᶜ, μ ((fun x => (x, ξ)) ⁻¹' SN) ∂Dno
            ≤ ∫⁻ _ in Fᶜ, 1 ∂Dno := by
              apply lintegral_mono
              intro ξ
              exact prob_le_one
        _ = Dno Fᶜ := by simp
        _ ≤ ENNReal.ofReal η := by
              rw [← ofReal_measureReal (measure_ne_top _ _)]
              apply ENNReal.ofReal_le_ofReal
              rw [measureReal_compl hfar_meas, probReal_univ]
              linarith
  -- Seed-wise strict inequality, integrated
  have strict : (μ.prod Dyes) SY < (μ.prod Dno) SN + ENNReal.ofReal (1/3 - η) := by
    rw [Measure.prod_apply hjointYes, Measure.prod_apply hjointNo]
    calc ∫⁻ ω, Dyes (Prod.mk ω ⁻¹' SY) ∂μ
        < ∫⁻ ω, (Dno (Prod.mk ω ⁻¹' SN) + ENNReal.ofReal (1/3 - η)) ∂μ := by
          apply lintegral_strict_mono (IsProbabilityMeasure.ne_zero μ)
            ((measurable_measure_prodMk_left hjointNo).add_const _).aemeasurable
          · rw [← Measure.prod_apply hjointYes]; exact measure_ne_top _ _
          · refine ae_of_all _ (fun ω => ?_)
            have g := gap ω
            have hb : 0 ≤ Dno.real (Prod.mk ω ⁻¹' SN) := measureReal_nonneg
            have ha : 0 ≤ Dyes.real (Prod.mk ω ⁻¹' SY) := measureReal_nonneg
            have hlt : Dyes.real (Prod.mk ω ⁻¹' SY) < Dno.real (Prod.mk ω ⁻¹' SN) + (1/3 - η) := by
              have := (abs_lt.mp g).2
              linarith
            rw [← ofReal_measureReal (measure_ne_top Dyes _),
              ← ofReal_measureReal (measure_ne_top Dno _), ← ENNReal.ofReal_add hb hc.le]
            exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hlt
      _ = ∫⁻ ω, Dno (Prod.mk ω ⁻¹' SN) ∂μ + ∫⁻ _ : Ω, ENNReal.ofReal (1/3 - η) ∂μ :=
          lintegral_add_right _ measurable_const
      _ = _ := by simp
  have hsum : ENNReal.ofReal (1/3) + ENNReal.ofReal η + ENNReal.ofReal (1/3 - η)
      = ENNReal.ofReal (2/3) := by
    rw [← ENNReal.ofReal_add (by norm_num) hη.1.le, ← ENNReal.ofReal_add (by linarith) hc.le]
    congr 1; ring
  have := yes_lb.trans_lt (strict.trans_le (add_le_add no_ub le_rfl))
  rw [hsum] at this
  exact lt_irrefl _ this
