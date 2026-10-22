-- Prove2me | solution 1 for CondPortOT.SingUninf.condExp_le_sup
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:53:02.239741+00:00
-- url     : https://prove2.me/submissions/2ae8d982-b2d6-4af3-b39b-9d3bdab927b0

import Mathlib
import Definitions.Def_CondPortOT_BigRadius_Setting

set_option autoImplicit false
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

theorem pt_ineq (l t : ℝ) (h : l ≤ t) :
    ENNReal.ofReal l + ENNReal.ofReal (-t) ≤ ENNReal.ofReal t + ENNReal.ofReal (-l) := by
  rcases le_or_gt 0 l with hl | hl
  · have ht : 0 ≤ t := le_trans hl h
    rw [ENNReal.ofReal_of_nonpos (by linarith : -t ≤ 0), ENNReal.ofReal_of_nonpos (by linarith : -l ≤ 0)]
    simpa using ENNReal.ofReal_le_ofReal h
  · rcases le_or_gt 0 t with ht | ht
    · rw [ENNReal.ofReal_of_nonpos hl.le, ENNReal.ofReal_of_nonpos (by linarith : -t ≤ 0)]
      simp
    · rw [ENNReal.ofReal_of_nonpos hl.le, ENNReal.ofReal_of_nonpos ht.le]
      simpa using ENNReal.ofReal_le_ofReal (by linarith : -t ≤ -l)

theorem key {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Q : Measure (X × Y)) [IsProbabilityMeasure Q] (S : Set (X × Y))
    (hQS : 0 < Q S) (L : Y → ℝ) (t : ℝ) (hL : ∀ y, L y ≤ t) :
    CondPortOT.SingUninf.condExp Q S L ≤ (t : EReal) := by
  have hq : Q S ≠ ⊤ := measure_ne_top Q S
  have hqr : 0 < (Q S).toReal := ENNReal.toReal_pos hQS.ne' hq
  have e1 : (fun p : X × Y => ((L p.2 : ℝ) : EReal).toENNReal) = fun p => ENNReal.ofReal (L p.2) := by
    funext p; rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have e2 : (fun p : X × Y => (-((L p.2 : ℝ) : EReal)).toENNReal) = fun p => ENNReal.ofReal (-L p.2) := by
    funext p
    rw [← EReal.coe_neg, EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  unfold CondPortOT.SingUninf.condExp ModelRiskOT.Duality.extIntegral
  rw [e1, e2]
  set A : ENNReal := ∫⁻ p, ENNReal.ofReal (L p.2) ∂(Q.restrict S) with hA
  set B : ENNReal := ∫⁻ p, ENNReal.ofReal (-L p.2) ∂(Q.restrict S) with hB
  have hineq : A + ENNReal.ofReal (-t) * Q S ≤ ENNReal.ofReal t * Q S + B := by
    have h1 : ∫⁻ p, (ENNReal.ofReal (L p.2) + ENNReal.ofReal (-t)) ∂(Q.restrict S)
        ≤ ∫⁻ p, (ENNReal.ofReal t + ENNReal.ofReal (-L p.2)) ∂(Q.restrict S) :=
      lintegral_mono fun p => pt_ineq _ _ (hL p.2)
    rw [lintegral_add_right _ measurable_const, lintegral_add_left measurable_const,
      lintegral_const, lintegral_const, Measure.restrict_apply_univ] at h1
    exact h1
  by_cases hBt : B = ⊤
  · rw [hBt, EReal.coe_ennreal_top, EReal.sub_top, EReal.coe_mul_bot_of_pos]
    · exact bot_le
    · exact inv_pos.mpr hqr
  · have hBf : B ≠ ⊤ := hBt
    have hrhs : ENNReal.ofReal t * Q S + B ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq, hBf⟩
    have hAf : A ≠ ⊤ := by
      intro h
      rw [h, top_add] at hineq
      exact hrhs (top_le_iff.mp hineq)
    have hr := ENNReal.toReal_mono hrhs hineq
    rw [ENNReal.toReal_add hAf (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq),
      ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq) hBf,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal'] at hr
    have hmax : max t 0 - max (-t) 0 = t := by
      rcases le_total 0 t with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    have hdiff : A.toReal - B.toReal ≤ t * (Q S).toReal := by
      have : (max t 0 - max (-t) 0) * (Q S).toReal = t * (Q S).toReal := by rw [hmax]
      nlinarith [hr, this]
    have hc : ((A : EReal) - (B : EReal)) = (((A.toReal - B.toReal : ℝ)) : EReal) := by
      rw [EReal.coe_sub, EReal.coe_ennreal_toReal hAf, EReal.coe_ennreal_toReal hBf]
    rw [hc, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    calc ((Q S).toReal)⁻¹ * (A.toReal - B.toReal) ≤ ((Q S).toReal)⁻¹ * (t * (Q S).toReal) :=
          mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hqr.le)
      _ = t := by field_simp

theorem solution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Q : Measure (X × Y)) [IsProbabilityMeasure Q] (S : Set (X × Y)) (hS : MeasurableSet S)
    (hQS : 0 < Q S) (L : Y → ℝ) :
    CondPortOT.SingUninf.condExp Q S L ≤ ⨆ y, (L y : EReal) := by
  by_contra h
  push Not at h
  obtain ⟨t, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp h
  have hL : ∀ y, L y ≤ t := fun y => by
    have := le_iSup (fun y => (L y : EReal)) y
    exact_mod_cast (this.trans h1.le)
  exact absurd (key Q S hQS L t hL) (not_le.mpr h2)
