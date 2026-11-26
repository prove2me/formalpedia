-- Prove2me | solution 1 for BBSamplingDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:10.191136+00:00
-- url     : https://prove2.me/submissions/9171febd-0653-4de6-abdf-63a3eccc5079

import Definitions.Def_Tablet_SLLNCurves
import Definitions.Def_Tablet_CountableDiagonalExtraction
import Definitions.Def_Tablet_EtaRepeats
import Definitions.Def_Tablet_EtaRepeatsTilde
import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_PsiMeasurable
import Definitions.Def_Tablet_PsiTildeMeasurable
import Definitions.Def_Tablet_PsiUniformBound
import Definitions.Def_Tablet_PsiTildeUniformBound
import Definitions.Def_Tablet_CurveScaledEvalMeasurable
import Definitions.Def_Tablet_BBSamplingDiagonal
import Theorems.Thm_CountableDiagonalExtraction
import Theorems.Thm_CurveScaledEvalMeasurable
import Theorems.Thm_EtaRepeats
import Theorems.Thm_EtaRepeatsTilde
import Theorems.Thm_PsiMeasurable
import Theorems.Thm_PsiTildeMeasurable
import Theorems.Thm_PsiTildeUniformBound
import Theorems.Thm_PsiUniformBound
import Theorems.Thm_SLLNCurves


set_option autoImplicit false
open MeasureTheory Filter Finset ENNReal
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (F : PSFamily T) (hT0 : F.massMeasure Set.univ ≠ 0)
    (om : ℕ → Form1 E) (x0 : E)
    (D : Set E) (hDc : D.Countable) (hDne : D.Nonempty) (hDd : Dense D) :
    ∃ n : ℕ → ℕ, (∀ l : ℕ, 0 < n l) ∧ Tendsto n atTop atTop ∧
    ∃ γ : ℕ → ℕ → Curve E,
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, (γ l i).len = (l : ℝ)) ∧
      (∀ l : ℕ, 1 ≤ l → ∀ i < n l, massOfFunctional (curveCurrent (γ l i)) = (l : ℝ≥0∞)) ∧
      (∀ k : ℕ, Tendsto (fun l : ℕ =>
          (F.massMeasure Set.univ).toReal / ((n l : ℝ) * l) *
            ∑ i ∈ Finset.range (n l), curveCurrent (γ l i) (om k))
          atTop (nhds (T (om k)))) ∧
      (∀ r : ℚ, 0 < r →
        Tendsto (fun l : ℕ =>
            (1 / (n l : ℝ)) * ∑ i ∈ Finset.range (n l),
              (if (r : ℝ) ≤ dist ((γ l i).toFun 0) x0 then (1 : ℝ) else 0))
          atTop
          (nhds ((F.massMeasure Set.univ).toReal⁻¹ *
            (F.massMeasure {x : E | (r : ℝ) ≤ dist x x0}).toReal))
        ∧
        Tendsto (fun l : ℕ =>
            (1 / (n l : ℝ)) * ∑ i ∈ Finset.range (n l),
              (if (r : ℝ) ≤ dist ((γ l i).toFun (γ l i).len) x0 then (1 : ℝ) else 0))
          atTop
          (nhds ((F.massMeasure Set.univ).toReal⁻¹ *
            (F.massMeasure {x : E | (r : ℝ) ≤ dist x x0}).toReal))) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ Q : Finset E, Q.Nonempty → (Q : Set E) ⊆ D →
        ∀ ε C : ℚ, 0 < ε → 0 < C →
          Tendsto (fun l : ℕ =>
              (1 / ((n l : ℝ) * l)) *
                ∑ i ∈ Finset.range (n l), psi (m * l) Q (ε : ℝ) (C : ℝ) (γ l i))
            atTop
            (nhds ((F.massMeasure Set.univ).toReal⁻¹ *
              ∫ c, psi m Q (ε : ℝ) (C : ℝ) c ∂(F.eta 1)))
          ∧
          Tendsto (fun l : ℕ =>
              (1 / ((n l : ℝ) * l)) *
                ∑ i ∈ Finset.range (n l), psiTilde (m * l) Q (ε : ℝ) (C : ℝ) (γ l i))
            atTop
            (nhds ((F.massMeasure Set.univ).toReal⁻¹ *
              ∫ c, psiTilde m Q (ε : ℝ) (C : ℝ) c ∂(F.eta 1)))) := by
-- BODY
  classical
  have hMfin : IsFiniteMeasure F.massMeasure := F.massMeasure_finite
  have hMtop : F.massMeasure Set.univ ≠ ⊤ := measure_ne_top _ _
  set MR : ℝ := (F.massMeasure Set.univ).toReal with hMRdef
  have hMR : MR ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hT0, hMtop⟩
  -- Step 1: `η_l(Θ(E)) = μ_T(E)` for every `l ≥ 1`.
  have hetaM : ∀ l : ℕ, 1 ≤ l → F.eta l Set.univ = F.massMeasure Set.univ := by
    intro l hl
    have h := (F.massMarginal l hl (fun _ => (1:ℝ≥0∞)) measurable_const).1
    simp only [MeasureTheory.lintegral_const, one_mul] at h
    exact h.symm
  have hetaMR : ∀ l : ℕ, 1 ≤ l → (F.eta l Set.univ).toReal = MR := by
    intro l hl; rw [hetaM l hl]
  have hetane : ∀ l : ℕ, 1 ≤ l → F.eta l Set.univ ≠ 0 := by
    intro l hl; rw [hetaM l hl]; exact hT0
  -- an enumeration of `D`
  obtain ⟨fD, hfD⟩ := hDc.exists_eq_range hDne
  have hQsurj : ∀ Q : Finset E, (Q : Set E) ⊆ D → ∃ s : Finset ℕ, s.image fD = Q := by
    intro Q hQ
    have hmem : ∀ x ∈ Q, ∃ k : ℕ, fD k = x := by
      intro x hx
      have hxD : x ∈ D := hQ hx
      rw [hfD] at hxD
      exact hxD
    choose kk hkk using hmem
    refine ⟨Q.attach.image (fun x => kk x.1 x.2), ?_⟩
    rw [Finset.image_image]
    have hcomp : (fD ∘ fun x : {y // y ∈ Q} => kk x.1 x.2) = fun x : {y // y ∈ Q} => x.1 := by
      funext x; exact hkk x.1 x.2
    rw [hcomp]
    exact Finset.attach_image_val
  -- the countable index set
  obtain ⟨e, he⟩ := exists_surjective_nat ((ℚ × Bool) ⊕ ((ℕ × Finset ℕ × ℚ × ℚ) × Bool))
  -- Step 2: the countable auxiliary family `g l p`, at each stage `l`.
  obtain ⟨g, hgb, hge, hgp, hgt⟩ :
      ∃ g : ℕ → ℕ → Curve E → ℝ,
        (∀ (l p : ℕ) (r : ℚ), e p = Sum.inl (r, true) →
            g l p = fun γ : Curve E =>
              if (r:ℝ) ≤ dist (γ.toFun 0) x0 then (1:ℝ) else 0) ∧
        (∀ (l p : ℕ) (r : ℚ), e p = Sum.inl (r, false) →
            g l p = fun γ : Curve E =>
              if (r:ℝ) ≤ dist (γ.toFun γ.len) x0 then (1:ℝ) else 0) ∧
        (∀ (l p mm : ℕ) (s : Finset ℕ) (ee cc : ℚ), e p = Sum.inr ((mm, s, ee, cc), true) →
            g l p = fun γ : Curve E =>
              if 0 < mm ∧ 0 < ee ∧ 0 < cc then
                (l:ℝ)⁻¹ * psi (mm * l) (s.image fD) (ee:ℝ) (cc:ℝ) γ else 0) ∧
        (∀ (l p mm : ℕ) (s : Finset ℕ) (ee cc : ℚ), e p = Sum.inr ((mm, s, ee, cc), false) →
            g l p = fun γ : Curve E =>
              if 0 < mm ∧ 0 < ee ∧ 0 < cc then
                (l:ℝ)⁻¹ * psiTilde (mm * l) (s.image fD) (ee:ℝ) (cc:ℝ) γ else 0) := by
    refine ⟨fun l p => Sum.elim
      (fun x : ℚ × Bool => fun γ : Curve E =>
        if (x.1:ℝ) ≤ dist (γ.toFun (cond x.2 0 γ.len)) x0 then (1:ℝ) else 0)
      (fun y : (ℕ × Finset ℕ × ℚ × ℚ) × Bool => fun γ : Curve E =>
        if 0 < y.1.1 ∧ 0 < y.1.2.2.1 ∧ 0 < y.1.2.2.2 then
          (l:ℝ)⁻¹ * cond y.2 (psi (y.1.1 * l) ((y.1.2.1).image fD) (y.1.2.2.1:ℝ) (y.1.2.2.2:ℝ) γ)
            (psiTilde (y.1.1 * l) ((y.1.2.1).image fD) (y.1.2.2.1:ℝ) (y.1.2.2.2:ℝ) γ)
        else 0)
      (e p), ?_, ?_, ?_, ?_⟩
    · intro l p r hp; beta_reduce; rw [hp]; rfl
    · intro l p r hp; beta_reduce; rw [hp]; rfl
    · intro l p mm s ee cc hp; beta_reduce; rw [hp]; rfl
    · intro l p mm s ee cc hp; beta_reduce; rw [hp]; rfl
  -- measurability of every member of the family
  have hev0 : Measurable (fun γ : Curve E => γ.toFun 0) := by
    simpa using CurveScaledEvalMeasurable (E := E) (0:ℝ)
  have hevL : Measurable (fun γ : Curve E => γ.toFun γ.len) := by
    simpa using CurveScaledEvalMeasurable (E := E) (1:ℝ)
  have hdist : Measurable (fun x : E => dist x x0) :=
    (continuous_id.dist continuous_const).measurable
  have hgm : ∀ l p, Measurable (g l p) := by
    intro l p
    rcases hp : e p with ⟨r, b⟩ | ⟨⟨mm, s, ee, cc⟩, b⟩
    · cases b with
      | false =>
        rw [hge l p r hp]
        exact Measurable.ite (measurableSet_le measurable_const (hdist.comp hevL))
          measurable_const measurable_const
      | true =>
        rw [hgb l p r hp]
        exact Measurable.ite (measurableSet_le measurable_const (hdist.comp hev0))
          measurable_const measurable_const
    · cases b with
      | false =>
        rw [hgt l p mm s ee cc hp]
        by_cases hadm : 0 < mm ∧ 0 < ee ∧ 0 < cc
        · simp only [if_pos hadm]
          exact measurable_const.mul (PsiTildeMeasurable _ _ _ _)
        · simp only [if_neg hadm]; exact measurable_const
      | true =>
        rw [hgp l p mm s ee cc hp]
        by_cases hadm : 0 < mm ∧ 0 < ee ∧ 0 < cc
        · simp only [if_pos hadm]
          exact measurable_const.mul (PsiMeasurable _ _ _ _)
        · simp only [if_neg hadm]; exact measurable_const
  -- integrability of every member of the family, at every stage `l ≥ 1`
  have hgi : ∀ l : ℕ, 1 ≤ l → ∀ p, Integrable (g l p) (F.eta l) := by
    intro l hl p
    have hfin := F.finite l
    have hlR : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl
    rcases hp : e p with ⟨r, b⟩ | ⟨⟨mm, s, ee, cc⟩, b⟩
    · have hbound : ∀ f : Curve E → ℝ, Measurable f →
          (∀ γ, ‖f γ‖ ≤ (1:ℝ)) → Integrable f (F.eta l) := by
        intro f hf hb
        exact Integrable.mono' (integrable_const (1:ℝ)) hf.aestronglyMeasurable
          (ae_of_all _ hb)
      cases b with
      | false =>
        rw [hge l p r hp]
        refine hbound _ ?_ (fun γ => by split_ifs <;> simp)
        exact Measurable.ite (measurableSet_le measurable_const (hdist.comp hevL))
          measurable_const measurable_const
      | true =>
        rw [hgb l p r hp]
        refine hbound _ ?_ (fun γ => by split_ifs <;> simp)
        exact Measurable.ite (measurableSet_le measurable_const (hdist.comp hev0))
          measurable_const measurable_const
    · cases b with
      | false =>
        rw [hgt l p mm s ee cc hp]
        by_cases hadm : 0 < mm ∧ 0 < ee ∧ 0 < cc
        · simp only [if_pos hadm]
          obtain ⟨hmm, hee, hcc⟩ := hadm
          have hmmR : (0:ℝ) < (mm:ℝ) := by exact_mod_cast hmm
          have hccR : (0:ℝ) ≤ (cc:ℝ) := by exact_mod_cast hcc.le
          have heeR : (0:ℝ) ≤ (ee:ℝ) := by exact_mod_cast hee.le
          refine Integrable.mono'
            (integrable_const (2*(cc:ℝ)^2 + 2*(cc:ℝ)^2/(mm:ℝ)))
            ((measurable_const.mul (PsiTildeMeasurable _ _ _ _)).aestronglyMeasurable) ?_
          filter_upwards [F.lengthExactly l hl] with γ hγ
          obtain ⟨h0, hub⟩ := PsiTildeUniformBound (mm*l) (Nat.mul_pos hmm (by omega))
            (s.image fD) (ee:ℝ) (cc:ℝ) heeR hccR γ
          rw [hγ] at hub
          have hcast : ((mm*l : ℕ):ℝ) = (mm:ℝ)*(l:ℝ) := by push_cast; ring
          rw [hcast] at hub
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) h0)]
          have key : (l:ℝ)⁻¹ * (2*(cc:ℝ)^2*(l:ℝ) + 2*(cc:ℝ)^2*(l:ℝ)^2/((mm:ℝ)*(l:ℝ)))
              = 2*(cc:ℝ)^2 + 2*(cc:ℝ)^2/(mm:ℝ) := by
            field_simp
          calc (l:ℝ)⁻¹ * psiTilde (mm*l) (s.image fD) (ee:ℝ) (cc:ℝ) γ
              ≤ (l:ℝ)⁻¹ * (2*(cc:ℝ)^2*(l:ℝ) + 2*(cc:ℝ)^2*(l:ℝ)^2/((mm:ℝ)*(l:ℝ))) :=
                mul_le_mul_of_nonneg_left hub (by positivity)
            _ = 2*(cc:ℝ)^2 + 2*(cc:ℝ)^2/(mm:ℝ) := key
        · simp only [if_neg hadm]; exact integrable_zero _ _ _
      | true =>
        rw [hgp l p mm s ee cc hp]
        by_cases hadm : 0 < mm ∧ 0 < ee ∧ 0 < cc
        · simp only [if_pos hadm]
          obtain ⟨hmm, hee, hcc⟩ := hadm
          have hmmR : (0:ℝ) < (mm:ℝ) := by exact_mod_cast hmm
          have hccR : (0:ℝ) ≤ (cc:ℝ) := by exact_mod_cast hcc.le
          have heeR : (0:ℝ) ≤ (ee:ℝ) := by exact_mod_cast hee.le
          refine Integrable.mono'
            (integrable_const (2*(cc:ℝ)^2 + 2*(cc:ℝ)^2/(mm:ℝ)))
            ((measurable_const.mul (PsiMeasurable _ _ _ _)).aestronglyMeasurable) ?_
          filter_upwards [F.lengthExactly l hl] with γ hγ
          obtain ⟨h0, hub⟩ := PsiUniformBound (mm*l) (Nat.mul_pos hmm (by omega))
            (s.image fD) (ee:ℝ) (cc:ℝ) heeR hccR γ
          rw [hγ] at hub
          have hcast : ((mm*l : ℕ):ℝ) = (mm:ℝ)*(l:ℝ) := by push_cast; ring
          rw [hcast] at hub
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) h0)]
          have key : (l:ℝ)⁻¹ * (2*(cc:ℝ)^2*(l:ℝ) + 2*(cc:ℝ)^2*(l:ℝ)^2/((mm:ℝ)*(l:ℝ)))
              = 2*(cc:ℝ)^2 + 2*(cc:ℝ)^2/(mm:ℝ) := by
            field_simp
          calc (l:ℝ)⁻¹ * psi (mm*l) (s.image fD) (ee:ℝ) (cc:ℝ) γ
              ≤ (l:ℝ)⁻¹ * (2*(cc:ℝ)^2*(l:ℝ) + 2*(cc:ℝ)^2*(l:ℝ)^2/((mm:ℝ)*(l:ℝ))) :=
                mul_le_mul_of_nonneg_left hub (by positivity)
            _ = 2*(cc:ℝ)^2 + 2*(cc:ℝ)^2/(mm:ℝ) := key
        · simp only [if_neg hadm]; exact integrable_zero _ _ _
  -- the `l`-independence of the stage integrals
  have hSmeas : ∀ r : ℚ, MeasurableSet {x : E | (r:ℝ) ≤ dist x x0} := fun r =>
    measurableSet_le measurable_const hdist
  have hphimeas : ∀ r : ℚ, Measurable (fun x : E => if (r:ℝ) ≤ dist x x0 then (1:ℝ≥0∞) else 0) :=
    fun r => Measurable.ite (hSmeas r) measurable_const measurable_const
  have hlintphi : ∀ r : ℚ, ∫⁻ x, (if (r:ℝ) ≤ dist x x0 then (1:ℝ≥0∞) else 0) ∂F.massMeasure
      = F.massMeasure {x : E | (r:ℝ) ≤ dist x x0} := by
    intro r
    have hrw : (fun x : E => if (r:ℝ) ≤ dist x x0 then (1:ℝ≥0∞) else 0)
        = Set.indicator {x : E | (r:ℝ) ≤ dist x x0} 1 := by
      funext x; simp [Set.indicator_apply]
    rw [hrw, lintegral_indicator_one (hSmeas r)]
  have hbochner : ∀ (μ : Measure (Curve E)) (h : Curve E → E), Measurable h → ∀ r : ℚ,
      ∫ γ, (if (r:ℝ) ≤ dist (h γ) x0 then (1:ℝ) else 0) ∂μ
        = (∫⁻ γ, (if (r:ℝ) ≤ dist (h γ) x0 then (1:ℝ≥0∞) else 0) ∂μ).toReal := by
    intro μ h hh r
    have hdh : Measurable (fun γ : Curve E => dist (h γ) x0) := hdist.comp hh
    have hmeas : Measurable (fun γ : Curve E => if (r:ℝ) ≤ dist (h γ) x0 then (1:ℝ) else 0) :=
      Measurable.ite (measurableSet_le measurable_const hdh) measurable_const measurable_const
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (fun γ : Curve E => by split_ifs <;> simp))
      hmeas.aestronglyMeasurable]
    congr 1
    refine lintegral_congr (fun γ => ?_)
    split_ifs <;> simp
  have hindb : ∀ l : ℕ, 1 ≤ l → ∀ r : ℚ,
      ∫ γ, (if (r:ℝ) ≤ dist (γ.toFun 0) x0 then (1:ℝ) else 0) ∂(F.eta l)
        = (F.massMeasure {x : E | (r:ℝ) ≤ dist x x0}).toReal := by
    intro l hl r
    rw [hbochner (F.eta l) (fun γ => γ.toFun 0) hev0 r]
    congr 1
    have hm := (F.massMarginal l hl
      (fun x => if (r:ℝ) ≤ dist x x0 then (1:ℝ≥0∞) else 0) (hphimeas r)).1
    rw [hlintphi r] at hm
    exact hm.symm
  have hinde : ∀ l : ℕ, 1 ≤ l → ∀ r : ℚ,
      ∫ γ, (if (r:ℝ) ≤ dist (γ.toFun γ.len) x0 then (1:ℝ) else 0) ∂(F.eta l)
        = (F.massMeasure {x : E | (r:ℝ) ≤ dist x x0}).toReal := by
    intro l hl r
    rw [hbochner (F.eta l) (fun γ => γ.toFun γ.len) hevL r]
    congr 1
    have hm := (F.massMarginal l hl
      (fun x => if (r:ℝ) ≤ dist x x0 then (1:ℝ≥0∞) else 0) (hphimeas r)).2
    rw [hlintphi r] at hm
    exact hm.symm
  have hI : ∀ l : ℕ, 1 ≤ l → ∀ p, ∫ c, g l p c ∂(F.eta l) = ∫ c, g 1 p c ∂(F.eta 1) := by
    intro l hl p
    rcases hp : e p with ⟨r, b⟩ | ⟨⟨mm, s, ee, cc⟩, b⟩
    · cases b with
      | false => rw [hge l p r hp, hge 1 p r hp, hinde l hl r, hinde 1 le_rfl r]
      | true => rw [hgb l p r hp, hgb 1 p r hp, hindb l hl r, hindb 1 le_rfl r]
    · cases b with
      | false =>
        rw [hgt l p mm s ee cc hp, hgt 1 p mm s ee cc hp]
        by_cases hadm : 0 < mm ∧ 0 < ee ∧ 0 < cc
        · simp only [if_pos hadm]
          obtain ⟨hmm, hee, hcc⟩ := hadm
          rw [EtaRepeatsTilde T F mm hmm (s.image fD) (ee:ℝ) (cc:ℝ)
              (by exact_mod_cast hee) (by exact_mod_cast hcc) l (by omega),
            EtaRepeatsTilde T F mm hmm (s.image fD) (ee:ℝ) (cc:ℝ)
              (by exact_mod_cast hee) (by exact_mod_cast hcc) 1 one_pos]
        · simp only [if_neg hadm]; simp
      | true =>
        rw [hgp l p mm s ee cc hp, hgp 1 p mm s ee cc hp]
        by_cases hadm : 0 < mm ∧ 0 < ee ∧ 0 < cc
        · simp only [if_pos hadm]
          obtain ⟨hmm, hee, hcc⟩ := hadm
          rw [EtaRepeats T F mm hmm (s.image fD) (ee:ℝ) (cc:ℝ)
              (by exact_mod_cast hee) (by exact_mod_cast hcc) l (by omega),
            EtaRepeats T F mm hmm (s.image fD) (ee:ℝ) (cc:ℝ)
              (by exact_mod_cast hee) (by exact_mod_cast hcc) 1 one_pos]
        · simp only [if_neg hadm]; simp
  -- Step 3: the strong law at every stage `l ≥ 1`
  have hex : ∀ L : ℕ, ∃ Γ : ℕ → Curve E,
      (∀ i, (Γ i).len = ((L+1 : ℕ) : ℝ)) ∧
      (∀ i, massOfFunctional (curveCurrent (Γ i)) = ((L+1 : ℕ) : ℝ≥0∞)) ∧
      (∀ k, Tendsto (fun n : ℕ =>
          (F.eta (L+1) Set.univ).toReal / ((n : ℝ) * ((L+1 : ℕ) : ℝ)) *
            ∑ i ∈ Finset.range n, curveCurrent (Γ i) (om k))
          atTop (nhds (T (om k)))) ∧
      (∀ p, Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, g (L+1) p (Γ i)) / (n : ℝ)) atTop
        (nhds ((F.eta (L+1) Set.univ).toReal⁻¹ * ∫ c, g (L+1) p c ∂(F.eta (L+1))))) := by
    intro L
    exact SLLNCurves T F (L+1) (by omega) (hetane (L+1) (by omega)) om (g (L+1))
      (fun p => hgm (L+1) p) (fun p => hgi (L+1) (by omega) p)
  choose Γ hΓlen hΓmass hΓcur hΓg using hex
  have hsh : ∀ l : ℕ, 1 ≤ l → (l - 1) + 1 = l := by omega
  have hGlen : ∀ l : ℕ, 1 ≤ l → ∀ i, (Γ (l-1) i).len = (l:ℝ) := by
    intro l hl i; have h := hΓlen (l-1) i; rw [hsh l hl] at h; exact h
  have hGmass : ∀ l : ℕ, 1 ≤ l → ∀ i,
      massOfFunctional (curveCurrent (Γ (l-1) i)) = (l : ℝ≥0∞) := by
    intro l hl i; have h := hΓmass (l-1) i; rw [hsh l hl] at h; exact h
  have hGcur : ∀ l : ℕ, 1 ≤ l → ∀ k, Tendsto (fun n : ℕ =>
      MR / ((n : ℝ) * (l : ℝ)) * ∑ i ∈ Finset.range n, curveCurrent (Γ (l-1) i) (om k))
      atTop (nhds (T (om k))) := by
    intro l hl k; have h := hΓcur (l-1) k; rw [hsh l hl] at h
    rwa [hetaMR l hl] at h
  have hGg : ∀ l : ℕ, 1 ≤ l → ∀ p, Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range n, g l p (Γ (l-1) i)) / (n : ℝ)) atTop
      (nhds (MR⁻¹ * ∫ c, g 1 p c ∂(F.eta 1))) := by
    intro l hl p; have h := hΓg (l-1) p; rw [hsh l hl] at h
    rwa [hetaMR l hl, hI l hl p] at h
  -- Step 4: the merged, `l`-independent target limits
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ → ℝ, A = fun (j : ℕ) => if j % 2 = 0 then T (om (j/2))
      else MR⁻¹ * ∫ c, g 1 (j/2) c ∂(F.eta 1) := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a : ℕ → ℕ → ℕ → ℝ, a = fun (j l n : ℕ) =>
      if 1 ≤ l then
        (if j % 2 = 0 then
          MR / (((n:ℝ)+1) * (l:ℝ)) *
            ∑ i ∈ Finset.range (n+1), curveCurrent (Γ (l-1) i) (om (j/2))
        else (∑ i ∈ Finset.range (n+1), g l (j/2) (Γ (l-1) i)) / ((n:ℝ)+1))
      else A j := ⟨_, rfl⟩
  have haEven : ∀ j l n : ℕ, 1 ≤ l → j % 2 = 0 → a j l n =
      MR / (((n:ℝ)+1) * (l:ℝ)) *
        ∑ i ∈ Finset.range (n+1), curveCurrent (Γ (l-1) i) (om (j/2)) := by
    intro j l n hl hj; rw [hadef]; simp only [if_pos hl, if_pos hj]
  have haOdd : ∀ j l n : ℕ, 1 ≤ l → j % 2 ≠ 0 → a j l n =
      (∑ i ∈ Finset.range (n+1), g l (j/2) (Γ (l-1) i)) / ((n:ℝ)+1) := by
    intro j l n hl hj; rw [hadef]; simp only [if_pos hl, if_neg hj]
  have ha : ∀ j l, Tendsto (a j l) atTop (nhds (A j)) := by
    intro j l
    by_cases hl : 1 ≤ l
    · by_cases hj : j % 2 = 0
      · have hA : A j = T (om (j/2)) := by rw [hAdef]; simp only [if_pos hj]
        rw [hA]
        refine ((hGcur l hl (j/2)).comp (tendsto_add_atTop_nat 1)).congr (fun n => ?_)
        rw [haEven j l n hl hj]
        simp only [Function.comp_apply]
        push_cast
        ring
      · have hA : A j = MR⁻¹ * ∫ c, g 1 (j/2) c ∂(F.eta 1) := by
          rw [hAdef]; simp only [if_neg hj]
        rw [hA]
        refine ((hGg l hl (j/2)).comp (tendsto_add_atTop_nat 1)).congr (fun n => ?_)
        rw [haOdd j l n hl hj]
        simp only [Function.comp_apply]
        push_cast
        ring
    · have hcst : a j l = fun _ : ℕ => A j := by
        funext n; rw [hadef]; simp only [if_neg hl]
      rw [hcst]
      exact tendsto_const_nhds
  -- Step 5: diagonalize
  obtain ⟨N, hNmono, hNlim⟩ := CountableDiagonalExtraction a A ha
  refine ⟨fun l => N l + 1, fun l => Nat.succ_pos _,
    tendsto_atTop_mono (fun l => Nat.le_succ (N l)) hNmono.tendsto_atTop,
    fun l i => Γ (l-1) i, fun l hl i _ => hGlen l hl i, fun l hl i _ => hGmass l hl i,
    ?_, ?_, ?_⟩
  · -- (I)
    intro k
    have h1 : (2*k) % 2 = 0 := by omega
    have h2 : (2*k) / 2 = k := by omega
    have h := hNlim (2*k)
    have hA : A (2*k) = T (om k) := by rw [hAdef]; simp only [if_pos h1, h2]
    rw [hA] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with l hl
    rw [haEven (2*k) l (N l) hl h1, h2]
    push_cast
    ring
  · -- (II)
    intro r hr
    obtain ⟨pb, hpb⟩ := he (Sum.inl (r, true))
    obtain ⟨pe, hpe⟩ := he (Sum.inl (r, false))
    constructor
    · have h1 : (2*pb+1) % 2 ≠ 0 := by omega
      have h2 : (2*pb+1) / 2 = pb := by omega
      have h := hNlim (2*pb+1)
      have hA : A (2*pb+1) = MR⁻¹ * (F.massMeasure {x : E | (r:ℝ) ≤ dist x x0}).toReal := by
        rw [hAdef]; simp only [if_neg h1, h2, hgb 1 pb r hpb, hindb 1 le_rfl r]
      rw [hA] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with l hl
      rw [haOdd (2*pb+1) l (N l) hl h1, h2]
      simp only [hgb l pb r hpb]
      push_cast
      ring
    · have h1 : (2*pe+1) % 2 ≠ 0 := by omega
      have h2 : (2*pe+1) / 2 = pe := by omega
      have h := hNlim (2*pe+1)
      have hA : A (2*pe+1) = MR⁻¹ * (F.massMeasure {x : E | (r:ℝ) ≤ dist x x0}).toReal := by
        rw [hAdef]; simp only [if_neg h1, h2, hge 1 pe r hpe, hinde 1 le_rfl r]
      rw [hA] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with l hl
      rw [haOdd (2*pe+1) l (N l) hl h1, h2]
      simp only [hge l pe r hpe]
      push_cast
      ring
  · -- (III)
    intro m hm Q hQne hQD ε C hε hC
    obtain ⟨s, hs⟩ := hQsurj Q hQD
    obtain ⟨p1, hp1⟩ := he (Sum.inr ((m, s, ε, C), true))
    obtain ⟨p2, hp2⟩ := he (Sum.inr ((m, s, ε, C), false))
    have hmpos : 0 < m := hm
    have hadm : 0 < m ∧ 0 < ε ∧ 0 < C := ⟨hmpos, hε, hC⟩
    have hεR : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
    have hCR : (0:ℝ) < (C:ℝ) := by exact_mod_cast hC
    constructor
    · have h1 : (2*p1+1) % 2 ≠ 0 := by omega
      have h2 : (2*p1+1) / 2 = p1 := by omega
      have h := hNlim (2*p1+1)
      have hA : A (2*p1+1) = MR⁻¹ * ∫ c, psi m Q (ε:ℝ) (C:ℝ) c ∂(F.eta 1) := by
        rw [hAdef]
        simp only [if_neg h1, h2, hgp 1 p1 m s ε C hp1, hs, if_pos hadm]
        rw [EtaRepeats T F m hmpos Q (ε:ℝ) (C:ℝ) hεR hCR 1 one_pos]
      rw [hA] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with l hl
      rw [haOdd (2*p1+1) l (N l) hl h1, h2]
      simp only [hgp l p1 m s ε C hp1, hs, if_pos hadm]
      rw [← Finset.mul_sum]
      have hlne : (l:ℝ) ≠ 0 := by
        have hpos : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl
        exact ne_of_gt hpos
      have hnne : ((N l:ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
    · have h1 : (2*p2+1) % 2 ≠ 0 := by omega
      have h2 : (2*p2+1) / 2 = p2 := by omega
      have h := hNlim (2*p2+1)
      have hA : A (2*p2+1) = MR⁻¹ * ∫ c, psiTilde m Q (ε:ℝ) (C:ℝ) c ∂(F.eta 1) := by
        rw [hAdef]
        simp only [if_neg h1, h2, hgt 1 p2 m s ε C hp2, hs, if_pos hadm]
        rw [EtaRepeatsTilde T F m hmpos Q (ε:ℝ) (C:ℝ) hεR hCR 1 one_pos]
      rw [hA] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with l hl
      rw [haOdd (2*p2+1) l (N l) hl h1, h2]
      simp only [hgt l p2 m s ε C hp2, hs, if_pos hadm]
      rw [← Finset.mul_sum]
      have hlne : (l:ℝ) ≠ 0 := by
        have hpos : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl
        exact ne_of_gt hpos
      have hnne : ((N l:ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
