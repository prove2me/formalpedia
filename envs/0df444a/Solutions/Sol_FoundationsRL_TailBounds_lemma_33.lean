-- Prove2me | solution 1 for FoundationsRL.TailBounds.lemma_33
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:57:51.399969+00:00
-- url     : https://prove2.me/submissions/b343900b-b5b8-450e-be0d-069503746ebb

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℕ) (Z : ℕ → Ω → ℝ)
    (hindep : iIndepFun (fun i : Finset.Icc 1 T => Z i) μ)
    (hid : ∀ i ∈ Finset.Icc 1 T, IdentDistrib (Z i) (Z 1) μ μ)
    (a b : ℝ) (hab : ∀ i ∈ Finset.Icc 1 T, ∀ᵐ ω ∂μ, Z i ω ∈ Set.Icc a b)
    (δ : ℝ) (hδ : 0 < δ) :
    1 - δ ≤ μ.real {ω | ∀ T' ∈ Finset.Icc 1 T,
        (1 / (T' : ℝ)) * ∑ i ∈ Finset.Icc 1 T', Z i ω - ∫ ω', Z 1 ω' ∂μ ≤
          (b - a) * Real.sqrt (Real.log ((T : ℝ) / δ) / (2 * (T' : ℝ)))} ∧
    ∀ τ : Ω → ℕ, (∀ ω, τ ω ∈ Finset.Icc 1 T) →
      (∀ t ∈ Finset.Icc 1 T,
        MeasurableSet[⨆ i ∈ Finset.Ico 1 t, MeasurableSpace.comap (Z i) inferInstance]
          {ω | τ ω ≤ t}) →
      1 - δ ≤ μ.real {ω |
        (1 / (τ ω : ℝ)) * ∑ i ∈ Finset.Icc 1 (τ ω), Z i ω - ∫ ω', Z 1 ω' ∂μ ≤
          (b - a) * Real.sqrt (Real.log ((T : ℝ) / δ) / (2 * (τ ω : ℝ)))} := by
  classical
  set E := ∫ ω', Z 1 ω' ∂μ with hE
  set r : ℕ → ℝ := fun T' => (b - a) * Real.sqrt (Real.log ((T : ℝ) / δ) / (2 * (T' : ℝ))) with hr
  set G := {ω | ∀ T' ∈ Finset.Icc 1 T, (1 / (T' : ℝ)) * ∑ i ∈ Finset.Icc 1 T', Z i ω - E ≤ r T'}
    with hG
  have hpart1 : 1 - δ ≤ μ.real G := by
    rcases le_or_gt 1 δ with hδ1 | hδ1
    · linarith [measureReal_nonneg (μ := μ) (s := G)]
    rcases Nat.eq_zero_or_pos T with hT0 | hTpos
    · have : G = Set.univ := by
        ext ω; simp only [hG, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        intro T' hT'; rw [hT0] at hT'; simp at hT'
      rw [this, probReal_univ]; linarith
    have h1T : 1 ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨le_refl 1, hTpos⟩
    have haeb : a ≤ b := by
      by_contra hba
      push Not at hba
      have h := hab 1 h1T
      have : ∀ᵐ ω ∂μ, False := by
        filter_upwards [h] with ω hω; exact absurd (hω.1.trans hω.2) (not_le.mpr hba)
      rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot] at this
      exact IsProbabilityMeasure.ne_zero μ this
    have hT : (0:ℝ) < T := by exact_mod_cast hTpos
    have hEi : ∀ i ∈ Finset.Icc 1 T, ∫ ω, Z i ω ∂μ = E := fun i hi => (hid i hi).integral_eq
    -- the complement is covered by the bad events
    have hcover : μ.real Gᶜ ≤ δ := by
      rcases haeb.eq_or_lt with hab_eq | hab_lt
      · -- degenerate: all Z_i = a a.e.
        have hall : ∀ᵐ ω ∂μ, ∀ i ∈ Finset.Icc 1 T, Z i ω = a := by
          rw [Filter.eventually_all_finset]
          intro i hi
          filter_upwards [hab i hi] with ω hω
          rw [← hab_eq] at hω; exact le_antisymm hω.2 hω.1
        have hEa : E = a := by
          rw [hE]
          have : ∀ᵐ ω ∂μ, Z 1 ω = a := by filter_upwards [hall] with ω hω using hω 1 h1T
          rw [integral_congr_ae this]; simp
        have hnull : μ Gᶜ = 0 := by
          apply measure_mono_null _ (ae_iff.mp hall)
          intro ω hω
          simp only [Set.mem_ofPred_eq, not_forall] at hω ⊢
          by_contra hcontra
          push Not at hcontra
          apply hω
          simp only [hG, Set.mem_ofPred_eq]
          intro T' hT'
          have hT'T : Finset.Icc 1 T' ⊆ Finset.Icc 1 T := Finset.Icc_subset_Icc le_rfl
            (Finset.mem_Icc.mp hT').2
          have : ∑ i ∈ Finset.Icc 1 T', Z i ω = T' * a := by
            rw [Finset.sum_congr rfl (fun i hi => hcontra i (hT'T hi))]; simp
          have hT'pos : (0:ℝ) < T' := by exact_mod_cast (Finset.mem_Icc.mp hT').1
          rw [this, hEa, hr]; simp only
          rw [← hab_eq, sub_self, zero_mul]
          field_simp; simp
        rw [measureReal_def, hnull]; simp; linarith
      · set c : NNReal := (‖b - a‖₊ / 2) ^ 2 with hc
        have hcval : (c : ℝ) = (b - a) ^ 2 / 4 := by
          rw [hc]; push_cast; rw [Real.norm_eq_abs, abs_of_pos (by linarith)]; ring
        set X : ↥(Finset.Icc 1 T) → Ω → ℝ := fun i ω => Z i ω - E with hX
        have hXind : iIndepFun X μ := hindep.comp (fun i x => x - E) (fun i => measurable_id.sub_const _)
        have hXsub : ∀ i : ↥(Finset.Icc 1 T), HasSubgaussianMGF (X i) c μ := by
          intro i
          have h := hasSubgaussianMGF_of_mem_Icc (hid i i.2).aemeasurable_fst (hab i i.2)
          rw [hEi i i.2] at h; exact h
        have hT1 : (1:ℝ) ≤ T := by exact_mod_cast hTpos
        have hL : 0 < Real.log ((T : ℝ) / δ) := Real.log_pos (by rw [one_lt_div hδ]; linarith)
        -- bound for each T'
        have hbad : ∀ T' ∈ Finset.Icc 1 T,
            μ.real {ω | r T' < (1 / (T' : ℝ)) * ∑ i ∈ Finset.Icc 1 T', Z i ω - E} ≤ δ / T := by
          intro T' hT'
          have hT'1 : 1 ≤ T' := (Finset.mem_Icc.mp hT').1
          have hT'T : T' ≤ T := (Finset.mem_Icc.mp hT').2
          have hT'pos : (0:ℝ) < T' := by exact_mod_cast hT'1
          set s : Finset ↥(Finset.Icc 1 T) := (Finset.Icc 1 T').subtype (· ∈ Finset.Icc 1 T) with hs
          have hfilt : (Finset.Icc 1 T').filter (· ∈ Finset.Icc 1 T) = Finset.Icc 1 T' := by
            apply Finset.filter_true_of_mem
            intro x hx
            exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1, (Finset.mem_Icc.mp hx).2.trans hT'T⟩
          have hsumX : ∀ ω, ∑ i ∈ s, X i ω = ∑ i ∈ Finset.Icc 1 T', Z i ω - T' * E := by
            intro ω
            have := Finset.sum_subtype_eq_sum_filter (fun i : ℕ => Z i ω - E)
              (s := Finset.Icc 1 T') (p := (· ∈ Finset.Icc 1 T))
            rw [hfilt] at this
            simp only [hX]
            rw [this, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
            simp
          have hcard : s.card = T' := by
            rw [hs, Finset.card_subtype, hfilt, Nat.card_Icc]; simp
          have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hXind (s := s)
            (fun i _ => hXsub i) (ε := T' * r T') (by
              rw [hr]; simp only
              have : 0 ≤ b - a := by linarith
              positivity)
          simp only [Finset.sum_const, hcard, nsmul_eq_mul] at hH
          push_cast at hH
          rw [hcval] at hH
          have hsub : {ω | r T' < (1 / (T' : ℝ)) * ∑ i ∈ Finset.Icc 1 T', Z i ω - E} ⊆
              {ω | (T' : ℝ) * r T' ≤ ∑ i ∈ s, X i ω} := by
            intro ω hω
            simp only [Set.mem_ofPred_eq] at hω ⊢
            rw [hsumX ω]
            have : (T' : ℝ) * ((1 / (T' : ℝ)) * ∑ i ∈ Finset.Icc 1 T', Z i ω - E) =
                ∑ i ∈ Finset.Icc 1 T', Z i ω - T' * E := by field_simp
            nlinarith
          refine (measureReal_mono hsub (measure_ne_top _ _)).trans (hH.trans (le_of_eq ?_))
          have hr2 : (r T') ^ 2 = (b - a) ^ 2 * (Real.log ((T : ℝ) / δ) / (2 * T')) := by
            rw [hr]; simp only; rw [mul_pow, Real.sq_sqrt (by positivity)]
          have hexp : -((T' : ℝ) * r T') ^ 2 / (2 * ((T' : ℝ) * ((b - a) ^ 2 / 4))) =
              -Real.log ((T : ℝ) / δ) := by
            rw [mul_pow, hr2]
            have : (b - a) ≠ 0 := by linarith
            field_simp; ring
          rw [hexp, Real.exp_neg, Real.exp_log (by positivity), inv_div]
        have hsubU : Gᶜ ⊆ ⋃ T' ∈ Finset.Icc 1 T,
            {ω | r T' < (1 / (T' : ℝ)) * ∑ i ∈ Finset.Icc 1 T', Z i ω - E} := by
          intro ω hω
          simp only [hG, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
          obtain ⟨T', hT', h⟩ := hω
          exact Set.mem_biUnion hT' h
        calc μ.real Gᶜ ≤ μ.real (⋃ T' ∈ Finset.Icc 1 T,
              {ω | r T' < (1 / (T' : ℝ)) * ∑ i ∈ Finset.Icc 1 T', Z i ω - E}) :=
              measureReal_mono hsubU (measure_ne_top _ _)
          _ ≤ ∑ T' ∈ Finset.Icc 1 T,
              μ.real {ω | r T' < (1 / (T' : ℝ)) * ∑ i ∈ Finset.Icc 1 T', Z i ω - E} :=
              measureReal_biUnion_finset_le _ _
          _ ≤ ∑ _T' ∈ Finset.Icc 1 T, δ / T := Finset.sum_le_sum hbad
          _ = δ := by rw [Finset.sum_const, Nat.card_Icc]; simp; field_simp
    have hun : (1:ℝ) ≤ μ.real G + μ.real Gᶜ := by
      have := measureReal_union_le (μ := μ) G Gᶜ
      rw [Set.union_compl_self, probReal_univ] at this; exact this
    linarith
  refine ⟨hpart1, fun τ hτ _ => ?_⟩
  refine hpart1.trans (measureReal_mono ?_ (measure_ne_top _ _))
  intro ω hω
  exact hω (τ ω) (hτ ω)
