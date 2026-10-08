-- Prove2me | solution 1 for FoundationsML.Regression.finite_hypothesis_regression_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:36:50.170197+00:00
-- url     : https://prove2.me/submissions/3d79a704-fa3d-4d25-8ddd-56422a142c51

import Mathlib
import Definitions.Def_FoundationsML_Regression_GeneralizationError
import Definitions.Def_FoundationsML_Regression_EmpiricalError

open MeasureTheory


namespace FoundationsML.Regression

open ProbabilityTheory in
lemma fhr53_single {X : Type*} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (L : ℝ → ℝ → ℝ) (M : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y') (hLb : ∀ y y', L y y' ≤ M)
    (hL_meas : Measurable (Function.uncurry L)) (h : X → ℝ) (hh : Measurable h)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin m => D)).real
      {S : Fin m → X × ℝ | EmpiricalError S L h + ε < GeneralizationError D L h} ≤
      Real.exp (-(2 * m * ε ^ 2 / M ^ 2)) := by
  set g : X × ℝ → ℝ := fun p => L (h p.1) p.2 with hg
  have hgm : Measurable g := hL_meas.comp ((hh.comp measurable_fst).prodMk measurable_snd)
  have hgI : ∀ x, -g x ∈ Set.Icc (-M) 0 := by
    intro x; simp only [Set.mem_Icc]; constructor <;> linarith [hLnn (h x.1) x.2, hLb (h x.1) x.2]
  have hint : ∫ x, g x ∂D = GeneralizationError D L h := rfl
  set μ := Measure.pi (fun _ : Fin m => D)
  set R := GeneralizationError D L h
  have hind : iIndepFun (fun (i : Fin m) (ω : Fin m → X × ℝ) => -g (ω i) + R) μ := by
    exact iIndepFun_pi (X := fun _ b => -g b + R) (fun _ => (hgm.neg.add_const R).aemeasurable)
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin m)), HasSubgaussianMGF
      (fun ω : Fin m → X × ℝ => -g (ω i) + R) ((‖(0:ℝ) - (-M)‖₊ / 2) ^ 2) μ := by
    intro i _
    have hmeas : AEMeasurable (fun ω : Fin m → X × ℝ => -g (ω i)) μ :=
      (hgm.neg.comp (measurable_pi_apply i)).aemeasurable
    have h := hasSubgaussianMGF_of_mem_Icc (a := -M) (b := 0) hmeas
      (Filter.Eventually.of_forall fun ω => hgI (ω i))
    have hi : ∫ ω, -g (ω i) ∂μ = -R := by
      have := integral_comp_eval (μ := fun _ : Fin m => D) (i := i) (f := fun x => -g x)
        hgm.neg.aestronglyMeasurable
      simp only [μ] at this ⊢
      rw [this, integral_neg, hint]
    rw [hi] at h
    simpa [sub_neg_eq_add] using h
  have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub
    (mul_nonneg (Nat.cast_nonneg m) hε : (0:ℝ) ≤ m * ε)
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hsum : ∀ S : Fin m → X × ℝ, ∑ i : Fin m, g (S i) = m * EmpiricalError S L h := by
    intro S
    unfold EmpiricalError
    rw [← mul_assoc, mul_one_div_cancel hmR.ne', one_mul]
  calc μ.real {S : Fin m → X × ℝ | EmpiricalError S L h + ε < R}
      ≤ μ.real {ω | (m:ℝ) * ε ≤ ∑ i : Fin m, (-g (ω i) + R)} := by
        apply measureReal_mono
        · intro S hS
          simp only [Set.mem_setOf_eq] at hS ⊢
          rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hsum S]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          nlinarith
        · exact measure_ne_top _ _
    _ ≤ _ := hH
    _ = Real.exp (-(2 * m * ε ^ 2 / M ^ 2)) := by
        congr 1
        have hs : ((∑ i : Fin m, ((‖(0:ℝ) - (-M)‖₊ / 2) ^ 2 : NNReal) : NNReal) : ℝ) = m * M ^ 2 / 4 := by
          push_cast
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [sub_neg_eq_add, zero_add, Real.norm_eq_abs, abs_of_pos hM]
          ring
        rw [hs]
        field_simp
        ring

theorem fhr53_core
    {X : Type*} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (L : ℝ → ℝ → ℝ) (M : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y') (hLb : ∀ y y', L y y' ≤ M)
    (hL_meas : Measurable (Function.uncurry L))
    (H : Finset (X → ℝ)) (hHne : H.Nonempty) (hH_meas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        GeneralizationError D L h ≤
          EmpiricalError S L h +
            M * Real.sqrt ((Real.log H.card + Real.log (1 / δ)) / (2 * m))}).toReal := by
  set μ := Measure.pi (fun _ : Fin m => D)
  set ε := M * Real.sqrt ((Real.log (H.card : ℝ) + Real.log (1 / δ)) / (2 * m)) with hεdef
  set G := {S : Fin m → X × ℝ | ∀ h ∈ H, GeneralizationError D L h ≤ EmpiricalError S L h + ε}
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hcard : (0:ℝ) < H.card := by exact_mod_cast hHne.card_pos
  have hlogH : 0 ≤ Real.log (H.card : ℝ) := Real.log_nonneg (by exact_mod_cast hHne.card_pos)
  have hlog2 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have harg : 0 ≤ (Real.log (H.card : ℝ) + Real.log (1 / δ)) / (2 * m) := by positivity
  have hε0 : 0 ≤ ε := mul_nonneg hM.le (Real.sqrt_nonneg _)
  have hε2 : 2 * m * ε ^ 2 / M ^ 2 = Real.log (H.card : ℝ) + Real.log (1 / δ) := by
    rw [hεdef, mul_pow, Real.sq_sqrt harg]; field_simp
  have hexp : Real.exp (-(2 * m * ε ^ 2 / M ^ 2)) = δ / H.card := by
    rw [hε2, neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hcard,
      Real.exp_log (by positivity)]
    field_simp
  have hsub : Gᶜ ⊆ ⋃ h ∈ H, {S : Fin m → X × ℝ | EmpiricalError S L h + ε < GeneralizationError D L h} := by
    intro S hS
    simp only [G, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hS
    obtain ⟨h, hH, hlt⟩ := hS
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨h, hH, hlt⟩
  have hbad : μ.real Gᶜ ≤ δ := by
    calc μ.real Gᶜ ≤ μ.real (⋃ h ∈ H, {S : Fin m → X × ℝ | EmpiricalError S L h + ε < GeneralizationError D L h}) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ h ∈ H, μ.real {S : Fin m → X × ℝ | EmpiricalError S L h + ε < GeneralizationError D L h} :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ h ∈ H, δ / H.card := by
          apply Finset.sum_le_sum
          intro h hh
          rw [← hexp]
          exact fhr53_single D L M hM hLnn hLb hL_meas h (hH_meas h hh) m hm ε hε0
      _ = δ := by
          rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  have h1 : (1:ℝ) ≤ μ.real G + μ.real Gᶜ := by
    have := measureReal_union_le (μ := μ) G Gᶜ
    rw [Set.union_compl_self, probReal_univ] at this
    exact this
  show 1 - δ ≤ μ.real G
  linarith

end FoundationsML.Regression

open FoundationsML.Regression


theorem solution
    {X : Type*} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (L : ℝ → ℝ → ℝ) (M : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y') (hLb : ∀ y y', L y y' ≤ M)
    (hL_meas : Measurable (Function.uncurry L))
    (H : Finset (X → ℝ)) (hHne : H.Nonempty) (hH_meas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ H,
        GeneralizationError D L h ≤
          EmpiricalError S L h +
            M * Real.sqrt ((Real.log H.card + Real.log (1 / δ)) / (2 * m))}).toReal := by
  exact fhr53_core D L M hM hLnn hLb hL_meas H hHne hH_meas m hm δ hδ hδ1
