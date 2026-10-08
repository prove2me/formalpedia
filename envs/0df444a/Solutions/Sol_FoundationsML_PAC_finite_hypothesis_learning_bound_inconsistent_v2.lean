-- Prove2me | solution 1 for FoundationsML.PAC.finite_hypothesis_learning_bound_inconsistent_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:02:04.397013+00:00
-- url     : https://prove2.me/submissions/f02433ca-62cf-41d1-b9f3-1634e2705c07

import Mathlib
import Definitions.Def_FoundationsML_PAC_GeneralizationError
import Definitions.Def_FoundationsML_PAC_EmpiricalError

open MeasureTheory


namespace FoundationsML.PAC

open ProbabilityTheory in
/-- One-sided Hoeffding bound for a single hypothesis. -/
lemma pacv2_single {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c h : X → Bool) (hc : Measurable c) (hh : Measurable h)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin m => D)).real
      {S : Fin m → X | EmpiricalError S c h + ε < GeneralizationError D c h} ≤
      Real.exp (-(2 * m * ε ^ 2)) := by
  set A : Set X := {x | h x ≠ c x} with hA
  have hAm : MeasurableSet A := (measurableSet_eq_fun hh hc).compl
  set g : X → ℝ := A.indicator 1 with hg
  have hgm : Measurable g := measurable_one.indicator hAm
  have hgI : ∀ x, -g x ∈ Set.Icc (-1:ℝ) 0 := by
    intro x; simp only [hg, Set.indicator]; split_ifs <;> norm_num
  have hint : ∫ x, g x ∂D = GeneralizationError D c h := by
    rw [hg, integral_indicator_one hAm]; rfl
  set μ := Measure.pi (fun _ : Fin m => D)
  set R := GeneralizationError D c h
  have hind : iIndepFun (fun (i : Fin m) (ω : Fin m → X) => -g (ω i) + R) μ := by
    exact iIndepFun_pi (X := fun _ b => -g b + R) (fun _ => (hgm.neg.add_const R).aemeasurable)
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin m)), HasSubgaussianMGF
      (fun ω : Fin m → X => -g (ω i) + R) ((‖(0:ℝ) - (-1)‖₊ / 2) ^ 2) μ := by
    intro i _
    have hmeas : AEMeasurable (fun ω : Fin m → X => -g (ω i)) μ :=
      (hgm.neg.comp (measurable_pi_apply i)).aemeasurable
    have h := hasSubgaussianMGF_of_mem_Icc (a := -1) (b := 0) hmeas
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
  have hsum : ∀ S : Fin m → X, ∑ i : Fin m, g (S i) = m * EmpiricalError S c h := by
    intro S
    unfold EmpiricalError
    rw [mul_div_cancel₀ _ hmR.ne']
    simp only [hg, Set.indicator, hA, Set.mem_setOf_eq, Pi.one_apply]
    rw [Finset.sum_boole]
    congr 2
    ext i
    simp
  calc μ.real {S : Fin m → X | EmpiricalError S c h + ε < R}
      ≤ μ.real {ω | (m:ℝ) * ε ≤ ∑ i : Fin m, (-g (ω i) + R)} := by
        apply measureReal_mono
        · intro S hS
          simp only [Set.mem_setOf_eq] at hS ⊢
          rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, hsum S]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          nlinarith
        · exact measure_ne_top _ _
    _ ≤ _ := hH
    _ = Real.exp (-(2 * m * ε ^ 2)) := by
        congr 1
        have hs : ((∑ i : Fin m, ((‖(0:ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal) : NNReal) : ℝ) = m / 4 := by
          push_cast
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
          ring
        rw [hs]
        field_simp
        ring

theorem pacv2_core
    {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (H : Finset (X → Bool)) (hHne : H.Nonempty) (c : X → Bool)
    (hc_meas : Measurable c) (hH_meas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D c h ≤
        EmpiricalError S c h +
          Real.sqrt ((Real.log (H.card : ℝ) + Real.log (2 / δ)) / (2 * m))}).toReal := by
  set μ := Measure.pi (fun _ : Fin m => D)
  set ε := Real.sqrt ((Real.log (H.card : ℝ) + Real.log (2 / δ)) / (2 * m)) with hεdef
  set G := {S : Fin m → X | ∀ h ∈ H, GeneralizationError D c h ≤ EmpiricalError S c h + ε}
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hcard : (0:ℝ) < H.card := by exact_mod_cast hHne.card_pos
  have hlogH : 0 ≤ Real.log (H.card : ℝ) := Real.log_nonneg (by exact_mod_cast hHne.card_pos)
  have hlog2 : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have harg : 0 ≤ (Real.log (H.card : ℝ) + Real.log (2 / δ)) / (2 * m) := by positivity
  have hε2 : 2 * m * ε ^ 2 = Real.log (H.card : ℝ) + Real.log (2 / δ) := by
    rw [hεdef, Real.sq_sqrt harg]; field_simp
  have hexp : Real.exp (-(2 * m * ε ^ 2)) = δ / (2 * H.card) := by
    rw [hε2, neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hcard,
      Real.exp_log (by positivity)]
    field_simp
  have hsub : Gᶜ ⊆ ⋃ h ∈ H, {S : Fin m → X | EmpiricalError S c h + ε < GeneralizationError D c h} := by
    intro S hS
    simp only [G, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hS
    obtain ⟨h, hH, hlt⟩ := hS
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨h, hH, hlt⟩
  have hbad : μ.real Gᶜ ≤ δ / 2 := by
    calc μ.real Gᶜ ≤ μ.real (⋃ h ∈ H, {S : Fin m → X | EmpiricalError S c h + ε < GeneralizationError D c h}) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ h ∈ H, μ.real {S : Fin m → X | EmpiricalError S c h + ε < GeneralizationError D c h} :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ h ∈ H, δ / (2 * H.card) := by
          apply Finset.sum_le_sum
          intro h hh
          rw [← hexp]
          exact pacv2_single D c h hc_meas (hH_meas h hh) m hm ε (Real.sqrt_nonneg _)
      _ = δ / 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  have h1 : (1:ℝ) ≤ μ.real G + μ.real Gᶜ := by
    have := measureReal_union_le (μ := μ) G Gᶜ
    rw [Set.union_compl_self, probReal_univ] at this
    exact this
  show 1 - δ ≤ μ.real G
  linarith

end FoundationsML.PAC

open FoundationsML.PAC


theorem solution
    {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (H : Finset (X → Bool)) (hHne : H.Nonempty) (c : X → Bool)
    (hc_meas : Measurable c) (hH_meas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D c h ≤
        EmpiricalError S c h +
          Real.sqrt ((Real.log (H.card : ℝ) + Real.log (2 / δ)) / (2 * m))}).toReal := by
  exact pacv2_core D H hHne c hc_meas hH_meas m hm δ hδ hδ1
