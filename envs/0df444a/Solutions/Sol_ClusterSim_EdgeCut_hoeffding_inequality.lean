-- Prove2me | solution 1 for ClusterSim.EdgeCut.hoeffding_inequality
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T23:17:44.296062+00:00
-- url     : https://prove2.me/submissions/1e43ebda-298f-4b7d-9505-66783d154d36

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] {a δ : ℝ} (ha : 0 < a)
    (hδ : 0 < δ) (hμ : ∀ᵐ x ∂μ, |x| ≤ a) (N : ℕ) (hN : 0 < N) :
    ENNReal.ofReal (1 - 2 * Real.exp (-(N * δ ^ 2) / (2 * a ^ 2))) ≤
        Measure.pi (fun _ : Fin N => μ)
          {x | |(∑ i, x i) / N - ∫ t, t ∂μ| < δ} ∧
      (4 * a ^ 2 / δ ^ 2 ≤ N → (2 / 3 : ℝ) < 1 - 2 * Real.exp (-(N * δ ^ 2) / (2 * a ^ 2))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hE : Real.exp (-(N * δ ^ 2) / (2 * a ^ 2)) = Real.exp (-(N * δ) ^ 2 / (2 * (N * a ^ 2))) := by
    congr 1
    field_simp
  refine ⟨?_, ?_⟩
  · set P := Measure.pi (fun _ : Fin N => μ) with hP
    set m := ∫ t, t ∂μ with hm
    have hIcc : ∀ᵐ t ∂μ, t ∈ Set.Icc (-a) a := by
      filter_upwards [hμ] with t ht using abs_le.mp ht
    have h1 : HasSubgaussianMGF (fun t : ℝ => t - m)
        ((‖a - -a‖₊ / 2) ^ 2) μ :=
      hasSubgaussianMGF_of_mem_Icc (X := id) aemeasurable_id hIcc
    have hc' : (‖a - -a‖ / 2) ^ 2 = a ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]; ring
    have hc2 : ((((N : NNReal) * ((‖a - -a‖₊ / 2) ^ 2) : NNReal)) : ℝ) = N * a ^ 2 := by
      push_cast; rw [hc']
    have hpres : ∀ i : Fin N, MeasureTheory.MeasurePreserving (fun ω : Fin N → ℝ => ω i) P μ :=
      fun i => measurePreserving_eval _ i
    have h2 : ∀ i : Fin N, HasSubgaussianMGF (fun ω : Fin N → ℝ => ω i - m)
        ((‖a - -a‖₊ / 2) ^ 2) P := by
      intro i
      have := HasSubgaussianMGF.of_map (μ := P) (hpres i).measurable.aemeasurable
        (by rw [(hpres i).map_eq]; exact h1)
      exact this
    have hind : iIndepFun (fun (i : Fin N) (ω : Fin N → ℝ) => ω i - m) P :=
      iIndepFun_pi (X := fun _ t => t - m) (fun _ => by fun_prop)
    have hind' : iIndepFun (fun (i : Fin N) (ω : Fin N → ℝ) => -(ω i - m)) P :=
      iIndepFun_pi (X := fun _ t => -(t - m)) (fun _ => by fun_prop)
    have h2' : ∀ i : Fin N, HasSubgaussianMGF (fun ω : Fin N → ℝ => -(ω i - m))
        ((‖a - -a‖₊ / 2) ^ 2) P := fun i => (h2 i).neg
    have hε : 0 ≤ (N : ℝ) * δ := by positivity
    have u1 := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
      (s := Finset.univ) (fun i _ => h2 i) hε
    have u2 := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind'
      (s := Finset.univ) (fun i _ => h2' i) hε
    simp only [NNReal.coe_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at u1 u2
    rw [hc2] at u1 u2
    rw [hE]
    set E := Real.exp (-(N * δ) ^ 2 / (2 * (N * a ^ 2))) with hEdef
    have hsub : {x : Fin N → ℝ | ¬ |(∑ i, x i) / N - m| < δ} ⊆
        {ω | (N : ℝ) * δ ≤ ∑ i, (ω i - m)} ∪ {ω | (N : ℝ) * δ ≤ ∑ i, -(ω i - m)} := by
      intro x hx
      simp only [Set.mem_setOf_eq, not_lt] at hx
      simp only [Set.mem_union, Set.mem_setOf_eq, Finset.sum_neg_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have key : (∑ i, x i) / N - m = ((∑ i, x i) - N * m) / N := by field_simp
      rcases le_abs'.mp hx with h | h
      · right
        rw [key] at h
        rw [div_le_iff₀ hNpos] at h
        nlinarith
      · left
        rw [key] at h
        rw [le_div_iff₀ hNpos] at h
        nlinarith
    have hbad : P.real {x | ¬ |(∑ i, x i) / N - m| < δ} ≤ 2 * E := by
      calc P.real {x | ¬ |(∑ i, x i) / N - m| < δ}
          ≤ P.real ({ω | (N : ℝ) * δ ≤ ∑ i, (ω i - m)} ∪ {ω | (N : ℝ) * δ ≤ ∑ i, -(ω i - m)}) :=
            measureReal_mono hsub
        _ ≤ P.real {ω | (N : ℝ) * δ ≤ ∑ i, (ω i - m)} + P.real {ω | (N : ℝ) * δ ≤ ∑ i, -(ω i - m)} :=
            measureReal_union_le _ _
        _ ≤ E + E := add_le_add u1 u2
        _ = 2 * E := by ring
    have hmeas : MeasurableSet {x : Fin N → ℝ | ¬ |(∑ i, x i) / N - m| < δ} := by
      have hm0 : MeasurableSet {x : Fin N → ℝ | |(∑ i, x i) / N - m| < δ} :=
        measurableSet_lt (by fun_prop) (by fun_prop)
      exact hm0.compl
    have hgood : {x : Fin N → ℝ | |(∑ i, x i) / N - m| < δ} =
        {x : Fin N → ℝ | ¬ |(∑ i, x i) / N - m| < δ}ᶜ := by ext; simp
    have : P.real {x : Fin N → ℝ | |(∑ i, x i) / N - m| < δ} = 1 - P.real {x | ¬ |(∑ i, x i) / N - m| < δ} := by
      rw [hgood, probReal_compl_eq_one_sub hmeas]
    calc ENNReal.ofReal (1 - 2 * E) ≤ ENNReal.ofReal (P.real {x : Fin N → ℝ | |(∑ i, x i) / N - m| < δ}) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = _ := ENNReal.ofReal_toReal (measure_ne_top _ _)
  · intro h
    have h1 : (2:ℝ) ≤ N * δ ^ 2 / (2 * a ^ 2) := by
      rw [div_le_iff₀ (by positivity)] at h
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h2 : Real.exp (-(N * δ ^ 2) / (2 * a ^ 2)) ≤ Real.exp (-2) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div]; linarith
    have h3 : Real.exp (-2) < 1 / 6 := by
      rw [Real.exp_neg, inv_eq_one_div]
      apply one_div_lt_one_div_of_lt (by norm_num)
      have := Real.exp_one_gt_d9
      have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [e2]; nlinarith
    linarith
