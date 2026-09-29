-- Prove2me | solution 1 for DeepLearningTheory.mlp_first_layer_two_point
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T00:59:54.691274+00:00
-- url     : https://prove2.me/submissions/0efb7f75-9554-44fc-a89a-dae6988a583e

import Mathlib
import Definitions.Def_DLT_DeepLinearNetwork
import Definitions.Def_DLT_MLPInit
import Definitions.Def_DLT_GaussianIntegrals

open MeasureTheory ProbabilityTheory
open scoped NNReal
open DeepLearningTheory

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem W5_DeepLearningTheory_gfacts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} {v : ℝ≥0} (h : P.map f = gaussianReal 0 v) :
    AEMeasurable f P ∧ MemLp f 2 P ∧ ∫ ω, f ω ∂P = 0 ∧ ∫ ω, f ω * f ω ∂P = v := by
  have hf : AEMeasurable f P := by
    by_contra hc
    rw [Measure.map_of_not_aemeasurable hc] at h
    have h2 : (0 : Measure ℝ) Set.univ = gaussianReal 0 v Set.univ := by rw [h]
    simp at h2
  have hmem : MemLp f 2 P := by
    have h3 := memLp_id_gaussianReal' (μ := 0) (v := v) 2 (by norm_num)
    rw [← h] at h3
    exact (memLp_map_measure_iff aestronglyMeasurable_id hf).1 h3
  have hint : ∫ ω, f ω ∂P = 0 := by
    calc ∫ ω, f ω ∂P = ∫ y, y ∂(P.map f) := (integral_map hf aestronglyMeasurable_id).symm
      _ = 0 := by rw [h, integral_id_gaussianReal]
  refine ⟨hf, hmem, hint, ?_⟩
  calc ∫ ω, f ω * f ω ∂P = ∫ y, y * y ∂(P.map f) :=
        (integral_map hf (continuous_id.mul continuous_id).aestronglyMeasurable).symm
    _ = v := by
      rw [h]
      have h4 := variance_id_gaussianReal (μ := 0) (v := v)
      rw [variance_of_integral_eq_zero aemeasurable_id (by simp [integral_id_gaussianReal])] at h4
      simpa [sq] using h4

theorem W5_DeepLearningTheory_indep_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f g : Ω → ℝ} {v w : ℝ≥0} (hf : P.map f = gaussianReal 0 v)
    (hg : P.map g = gaussianReal 0 w) (hfg : IndepFun f g P) :
    ∫ ω, f ω * g ω ∂P = 0 := by
  obtain ⟨hf1, -, hf3, -⟩ := W5_DeepLearningTheory_gfacts hf
  obtain ⟨hg1, -, -, -⟩ := W5_DeepLearningTheory_gfacts hg
  rw [hfg.integral_fun_mul_eq_mul_integral hf1.aestronglyMeasurable hg1.aestronglyMeasurable,
    hf3, zero_mul]

theorem W5_DeepLearningTheory_bilin {Ω κ₁ κ₂ : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (s : Finset κ₁) (t : Finset κ₂) (Y₁ : κ₁ → Ω → ℝ) (Y₂ : κ₂ → Ω → ℝ)
    (h1 : ∀ k ∈ s, MemLp (Y₁ k) 2 P) (h2 : ∀ l ∈ t, MemLp (Y₂ l) 2 P) :
    ∫ ω, (∑ k ∈ s, Y₁ k ω) * (∑ l ∈ t, Y₂ l ω) ∂P =
      ∑ k ∈ s, ∑ l ∈ t, ∫ ω, Y₁ k ω * Y₂ l ω ∂P := by
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [integral_finsetSum]
    intro l hl
    exact (h1 k hk).integrable_mul (h2 l hl)
  · intro k hk
    exact integrable_finsetSum _ fun l hl => (h1 k hk).integrable_mul (h2 l hl)

/-! ### MLP parameters -/

theorem W5_DeepLearningTheory_mlp_bb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {Cb CW : ℕ → ℝ≥0}
    {b : Ω → ℕ → ℕ → ℝ} {W : Ω → ℕ → ℕ → ℕ → ℝ} (hinit : IsMLPInit P n Cb CW b W)
    {ℓ i ℓ' i' : ℕ} (h1 : 1 ≤ ℓ) (hi : i < n ℓ) (h1' : 1 ≤ ℓ') (hi' : i' < n ℓ') :
    ∫ ω, b ω ℓ i * b ω ℓ' i' ∂P = if ℓ = ℓ' ∧ i = i' then (Cb ℓ : ℝ) else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact (W5_DeepLearningTheory_gfacts (hinit.2.1 ℓ i h1 hi)).2.2.2
  · apply W5_DeepLearningTheory_indep_zero (hinit.2.1 ℓ i h1 hi) (hinit.2.1 ℓ' i' h1' hi')
    have hne : (Sum.inl (Subtype.mk (ℓ, i) ⟨h1, hi⟩ : {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.2 < n p.1}) :
        BiasIndex n ⊕ WeightIndex n) ≠
        Sum.inl (Subtype.mk (ℓ', i') ⟨h1', hi'⟩ : {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.2 < n p.1}) := by
      intro heq
      apply h
      have h2 := congrArg Subtype.val (Sum.inl_injective heq)
      simp only [Prod.mk.injEq] at h2
      exact h2
    exact hinit.1.indepFun hne

theorem W5_DeepLearningTheory_mlp_bW {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {Cb CW : ℕ → ℝ≥0}
    {b : Ω → ℕ → ℕ → ℝ} {W : Ω → ℕ → ℕ → ℕ → ℝ} (hinit : IsMLPInit P n Cb CW b W)
    {ℓ i ℓ' i' j' : ℕ} (h1 : 1 ≤ ℓ) (hi : i < n ℓ) (h1' : 1 ≤ ℓ') (hi' : i' < n ℓ')
    (hj' : j' < n (ℓ' - 1)) :
    ∫ ω, b ω ℓ i * W ω ℓ' i' j' ∂P = 0 := by
  apply W5_DeepLearningTheory_indep_zero (hinit.2.1 ℓ i h1 hi) (hinit.2.2 ℓ' i' j' h1' hi' hj')
  have hne : (Sum.inl (Subtype.mk (ℓ, i) ⟨h1, hi⟩ : {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.2 < n p.1}) :
      BiasIndex n ⊕ WeightIndex n) ≠
      Sum.inr (Subtype.mk (ℓ', i', j') ⟨h1', hi', hj'⟩ :
        {p : ℕ × ℕ × ℕ // 1 ≤ p.1 ∧ p.2.1 < n p.1 ∧ p.2.2 < n (p.1 - 1)}) := Sum.inl_ne_inr
  exact hinit.1.indepFun hne

theorem W5_DeepLearningTheory_mlp_WW {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {Cb CW : ℕ → ℝ≥0}
    {b : Ω → ℕ → ℕ → ℝ} {W : Ω → ℕ → ℕ → ℕ → ℝ} (hinit : IsMLPInit P n Cb CW b W)
    {ℓ i j ℓ' i' j' : ℕ} (h1 : 1 ≤ ℓ) (hi : i < n ℓ) (hj : j < n (ℓ - 1))
    (h1' : 1 ≤ ℓ') (hi' : i' < n ℓ') (hj' : j' < n (ℓ' - 1)) :
    ∫ ω, W ω ℓ i j * W ω ℓ' i' j' ∂P =
      if ℓ = ℓ' ∧ i = i' ∧ j = j' then ((CW ℓ / (n (ℓ - 1) : ℝ≥0) : ℝ≥0) : ℝ) else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl, rfl⟩ := h
    exact (W5_DeepLearningTheory_gfacts (hinit.2.2 ℓ i j h1 hi hj)).2.2.2
  · apply W5_DeepLearningTheory_indep_zero (hinit.2.2 ℓ i j h1 hi hj)
      (hinit.2.2 ℓ' i' j' h1' hi' hj')
    have hne : (Sum.inr (Subtype.mk (ℓ, i, j) ⟨h1, hi, hj⟩ :
        {p : ℕ × ℕ × ℕ // 1 ≤ p.1 ∧ p.2.1 < n p.1 ∧ p.2.2 < n (p.1 - 1)}) :
        BiasIndex n ⊕ WeightIndex n) ≠
        Sum.inr (Subtype.mk (ℓ', i', j') ⟨h1', hi', hj'⟩ :
          {p : ℕ × ℕ × ℕ // 1 ≤ p.1 ∧ p.2.1 < n p.1 ∧ p.2.2 < n (p.1 - 1)}) := by
      intro heq
      apply h
      have h2 := congrArg Subtype.val (Sum.inr_injective heq)
      simp only [Prod.mk.injEq] at h2
      exact h2
    exact hinit.1.indepFun hne

theorem W5_DeepLearningTheory_lin_WW {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ → ℕ} {CW : ℝ≥0}
    {W : Ω → ℕ → ℕ → ℕ → ℝ} (hW : IsLinearNetInit P n CW W)
    {ℓ i j ℓ' i' j' : ℕ} (h1 : 1 ≤ ℓ) (hi : i < n ℓ) (hj : j < n (ℓ - 1))
    (h1' : 1 ≤ ℓ') (hi' : i' < n ℓ') (hj' : j' < n (ℓ' - 1)) :
    ∫ ω, W ω ℓ i j * W ω ℓ' i' j' ∂P =
      if ℓ = ℓ' ∧ i = i' ∧ j = j' then ((CW / (n (ℓ - 1) : ℝ≥0) : ℝ≥0) : ℝ) else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl, rfl⟩ := h
    exact (W5_DeepLearningTheory_gfacts (hW.2 ℓ i j h1 hi hj)).2.2.2
  · apply W5_DeepLearningTheory_indep_zero (hW.2 ℓ i j h1 hi hj) (hW.2 ℓ' i' j' h1' hi' hj')
    have hne : (Subtype.mk (ℓ, i, j) ⟨h1, hi, hj⟩ :
        {p : ℕ × ℕ × ℕ // 1 ≤ p.1 ∧ p.2.1 < n p.1 ∧ p.2.2 < n (p.1 - 1)}) ≠
        Subtype.mk (ℓ', i', j') ⟨h1', hi', hj'⟩ := by
      intro heq
      apply h
      have h2 := congrArg Subtype.val heq
      simp only [Prod.mk.injEq] at h2
      exact h2
    exact hW.1.indepFun (i := (Subtype.mk (ℓ, i, j) ⟨h1, hi, hj⟩ : WeightIndex n))
      (j := (Subtype.mk (ℓ', i', j') ⟨h1', hi', hj'⟩ : WeightIndex n)) hne

/-! ### First-layer statistics -/

theorem W5_DeepLearningTheory_mlp_first_layer_mean_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (x : ℕ → ℝ) (i : ℕ) (hi : i < n 1) :
    ∫ ω, mlpPreact n σ (b ω) (W ω) x 1 i ∂P = 0 := by
  have hz : ∀ ω, mlpPreact n σ (b ω) (W ω) x 1 i =
      b ω 1 i + ∑ j ∈ Finset.range (n 0), W ω 1 i j * x j := by
    intro ω; simp [mlpPreact]
  simp_rw [hz]
  have hW : ∀ j ∈ Finset.range (n 0), P.map (fun ω => W ω 1 i j) =
      gaussianReal 0 (CW 1 / (n (1 - 1) : ℝ≥0)) :=
    fun j hj => hinit.2.2 1 i j le_rfl hi (by simpa using hj)
  have hb := W5_DeepLearningTheory_gfacts (hinit.2.1 1 i le_rfl hi)
  have hterm : ∀ j ∈ Finset.range (n 0), Integrable (fun ω => W ω 1 i j * x j) P :=
    fun j hj => ((W5_DeepLearningTheory_gfacts (hW j hj)).2.1.integrable one_le_two).mul_const _
  rw [integral_add (hb.2.1.integrable one_le_two) (integrable_finsetSum _ hterm),
    integral_finsetSum _ hterm, hb.2.2.1, zero_add]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [integral_mul_const, (W5_DeepLearningTheory_gfacts (hW j hj)).2.2.1, zero_mul]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (Cb CW : ℕ → ℝ≥0) (σ : ℝ → ℝ)
    (b : Ω → ℕ → ℕ → ℝ) (W : Ω → ℕ → ℕ → ℕ → ℝ) (hinit : IsMLPInit P n Cb CW b W)
    (x₁ x₂ : ℕ → ℝ) (i₁ i₂ : ℕ) (hi₁ : i₁ < n 1) (hi₂ : i₂ < n 1) :
    ∫ ω, mlpPreact n σ (b ω) (W ω) x₁ 1 i₁ * mlpPreact n σ (b ω) (W ω) x₂ 1 i₂ ∂P
      = kron i₁ i₂ * ((Cb 1 : ℝ) + (CW 1 : ℝ) * inputKernel (n 0) x₁ x₂) := by
  have hz : ∀ (ω : Ω) (x : ℕ → ℝ) (i : ℕ), mlpPreact n σ (b ω) (W ω) x 1 i =
      ∑ o ∈ Finset.insertNone (Finset.range (n 0)),
        Option.elim o (b ω 1 i) (fun j => W ω 1 i j * x j) := by
    intro ω x i
    rw [Finset.sum_insertNone]
    simp [mlpPreact]
  simp_rw [hz]
  have hmem : ∀ (x : ℕ → ℝ) (i : ℕ), i < n 1 → ∀ o ∈ Finset.insertNone (Finset.range (n 0)),
      MemLp (fun ω => Option.elim o (b ω 1 i) (fun j => W ω 1 i j * x j)) 2 P := by
    intro x i hi o ho
    cases o with
    | none => exact (W5_DeepLearningTheory_gfacts (hinit.2.1 1 i le_rfl hi)).2.1
    | some j =>
      have hj : j < n 0 := by simpa using ho
      exact (W5_DeepLearningTheory_gfacts
        (hinit.2.2 1 i j le_rfl hi (by simpa using hj))).2.1.mul_const (x j)
  have hB := W5_DeepLearningTheory_bilin (P := P) (Finset.insertNone (Finset.range (n 0)))
    (Finset.insertNone (Finset.range (n 0)))
    (fun o ω => Option.elim o (b ω 1 i₁) (fun j => W ω 1 i₁ j * x₁ j))
    (fun o ω => Option.elim o (b ω 1 i₂) (fun j => W ω 1 i₂ j * x₂ j))
    (hmem x₁ i₁ hi₁) (hmem x₂ i₂ hi₂)
  try simp only at hB
  rw [hB]
  simp only [Finset.sum_insertNone, Option.elim]
  have hbb := W5_DeepLearningTheory_mlp_bb hinit (le_refl 1) hi₁ (le_refl 1) hi₂
  have hbW : ∀ k ∈ Finset.range (n 0), ∫ ω, b ω 1 i₁ * (W ω 1 i₂ k * x₂ k) ∂P = 0 := by
    intro k hk
    have := W5_DeepLearningTheory_mlp_bW hinit (le_refl 1) hi₁ (le_refl 1) hi₂
      (j' := k) (by simpa using hk)
    rw [show (fun ω => b ω 1 i₁ * (W ω 1 i₂ k * x₂ k)) =
      fun ω => x₂ k * (b ω 1 i₁ * W ω 1 i₂ k) from funext fun ω => by ring,
      integral_const_mul, this, mul_zero]
  have hWb : ∀ j ∈ Finset.range (n 0), ∫ ω, W ω 1 i₁ j * x₁ j * b ω 1 i₂ ∂P = 0 := by
    intro j hj
    have := W5_DeepLearningTheory_mlp_bW hinit (le_refl 1) hi₂ (le_refl 1) hi₁
      (j' := j) (by simpa using hj)
    rw [show (fun ω => W ω 1 i₁ j * x₁ j * b ω 1 i₂) =
      fun ω => x₁ j * (b ω 1 i₂ * W ω 1 i₁ j) from funext fun ω => by ring,
      integral_const_mul, this, mul_zero]
  have hWW : ∀ j ∈ Finset.range (n 0),
      ∑ k ∈ Finset.range (n 0), ∫ ω, W ω 1 i₁ j * x₁ j * (W ω 1 i₂ k * x₂ k) ∂P =
        kron i₁ i₂ * (x₁ j * x₂ j * ((CW 1 / (n 0 : ℝ≥0) : ℝ≥0) : ℝ)) := by
    intro j hj
    have hk : ∀ k ∈ Finset.range (n 0),
        ∫ ω, W ω 1 i₁ j * x₁ j * (W ω 1 i₂ k * x₂ k) ∂P =
          x₁ j * x₂ k * (if 1 = 1 ∧ i₁ = i₂ ∧ j = k then
            ((CW 1 / (n (1 - 1) : ℝ≥0) : ℝ≥0) : ℝ) else 0) := by
      intro k hk
      rw [show (fun ω => W ω 1 i₁ j * x₁ j * (W ω 1 i₂ k * x₂ k)) =
        fun ω => x₁ j * x₂ k * (W ω 1 i₁ j * W ω 1 i₂ k) from funext fun ω => by ring,
        integral_const_mul, W5_DeepLearningTheory_mlp_WW hinit (le_refl 1) hi₁
          (by simpa using hj) (le_refl 1) hi₂ (by simpa using hk)]
    rw [Finset.sum_congr rfl hk, Finset.sum_eq_single j]
    · unfold kron
      by_cases h : i₁ = i₂ <;> simp [h]
    · intro k _ hkj
      simp [Ne.symm hkj]
    · intro hj'
      exact absurd hj hj'
  rw [hbb, Finset.sum_eq_zero hbW, Finset.sum_add_distrib, Finset.sum_eq_zero hWb,
    Finset.sum_congr rfl hWW]
  unfold kron
  by_cases h : i₁ = i₂
  · subst h
    simp only [eq_self_iff_true, and_self, if_true, one_mul, add_zero, zero_add]
    congr 1
    rw [inputKernel, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  · simp [h]

theorem W5_DeepLearningTheory_linearNet_two_point_first_layer {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ → ℕ) (CW : ℝ≥0) (W : Ω → ℕ → ℕ → ℕ → ℝ)
    (hW : IsLinearNetInit P n CW W) (x₁ x₂ : ℕ → ℝ) (i₁ i₂ : ℕ)
    (hi₁ : i₁ < n 1) (hi₂ : i₂ < n 1) :
    ∫ ω, linearPreact n (W ω) x₁ 1 i₁ * linearPreact n (W ω) x₂ 1 i₂ ∂P
      = kron i₁ i₂ * (CW : ℝ) * inputKernel (n 0) x₁ x₂ := by
  have hz : ∀ (ω : Ω) (x : ℕ → ℝ) (i : ℕ), linearPreact n (W ω) x 1 i =
      ∑ j ∈ Finset.range (n 0), W ω 1 i j * x j := by
    intro ω x i
    simp [linearPreact]
  simp_rw [hz]
  have hmem : ∀ (x : ℕ → ℝ) (i : ℕ), i < n 1 → ∀ j ∈ Finset.range (n 0),
      MemLp (fun ω => W ω 1 i j * x j) 2 P := by
    intro x i hi j hj
    exact (W5_DeepLearningTheory_gfacts
      (hW.2 1 i j le_rfl hi (by simpa using hj))).2.1.mul_const (x j)
  have hB := W5_DeepLearningTheory_bilin (P := P) (Finset.range (n 0)) (Finset.range (n 0))
    (fun j ω => W ω 1 i₁ j * x₁ j) (fun j ω => W ω 1 i₂ j * x₂ j)
    (hmem x₁ i₁ hi₁) (hmem x₂ i₂ hi₂)
  try simp only at hB
  rw [hB]
  have hWW : ∀ j ∈ Finset.range (n 0),
      ∑ k ∈ Finset.range (n 0), ∫ ω, W ω 1 i₁ j * x₁ j * (W ω 1 i₂ k * x₂ k) ∂P =
        kron i₁ i₂ * (x₁ j * x₂ j * ((CW / (n 0 : ℝ≥0) : ℝ≥0) : ℝ)) := by
    intro j hj
    have hk : ∀ k ∈ Finset.range (n 0),
        ∫ ω, W ω 1 i₁ j * x₁ j * (W ω 1 i₂ k * x₂ k) ∂P =
          x₁ j * x₂ k * (if 1 = 1 ∧ i₁ = i₂ ∧ j = k then
            ((CW / (n (1 - 1) : ℝ≥0) : ℝ≥0) : ℝ) else 0) := by
      intro k hk
      rw [show (fun ω => W ω 1 i₁ j * x₁ j * (W ω 1 i₂ k * x₂ k)) =
        fun ω => x₁ j * x₂ k * (W ω 1 i₁ j * W ω 1 i₂ k) from funext fun ω => by ring,
        integral_const_mul, W5_DeepLearningTheory_lin_WW hW (le_refl 1) hi₁
          (by simpa using hj) (le_refl 1) hi₂ (by simpa using hk)]
    rw [Finset.sum_congr rfl hk, Finset.sum_eq_single j]
    · unfold kron
      by_cases h : i₁ = i₂ <;> simp [h]
    · intro k _ hkj
      simp [Ne.symm hkj]
    · intro hj'
      exact absurd hj hj'
  rw [Finset.sum_congr rfl hWW]
  unfold kron
  by_cases h : i₁ = i₂
  · simp only [h, if_true, one_mul, inputKernel, Finset.mul_sum,
      NNReal.coe_div, NNReal.coe_natCast]
    refine Finset.sum_congr rfl fun j _ => by ring
  · simp [h]
