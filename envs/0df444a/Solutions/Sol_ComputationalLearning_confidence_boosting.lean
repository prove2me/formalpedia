-- Prove2me | solution 1 for ComputationalLearning.confidence_boosting
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T04:19:06.129569+00:00
-- url     : https://prove2.me/submissions/4a5b6a0d-8d23-4038-b5cd-2b60f2ca2953

import Mathlib
import Definitions.Def_ComputationalLearning_Boosting

open MeasureTheory ProbabilityTheory


namespace ComputationalLearning

section Confidence

variable {X : Type*} [MeasurableSpace X]

lemma cb_prob (c : X → Bool) (hc : Measurable c) (D : Measure X) [IsProbabilityMeasure D] :
    IsProbabilityMeasure (exampleLaw D c) :=
  Measure.isProbabilityMeasure_map (measurable_id.prodMk hc).aemeasurable

/-- Hoeffding's inequality for a `[0, 1]`-valued statistic of the examples. -/
lemma cb_hoeff (c : X → Bool) (hc : Measurable c) (D : Measure X) [IsProbabilityMeasure D]
    (g : X × Bool → ℝ) (hg : Measurable g) (hg01 : ∀ q, g q ∈ Set.Icc (0:ℝ) 1) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    (sampleLaw D c m).real {S | t ≤ ∑ i : Fin m, (g (S i) - ∫ q, g q ∂(exampleLaw D c))} ≤
      Real.exp (-t ^ 2 / (2 * ∑ i : Fin m, ((‖(1:ℝ) - 0‖₊ / 2) ^ 2 : NNReal))) := by
  haveI := cb_prob c hc D
  set μg := ∫ q, g q ∂(exampleLaw D c) with hμg
  have hind : iIndepFun (fun (i : Fin m) (S : Fin m → X × Bool) => g (S i) - μg)
      (sampleLaw D c m) := by
    unfold sampleLaw
    exact iIndepFun_pi (X := fun _ q => g q - μg) (fun _ => (hg.sub_const μg).aemeasurable)
  haveI : IsProbabilityMeasure (sampleLaw D c m) := by unfold sampleLaw; infer_instance
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin m)), HasSubgaussianMGF
      (fun S : Fin m → X × Bool => g (S i) - μg) ((‖(1:ℝ) - 0‖₊ / 2) ^ 2) (sampleLaw D c m) := by
    intro i _
    have hm : AEMeasurable (fun S : Fin m → X × Bool => g (S i)) (sampleLaw D c m) :=
      (hg.comp (measurable_pi_apply i)).aemeasurable
    have h := hasSubgaussianMGF_of_mem_Icc (a := 0) (b := 1) hm
      (Filter.Eventually.of_forall fun S => hg01 (S i))
    have hint : ∫ S, g (S i) ∂(sampleLaw D c m) = μg := by
      unfold sampleLaw
      exact integral_comp_eval hg.aestronglyMeasurable
    rw [hint] at h
    exact h
  exact HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub ht

lemma cb_hoeff' (c : X → Bool) (hc : Measurable c) (D : Measure X) [IsProbabilityMeasure D]
    (g : X × Bool → ℝ) (hg : Measurable g) (hg01 : ∀ q, g q ∈ Set.Icc (0:ℝ) 1) (m : ℕ)
    (hm : 0 < m) (t : ℝ) (ht : 0 ≤ t) :
    sampleLaw D c m {S | t ≤ ∑ i : Fin m, (g (S i) - ∫ q, g q ∂(exampleLaw D c))} ≤
      ENNReal.ofReal (Real.exp (-(2 * t ^ 2 / m))) := by
  haveI := cb_prob c hc D
  haveI : IsProbabilityMeasure (sampleLaw D c m) := by unfold sampleLaw; infer_instance
  have h := cb_hoeff c hc D g hg hg01 m t ht
  rw [← ENNReal.ofReal_toReal (measure_ne_top (sampleLaw D c m) _)]
  apply ENNReal.ofReal_le_ofReal
  refine h.trans (le_of_eq ?_)
  congr 1
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hs : ((∑ i : Fin m, ((‖(1:ℝ) - 0‖₊ / 2) ^ 2 : NNReal) : NNReal) : ℝ) = m / 4 := by
    push_cast
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
    ring
  rw [hs]
  field_simp
  ring

theorem cb_part1 (c : X → Bool) (hc : Measurable c) (D : Measure X) [IsProbabilityMeasure D]
    {ε : ℝ} (m : ℕ) (L : (Fin m → X × Bool) → X → Bool) {δ₀ : ℝ} (h0 : 0 ≤ δ₀) (h1 : δ₀ ≤ 1)
    (hL : sampleLaw D c m {S | ε < errorOf D c (L S)} ≤ ENNReal.ofReal (1 - δ₀)) (k : ℕ) :
    blockSampleLaw D c k m {B | ∀ i, ε < errorOf D c (L (B i))} ≤
      ENNReal.ofReal ((1 - δ₀) ^ k) := by
  haveI := cb_prob c hc D
  haveI : IsProbabilityMeasure (sampleLaw D c m) := by unfold sampleLaw; infer_instance
  have hset : {B : Fin k → Fin m → X × Bool | ∀ i, ε < errorOf D c (L (B i))} =
      Set.univ.pi (fun _ => {S | ε < errorOf D c (L S)}) := by
    ext B; simp [Set.mem_pi]
  rw [hset, blockSampleLaw, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.ofReal_pow (by linarith)]
  exact pow_le_pow_left₀ zero_le hL k

theorem cb_part2 (c : X → Bool) (hc : Measurable c) (D : Measure X) [IsProbabilityMeasure D]
    {ε : ℝ} (k : ℕ) (h : Fin k → X → Bool) (hh : ∀ i, Measurable (h i))
    (hex : ∃ i, errorOf D c (h i) ≤ ε) {γ : ℝ} (hγ : 0 < γ) (m : ℕ)
    (sel : (Fin m → X × Bool) → Fin k)
    (hsel : ∀ S j, mistakes (h (sel S)) S ≤ mistakes (h j) S) :
    sampleLaw D c m {S | ε + γ < errorOf D c (h (sel S))} ≤
      ENNReal.ofReal (2 * k * Real.exp (-(m * γ ^ 2 / 2))) := by
  classical
  haveI := cb_prob c hc D
  haveI : IsProbabilityMeasure (sampleLaw D c m) := by unfold sampleLaw; infer_instance
  obtain ⟨j0, hj0⟩ := hex
  have hk : (1:ℝ) ≤ k := by
    have : 0 < k := Fin.pos j0
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    calc sampleLaw D c 0 {S | ε + γ < errorOf D c (h (sel S))} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal (2 * k * Real.exp (-(((0:ℕ):ℝ) * γ ^ 2 / 2))) := by
          rw [← ENNReal.ofReal_one]
          apply ENNReal.ofReal_le_ofReal
          simp only [Nat.cast_zero, zero_mul, zero_div, neg_zero, Real.exp_zero, mul_one]
          linarith
  have hmR : (0:ℝ) < m := by exact_mod_cast hmpos
  set Z : Fin k → X × Bool → ℝ := fun j q => if h j q.1 ≠ q.2 then 1 else 0 with hZ
  set Zc : Fin k → X × Bool → ℝ := fun j q => 1 - Z j q with hZc
  have hφ : Measurable (fun x : X => (x, c x)) := measurable_id.prodMk hc
  have hZm : ∀ j, Measurable (Z j) := fun j =>
    Measurable.ite (measurableSet_eq_fun ((hh j).comp measurable_fst) measurable_snd).compl
      measurable_const measurable_const
  have hZcm : ∀ j, Measurable (Zc j) := fun j => measurable_const.sub (hZm j)
  have hZ01 : ∀ j q, Z j q ∈ Set.Icc (0:ℝ) 1 := by
    intro j q; simp only [hZ]; split_ifs <;> simp
  have hZc01 : ∀ j q, Zc j q ∈ Set.Icc (0:ℝ) 1 := by
    intro j q; simp only [hZc, hZ]; split_ifs <;> simp
  have hEZ : ∀ j, ∫ q, Z j q ∂(exampleLaw D c) = errorOf D c (h j) := by
    intro j
    rw [exampleLaw, integral_map hφ.aemeasurable (hZm j).aestronglyMeasurable]
    have e : (fun x : X => Z j (x, c x)) = {x | h j x ≠ c x}.indicator 1 := by
      funext x; simp [hZ, Set.indicator_apply]
    rw [e, integral_indicator_one
      (show MeasurableSet {x | h j x ≠ c x} from (measurableSet_eq_fun (hh j) hc).compl)]
    rfl
  have hEZc : ∀ j, ∫ q, Zc j q ∂(exampleLaw D c) = 1 - errorOf D c (h j) := by
    intro j
    simp only [hZc]
    rw [integral_sub (integrable_const 1) (Integrable.of_mem_Icc 0 1 (hZm j).aemeasurable
      (Filter.Eventually.of_forall (hZ01 j))), integral_const, hEZ]
    simp
  set t : ℝ := m * γ / 2 with ht
  have ht0 : 0 ≤ t := by positivity
  set A : Fin k → Set (Fin m → X × Bool) :=
    fun j => {S | t ≤ ∑ i, (Z j (S i) - ∫ q, Z j q ∂(exampleLaw D c))} with hA
  set B : Fin k → Set (Fin m → X × Bool) :=
    fun j => {S | t ≤ ∑ i, (Zc j (S i) - ∫ q, Zc j q ∂(exampleLaw D c))} with hB
  have hmist : ∀ (j : Fin k) (S : Fin m → X × Bool), (mistakes (h j) S : ℝ) = ∑ i, Z j (S i) := by
    intro j S
    unfold mistakes
    rw [Finset.natCast_card_filter]
  have hsub : {S | ε + γ < errorOf D c (h (sel S))} ⊆ ⋃ j, (A j ∪ B j) := by
    intro S hS
    by_contra hno
    simp only [Set.mem_iUnion, Set.mem_union, not_exists, not_or] at hno
    have hup : ∀ j, (mistakes (h j) S : ℝ) - m * errorOf D c (h j) < t := by
      intro j
      have h1 := (hno j).1
      simp only [hA, Set.mem_setOf_eq, not_le] at h1
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hEZ] at h1
      rw [hmist]; linarith
    have hlow : ∀ j, m * errorOf D c (h j) - (mistakes (h j) S : ℝ) < t := by
      intro j
      have h1 := (hno j).2
      simp only [hB, Set.mem_setOf_eq, not_le] at h1
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hEZc] at h1
      have e : ∑ i, Zc j (S i) = m - ∑ i, Z j (S i) := by
        simp only [hZc, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [e] at h1
      rw [hmist]; linarith
    have hselm : (mistakes (h (sel S)) S : ℝ) ≤ mistakes (h j0) S := by exact_mod_cast hsel S j0
    have h1 := hlow (sel S)
    have h2 := hup j0
    simp only [Set.mem_setOf_eq] at hS
    have h3 : (m:ℝ) * errorOf D c (h j0) ≤ m * ε := mul_le_mul_of_nonneg_left hj0 hmR.le
    have h4 : (m:ℝ) * errorOf D c (h (sel S)) < m * (ε + γ) := by
      have : t + t = m * γ := by rw [ht]; ring
      nlinarith
    have := lt_of_mul_lt_mul_left h4 hmR.le
    linarith
  have hb : ∀ j, sampleLaw D c m (A j) ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2 / m))) :=
    fun j => cb_hoeff' c hc D (Z j) (hZm j) (hZ01 j) m hmpos t ht0
  have hb' : ∀ j, sampleLaw D c m (B j) ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2 / m))) :=
    fun j => cb_hoeff' c hc D (Zc j) (hZcm j) (hZc01 j) m hmpos t ht0
  have hexp : -(2 * t ^ 2 / m) = -(m * γ ^ 2 / 2) := by rw [ht]; field_simp
  calc sampleLaw D c m {S | ε + γ < errorOf D c (h (sel S))}
      ≤ sampleLaw D c m (⋃ j, (A j ∪ B j)) := measure_mono hsub
    _ ≤ ∑ j, sampleLaw D c m (A j ∪ B j) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ j, (sampleLaw D c m (A j) + sampleLaw D c m (B j)) :=
        Finset.sum_le_sum fun j _ => measure_union_le _ _
    _ ≤ ∑ j : Fin k, (ENNReal.ofReal (Real.exp (-(2 * t ^ 2 / m))) +
          ENNReal.ofReal (Real.exp (-(2 * t ^ 2 / m)))) :=
        Finset.sum_le_sum fun j _ => add_le_add (hb j) (hb' j)
    _ = ENNReal.ofReal (∑ j : Fin k, (Real.exp (-(2 * t ^ 2 / m)) +
          Real.exp (-(2 * t ^ 2 / m)))) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
        exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_add (by positivity)
          (by positivity)).symm
    _ = ENNReal.ofReal (2 * k * Real.exp (-(m * γ ^ 2 / 2))) := by
        congr 1
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hexp]
        ring

theorem cb_main (c : X → Bool) (hc : Measurable c)
    (D : Measure X) [IsProbabilityMeasure D] {ε : ℝ} :
    (∀ (m : ℕ) (L : (Fin m → X × Bool) → X → Bool) {δ₀ : ℝ}, 0 ≤ δ₀ → δ₀ ≤ 1 →
      sampleLaw D c m {S | ε < errorOf D c (L S)} ≤ ENNReal.ofReal (1 - δ₀) →
      ∀ k : ℕ, blockSampleLaw D c k m {B | ∀ i, ε < errorOf D c (L (B i))} ≤
        ENNReal.ofReal ((1 - δ₀) ^ k)) ∧
    (∀ (k : ℕ) (h : Fin k → X → Bool), (∀ i, Measurable (h i)) →
      (∃ i, errorOf D c (h i) ≤ ε) →
      ∀ {γ : ℝ}, 0 < γ → ∀ (m : ℕ) (sel : (Fin m → X × Bool) → Fin k),
        (∀ S j, mistakes (h (sel S)) S ≤ mistakes (h j) S) →
        sampleLaw D c m {S | ε + γ < errorOf D c (h (sel S))} ≤
          ENNReal.ofReal (2 * k * Real.exp (-(m * γ ^ 2 / 2)))) :=
  ⟨fun m L _ h0 h1 hL k => cb_part1 c hc D m L h0 h1 hL k,
    fun k h hh hex _ hγ m sel hsel => cb_part2 c hc D k h hh hex hγ m sel hsel⟩

end Confidence

end ComputationalLearning

open ComputationalLearning

theorem solution {X : Type*} [MeasurableSpace X] (c : X → Bool) (hc : Measurable c)
    (D : Measure X) [IsProbabilityMeasure D] {ε : ℝ} :
    (∀ (m : ℕ) (L : (Fin m → X × Bool) → X → Bool) {δ₀ : ℝ}, 0 ≤ δ₀ → δ₀ ≤ 1 →
      sampleLaw D c m {S | ε < errorOf D c (L S)} ≤ ENNReal.ofReal (1 - δ₀) →
      ∀ k : ℕ, blockSampleLaw D c k m {B | ∀ i, ε < errorOf D c (L (B i))} ≤
        ENNReal.ofReal ((1 - δ₀) ^ k)) ∧
    (∀ (k : ℕ) (h : Fin k → X → Bool), (∀ i, Measurable (h i)) → (∃ i, errorOf D c (h i) ≤ ε) →
      ∀ {γ : ℝ}, 0 < γ → ∀ (m : ℕ) (sel : (Fin m → X × Bool) → Fin k),
        (∀ S j, mistakes (h (sel S)) S ≤ mistakes (h j) S) →
        sampleLaw D c m {S | ε + γ < errorOf D c (h (sel S))} ≤
          ENNReal.ofReal (2 * k * Real.exp (-(m * γ ^ 2 / 2)))) := by
  exact cb_main c hc D
