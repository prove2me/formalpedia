-- Prove2me | solution 1 for ComputationalLearning.noisy_query_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T03:31:17.983125+00:00
-- url     : https://prove2.me/submissions/786774a2-ec41-48a7-88f4-39466695a98a

import Mathlib
import Definitions.Def_ComputationalLearning_Noise

open MeasureTheory ProbabilityTheory

namespace ComputationalLearning

section NoisyQuery

variable {X : Type*} [MeasurableSpace X]

/-- The noisy oracle as a mixture: with weight `η` the flipped label, with weight `1 − η` the
correct one. -/
lemma noisy_eq (μ : Measure X) [SFinite μ] (c : X → Bool) (hc : Measurable c) (η : ℝ) :
    noisyExampleLaw μ c η = ENNReal.ofReal η • μ.map (fun x => (x, !c x)) +
      ENNReal.ofReal (1 - η) • μ.map (fun x => (x, c x)) := by
  have hF : Measurable (fun p : X × Bool => (p.1, if p.2 then !c p.1 else c p.1)) := by
    apply measurable_fst.prodMk
    exact Measurable.ite (measurable_snd (measurableSet_singleton true))
      ((measurable_of_countable not).comp (hc.comp measurable_fst)) (hc.comp measurable_fst)
  have hT : Measurable (fun x : X => (x, true)) := measurable_id.prodMk measurable_const
  have hFa : Measurable (fun x : X => (x, false)) := measurable_id.prodMk measurable_const
  unfold noisyExampleLaw bernoulliMeasure
  rw [Measure.prod_add, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_dirac,
    Measure.prod_dirac, Measure.map_add _ _ hF, Measure.map_smul, Measure.map_smul,
    Measure.map_map hF hT, Measure.map_map hF hFa]
  rfl

lemma noisy_apply (μ : Measure X) [SFinite μ] (c : X → Bool) (hc : Measurable c) (η : ℝ)
    (A : Set (X × Bool)) (hA : MeasurableSet A) :
    noisyExampleLaw μ c η A = ENNReal.ofReal η * μ {x | (x, !c x) ∈ A} +
      ENNReal.ofReal (1 - η) * μ {x | (x, c x) ∈ A} := by
  have h1 : Measurable (fun x : X => (x, !c x)) :=
    measurable_id.prodMk ((measurable_of_countable not).comp hc)
  have h2 : Measurable (fun x : X => (x, c x)) := measurable_id.prodMk hc
  rw [noisy_eq μ c hc η, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply h1 hA, Measure.map_apply h2 hA, smul_eq_mul, smul_eq_mul]
  rfl

theorem nq_main (D : Measure X)
    [IsProbabilityMeasure D] (c : X → Bool) (hc : Measurable c) (χ : X × Bool → Bool)
    (hχ : Measurable χ) {η : ℝ} (hη0 : 0 ≤ η) (hη : η < 1 / 2) :
    queryProb D c χ =
      (D (labelSensitive χ)).toReal *
        ((noisyExampleLaw (D[|labelSensitive χ]) c η {p | χ p = true}).toReal - η) /
          (1 - 2 * η) +
      (noisyExampleLaw D c η {p | χ p = true ∧ p.1 ∉ labelSensitive χ}).toReal := by
  set X1 := labelSensitive χ with hX1
  set Q : Set X := {x | χ (x, c x) = true} with hQ
  have hmχ : MeasurableSet {p : X × Bool | χ p = true} := hχ (measurableSet_singleton true)
  have hX1m : MeasurableSet X1 := by
    have h1 : Measurable (fun x : X => χ (x, false)) :=
      hχ.comp (measurable_id.prodMk measurable_const)
    have h2 : Measurable (fun x : X => χ (x, true)) :=
      hχ.comp (measurable_id.prodMk measurable_const)
    exact (measurableSet_eq_fun h1 h2).compl
  have hQm : MeasurableSet Q := (hχ.comp (measurable_id.prodMk hc)) (measurableSet_singleton true)
  have hA2m : MeasurableSet {p : X × Bool | χ p = true ∧ p.1 ∉ X1} :=
    hmχ.inter (measurable_fst hX1m.compl)
  have hflip : ∀ x ∈ X1, χ (x, !c x) = !χ (x, c x) := by
    intro x hx
    have hx' : χ (x, false) ≠ χ (x, true) := hx
    cases hcx : c x <;> simp only [Bool.not_false, Bool.not_true] <;>
      cases h1 : χ (x, false) <;> cases h2 : χ (x, true) <;> simp_all
  have hsame : ∀ x ∉ X1, χ (x, !c x) = χ (x, c x) := by
    intro x hx
    have hx' : χ (x, false) = χ (x, true) := by
      by_contra h; exact hx h
    cases hcx : c x <;> simp only [Bool.not_false, Bool.not_true] <;> simp [hx']
  have hq : queryProb D c χ = (D Q).toReal := by
    have h2 : Measurable (fun x : X => (x, c x)) := measurable_id.prodMk hc
    unfold queryProb exampleLaw
    rw [Measure.map_apply h2 hmχ]
    rfl
  have hset2a : {x | (x, !c x) ∈ {p : X × Bool | χ p = true ∧ p.1 ∉ X1}} = Q ∩ X1ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, hQ]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by rw [← hsame x h2]; exact h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by rw [hsame x h2]; exact h1, h2⟩
  have hset2b : {x | (x, c x) ∈ {p : X × Bool | χ p = true ∧ p.1 ∉ X1}} = Q ∩ X1ᶜ := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, hQ]
  have hterm2 : (noisyExampleLaw D c η {p | χ p = true ∧ p.1 ∉ X1}).toReal =
      (D (Q ∩ X1ᶜ)).toReal := by
    rw [noisy_apply D c hc η _ hA2m, hset2a, hset2b, ← add_mul,
      ← ENNReal.ofReal_add hη0 (by linarith)]
    simp only [add_sub_cancel, ENNReal.ofReal_one, one_mul]
  have hsplit : (D Q).toReal = (D (X1 ∩ Q)).toReal + (D (Q ∩ X1ᶜ)).toReal := by
    have := measure_inter_add_sdiff (μ := D) Q hX1m
    rw [Set.sdiff_eq] at this
    rw [← this, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), Set.inter_comm Q X1]
  rw [hq, hterm2]
  by_cases h0 : D X1 = 0
  · have hc0 : D[|X1] = 0 := cond_eq_zero_of_meas_eq_zero h0
    rw [hc0, h0]
    have hnz : noisyExampleLaw (0 : Measure X) c η {p | χ p = true} = 0 := by
      rw [noisy_apply 0 c hc η _ hmχ]; simp
    rw [hnz]
    have h1 : D (X1 ∩ Q) = 0 := measure_mono_null Set.inter_subset_left h0
    rw [hsplit, h1]
    simp
  · have hc1 : ∀ t, D[|X1] t = (D X1)⁻¹ * D (X1 ∩ t) := fun t => cond_apply hX1m D t
    rw [noisy_apply _ c hc η _ hmχ, hc1, hc1]
    have hs1 : X1 ∩ {x | (x, !c x) ∈ {p : X × Bool | χ p = true}} = X1 ∩ Qᶜ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff, hQ]
      constructor
      · rintro ⟨hx, h⟩
        refine ⟨hx, fun hq => ?_⟩
        rw [hflip x hx, hq] at h
        exact Bool.false_ne_true h
      · rintro ⟨hx, h⟩
        refine ⟨hx, ?_⟩
        rw [hflip x hx]
        simpa using h
    have hs2 : X1 ∩ {x | (x, c x) ∈ {p : X × Bool | χ p = true}} = X1 ∩ Q := rfl
    rw [hs1, hs2]
    have hinv : (D X1)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr h0
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top hinv (measure_ne_top _ _)))
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top hinv (measure_ne_top _ _))),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_inv, ENNReal.toReal_ofReal hη0, ENNReal.toReal_ofReal (by linarith)]
    have hb : (D (X1 ∩ Qᶜ)).toReal = (D X1).toReal - (D (X1 ∩ Q)).toReal := by
      have := measure_inter_add_sdiff (μ := D) X1 hQm
      rw [Set.sdiff_eq] at this
      rw [← this, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      ring
    have hp1 : (D X1).toReal ≠ 0 := by
      rw [ENNReal.toReal_ne_zero]; exact ⟨h0, measure_ne_top _ _⟩
    have h2η : (1 - 2 * η) ≠ 0 := by linarith
    rw [hb, hsplit]
    set a := (D (X1 ∩ Q)).toReal
    set p := (D X1).toReal
    have key : p * (η * (p⁻¹ * (p - a)) + (1 - η) * (p⁻¹ * a) - η) = a * (1 - 2 * η) := by
      field_simp
      ring
    rw [key, mul_div_assoc, div_self h2η, mul_one]

end NoisyQuery

end ComputationalLearning

open ComputationalLearning

theorem solution {X : Type*} [MeasurableSpace X] (D : Measure X)
    [IsProbabilityMeasure D] (c : X → Bool) (hc : Measurable c) (χ : X × Bool → Bool)
    (hχ : Measurable χ) {η : ℝ} (hη0 : 0 ≤ η) (hη : η < 1 / 2) :
    queryProb D c χ =
      (D (labelSensitive χ)).toReal *
        ((noisyExampleLaw (D[|labelSensitive χ]) c η {p | χ p = true}).toReal - η) / (1 - 2 * η) +
      (noisyExampleLaw D c η {p | χ p = true ∧ p.1 ∉ labelSensitive χ}).toReal := by
  exact nq_main D c hc χ hχ hη0 hη
