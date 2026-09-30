-- Prove2me | solution 1 for ComputationalLearning.conjunctions_occam_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T03:20:02.11314+00:00
-- url     : https://prove2.me/submissions/8b01683d-e1f3-4616-892e-4b017da2ef11

import Mathlib
import Definitions.Def_ComputationalLearning_Occam

open MeasureTheory

namespace ComputationalLearning

section OccamCard

variable {X : Type*} [MeasurableSpace X]

lemma oc_single (c : X → Bool) (hc : Measurable c) (D : Measure X) [IsProbabilityMeasure D]
    (h : X → Bool) (hh : Measurable h) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (herr : ε < errorOf D c h) (m : ℕ) :
    sampleLaw D c m {S | IsConsistent h S} ≤ ENNReal.ofReal ((1 - ε) ^ m) := by
  have hφ : Measurable (fun x : X => (x, c x)) := measurable_id.prodMk hc
  haveI : IsProbabilityMeasure (exampleLaw D c) :=
    Measure.isProbabilityMeasure_map hφ.aemeasurable
  have hset : {S : Fin m → X × Bool | IsConsistent h S} =
      Set.univ.pi (fun _ => {q : X × Bool | h q.1 = q.2}) := by
    ext S; simp [IsConsistent, Set.mem_pi]
  rw [hset, sampleLaw, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hA : exampleLaw D c {q : X × Bool | h q.1 = q.2} = 1 - D {x | h x ≠ c x} := by
    rw [exampleLaw, Measure.map_apply hφ (show MeasurableSet {q : X × Bool | h q.1 = q.2} from
      measurableSet_eq_fun (hh.comp measurable_fst) measurable_snd)]
    have : (fun x : X => (x, c x)) ⁻¹' {q : X × Bool | h q.1 = q.2} = {x | h x ≠ c x}ᶜ := by
      ext x; simp
    rw [this, prob_compl_eq_one_sub
      (show MeasurableSet {x | h x ≠ c x} from (measurableSet_eq_fun hh hc).compl)]
  rw [hA]
  have h1 : 1 - D {x | h x ≠ c x} ≤ ENNReal.ofReal (1 - ε) := by
    rw [ENNReal.ofReal_sub 1 hε.le, ENNReal.ofReal_one]
    exact tsub_le_tsub_left (ENNReal.ofReal_le_of_le_toReal herr.le) 1
  calc (1 - D {x | h x ≠ c x}) ^ m ≤ ENNReal.ofReal (1 - ε) ^ m := pow_le_pow_left₀ zero_le h1 m
    _ = ENNReal.ofReal ((1 - ε) ^ m) := (ENNReal.ofReal_pow (by linarith) m).symm

theorem oc_bad (c : X → Bool) (hc : Measurable c) (D : Measure X) [IsProbabilityMeasure D]
    (H : Finset (X → Bool)) (hH : ∀ h ∈ H, Measurable h) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (m : ℕ) :
    sampleLaw D c m {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} ≤
      ENNReal.ofReal (H.card * (1 - ε) ^ m) := by
  classical
  set H' := H.filter (fun h => ε < errorOf D c h) with hH'
  have hsub : {S : Fin m → X × Bool | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} ⊆
      ⋃ h ∈ H', {S | IsConsistent h S} := by
    rintro S ⟨h, hh, hcons, herr⟩
    exact Set.mem_iUnion₂.mpr ⟨h, Finset.mem_filter.mpr ⟨hh, herr⟩, hcons⟩
  calc sampleLaw D c m {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h}
      ≤ sampleLaw D c m (⋃ h ∈ H', {S | IsConsistent h S}) := measure_mono hsub
    _ ≤ ∑ h ∈ H', sampleLaw D c m {S | IsConsistent h S} := measure_biUnion_finset_le _ _
    _ ≤ ∑ h ∈ H', ENNReal.ofReal ((1 - ε) ^ m) := Finset.sum_le_sum fun h hh =>
          oc_single c hc D h (hH h (Finset.mem_filter.mp hh).1) hε hε1
            (Finset.mem_filter.mp hh).2 m
    _ = ENNReal.ofReal (H'.card * (1 - ε) ^ m) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (H.card * (1 - ε) ^ m) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) m)
          exact_mod_cast Finset.card_filter_le _ _

/-- `K (1 − ε)^m ≤ δ` once `m ≥ (1/ε)(ln K + ln(1/δ))`. -/
lemma oc_real {K ε δ : ℝ} (hK : 0 < K) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (m : ℕ)
    (hm : 1 / ε * (Real.log K + Real.log (1 / δ)) ≤ m) : K * (1 - ε) ^ m ≤ δ := by
  calc K * (1 - ε) ^ m ≤ K * Real.exp (-(ε * m)) := by
        apply mul_le_mul_of_nonneg_left _ hK.le
        calc (1 - ε) ^ m ≤ (Real.exp (-ε)) ^ m :=
              pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-ε)]) m
          _ = Real.exp (-(ε * m)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ K * Real.exp (-(Real.log K + Real.log (1 / δ))) := by
        apply mul_le_mul_of_nonneg_left _ hK.le
        apply Real.exp_le_exp.mpr
        have := mul_le_mul_of_nonneg_left hm hε.le
        have e : ε * (1 / ε * (Real.log K + Real.log (1 / δ))) =
            Real.log K + Real.log (1 / δ) := by field_simp
        linarith
    _ = δ := by
        rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hK,
          Real.exp_log (by positivity)]
        field_simp

lemma oc_null (c : X → Bool) (hc : Measurable c) (D : Measure X) [IsProbabilityMeasure D]
    (m : ℕ) : sampleLaw D c m {S | ¬ IsLabeledBy c S} = 0 := by
  have hφ : Measurable (fun x : X => (x, c x)) := measurable_id.prodMk hc
  haveI : IsProbabilityMeasure (exampleLaw D c) :=
    Measure.isProbabilityMeasure_map hφ.aemeasurable
  have e : {S : Fin m → X × Bool | ¬ IsLabeledBy c S} =
      ⋃ j, (fun S : Fin m → X × Bool => S j) ⁻¹' {p | p.2 ≠ c p.1} := by
    ext S; simp [IsLabeledBy]
  rw [e]
  refine measure_iUnion_null fun j => ?_
  apply Measure.pi_eval_preimage_null
  have hms : MeasurableSet {p : X × Bool | p.2 ≠ c p.1} :=
    (measurableSet_eq_fun measurable_snd (hc.comp measurable_fst)).compl
  rw [exampleLaw, Measure.map_apply hφ hms]
  simp

theorem oc_main (c : X → Bool) (hc : Measurable c)
    (D : Measure X) [IsProbabilityMeasure D] (H : Finset (X → Bool)) (hH : ∀ h ∈ H, Measurable h)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (m : ℕ) :
    sampleLaw D c m {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} ≤
      ENNReal.ofReal (H.card * (1 - ε) ^ m) ∧
    (1 / ε * (Real.log H.card + Real.log (1 / δ)) ≤ m →
      sampleLaw D c m {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} ≤ ENNReal.ofReal δ) ∧
    (∀ L : (Fin m → X × Bool) → X → Bool, (∀ S, L S ∈ H) →
      (∀ S, IsLabeledBy c S → IsConsistent (L S) S) →
      sampleLaw D c m {S | ε < errorOf D c (L S)} ≤ ENNReal.ofReal (H.card * (1 - ε) ^ m)) := by
  refine ⟨oc_bad c hc D H hH hε hε1 m, fun hm => ?_, fun L hLH hLcons => ?_⟩
  · refine (oc_bad c hc D H hH hε hε1 m).trans (ENNReal.ofReal_le_ofReal ?_)
    rcases Nat.eq_zero_or_pos H.card with h0 | hpos
    · rw [h0]; simp only [Nat.cast_zero, zero_mul]; exact hδ.le
    · exact oc_real (by exact_mod_cast hpos) hε hε1 hδ m hm
  · have hsub : {S : Fin m → X × Bool | ε < errorOf D c (L S)} ⊆ {S | ¬ IsLabeledBy c S} ∪
        {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} := by
      intro S hS
      by_cases hlab : IsLabeledBy c S
      · exact Or.inr ⟨L S, hLH S, hLcons S hlab, hS⟩
      · exact Or.inl hlab
    calc sampleLaw D c m {S | ε < errorOf D c (L S)}
        ≤ sampleLaw D c m ({S | ¬ IsLabeledBy c S} ∪
            {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h}) := measure_mono hsub
      _ ≤ sampleLaw D c m {S | ¬ IsLabeledBy c S} +
            sampleLaw D c m {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D c h} :=
          measure_union_le _ _
      _ ≤ 0 + ENNReal.ofReal (H.card * (1 - ε) ^ m) := by
          rw [oc_null c hc D m]
          gcongr
          exact oc_bad c hc D H hH hε hε1 m
      _ = ENNReal.ofReal (H.card * (1 - ε) ^ m) := zero_add _

end OccamCard

section ConjCount

variable {n : ℕ}

lemma cl_sub {m : ℕ} (T : Conjunction (Fin n)) (S : Fin m → Cube (Fin n) × Bool)
    (hS : IsLabeledBy (evalConj T) S) : T ⊆ eliminate S := by
  intro l hl
  simp only [eliminate, Finset.mem_filter, Finset.mem_univ, true_and]
  intro j hj
  have h2 : evalConj T (S j).1 = true := by rw [← hS j, hj]
  simp only [evalConj, decide_eq_true_eq] at h2
  exact h2 l hl

lemma cl_consistent {m : ℕ} (T : Conjunction (Fin n)) (S : Fin m → Cube (Fin n) × Bool)
    (hS : IsLabeledBy (evalConj T) S) : IsConsistent (evalConj (eliminate S)) S := by
  intro i
  have hsub := cl_sub T S hS
  cases h : (S i).2
  · have hT : evalConj T (S i).1 = false := by rw [← hS i, h]
    simp only [evalConj, decide_eq_false_iff_not] at hT ⊢
    intro hall
    exact hT fun l hl => hall l (hsub hl)
  · simp only [evalConj, decide_eq_true_eq]
    intro l hl
    simp only [eliminate, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    exact hl i h

/-- The code of a conjunction: `none` if it is contradictory, otherwise the partial assignment
it requires. -/
def conjCode (E : Conjunction (Fin n)) : Option (Fin n → Option Bool) :=
  if ∃ i, (i, true) ∈ E ∧ (i, false) ∈ E then none
  else some (fun i => if (i, true) ∈ E then some true else if (i, false) ∈ E then some false
    else none)

/-- The concept of a code. -/
def codeEval : Option (Fin n → Option Bool) → Cube (Fin n) → Bool
  | none => fun _ => false
  | some σ => fun a => decide (∀ i, ∀ b, σ i = some b → a i = b)

lemma evalConj_eq_codeEval (E : Conjunction (Fin n)) : evalConj E = codeEval (conjCode E) := by
  funext a
  unfold conjCode
  split_ifs with hcon
  · obtain ⟨i, h1, h2⟩ := hcon
    simp only [codeEval, evalConj, decide_eq_false_iff_not]
    intro hall
    have e1 : a i = true := hall _ h1
    have e2 : a i = false := hall _ h2
    rw [e1] at e2
    exact Bool.noConfusion e2
  · push Not at hcon
    rw [Bool.eq_iff_iff]
    simp only [codeEval, evalConj, decide_eq_true_eq]
    constructor
    · intro hall i b hσ
      by_cases h1 : (i, true) ∈ E
      · rw [if_pos h1] at hσ
        cases hσ
        exact hall _ h1
      · rw [if_neg h1] at hσ
        by_cases h2 : (i, false) ∈ E
        · rw [if_pos h2] at hσ
          cases hσ
          exact hall _ h2
        · rw [if_neg h2] at hσ
          simp at hσ
    · intro hσ l hl
      obtain ⟨i, b⟩ := l
      cases b
      · have hnt : (i, true) ∉ E := fun h => hcon i h hl
        exact hσ i false (by rw [if_neg hnt, if_pos hl])
      · exact hσ i true (by rw [if_pos hl])

lemma card_conj_image :
    ((Finset.univ : Finset (Conjunction (Fin n))).image evalConj).card ≤ 3 ^ n + 1 := by
  classical
  calc ((Finset.univ : Finset (Conjunction (Fin n))).image evalConj).card
      ≤ ((Finset.univ : Finset (Option (Fin n → Option Bool))).image codeEval).card := by
        apply Finset.card_le_card
        intro h hh
        obtain ⟨E, _, rfl⟩ := Finset.mem_image.mp hh
        exact Finset.mem_image.mpr ⟨conjCode E, Finset.mem_univ _, (evalConj_eq_codeEval E).symm⟩
    _ ≤ (Finset.univ : Finset (Option (Fin n → Option Bool))).card := Finset.card_image_le
    _ = 3 ^ n + 1 := by simp [Fintype.card_option, Fintype.card_fin]

theorem conj_occam (T : Conjunction (Fin n)) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (m : ℕ)
    (hm : 1 / ε * (Real.log (3 ^ n + 1) + Real.log (1 / δ)) ≤ m) :
    sampleLaw D (evalConj T) m {S | ε < errorOf D (evalConj T) (evalConj (eliminate S))} ≤
      ENNReal.ofReal δ := by
  classical
  set H := (Finset.univ : Finset (Conjunction (Fin n))).image evalConj with hHdef
  have h3 := (oc_main (evalConj T) (measurable_of_countable _) D H
    (fun h _ => measurable_of_countable _) hε hε1 hδ m).2.2
    (fun S => evalConj (eliminate S)) (fun S => Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)
    (fun S hS => cl_consistent T S hS)
  refine h3.trans (ENNReal.ofReal_le_ofReal ?_)
  have hK : (H.card : ℝ) ≤ 3 ^ n + 1 := by exact_mod_cast card_conj_image
  have hpos : (0:ℝ) < 3 ^ n + 1 := by positivity
  calc (H.card : ℝ) * (1 - ε) ^ m ≤ (3 ^ n + 1) * (1 - ε) ^ m :=
        mul_le_mul_of_nonneg_right hK (pow_nonneg (by linarith) m)
    _ ≤ δ := oc_real hpos hε hε1 hδ m hm

end ConjCount

end ComputationalLearning

open ComputationalLearning

theorem solution {n : ℕ} (T : Conjunction (Fin n)) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (m : ℕ)
    (hm : 1 / ε * (Real.log (3 ^ n + 1) + Real.log (1 / δ)) ≤ m) :
    sampleLaw D (evalConj T) m {S | ε < errorOf D (evalConj T) (evalConj (eliminate S))} ≤
      ENNReal.ofReal δ := by
  exact conj_occam T D hε hε1 hδ m hm
