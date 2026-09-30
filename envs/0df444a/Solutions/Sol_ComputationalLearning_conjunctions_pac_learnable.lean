-- Prove2me | solution 1 for ComputationalLearning.conjunctions_pac_learnable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T02:44:48.249746+00:00
-- url     : https://prove2.me/submissions/eabe96bd-70df-4fbb-9419-36d4a8e0a823

import Mathlib
import Definitions.Def_ComputationalLearning_PAC

open MeasureTheory

open MeasureTheory

namespace ComputationalLearning

lemma cl_meas {n : ℕ} (s : Set (Cube (Fin n) × Bool)) : MeasurableSet s :=
  (Set.to_countable s).measurableSet

lemma cl_meas' {n : ℕ} (s : Set (Cube (Fin n))) : MeasurableSet s :=
  (Set.to_countable s).measurableSet

lemma cl_sub {n m : ℕ} (T : Conjunction (Fin n)) (S : Fin m → Cube (Fin n) × Bool)
    (hS : IsLabeledBy (evalConj T) S) : T ⊆ eliminate S := by
  intro l hl
  simp only [eliminate, Finset.mem_filter, Finset.mem_univ, true_and]
  intro j hj
  have h2 : evalConj T (S j).1 = true := by rw [← hS j, hj]
  simp only [evalConj, decide_eq_true_eq] at h2
  exact h2 l hl

lemma cl_consistent {n m : ℕ} (T : Conjunction (Fin n)) (S : Fin m → Cube (Fin n) × Bool)
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

theorem cl_bound {n : ℕ} (T : Conjunction (Fin n)) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 2 * n / ε * (Real.log (2 * n) + Real.log (1 / δ)) ≤ m) :
    sampleLaw D (evalConj T) m {S | ε < errorOf D (evalConj T) (evalConj (eliminate S))} ≤
      ENNReal.ofReal δ := by
  classical
  set c := evalConj T with hc
  haveI : IsProbabilityMeasure (exampleLaw D c) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  -- unlabeled samples form a null set
  have hnull : sampleLaw D c m {S | ¬ IsLabeledBy c S} = 0 := by
    have e : {S : Fin m → Cube (Fin n) × Bool | ¬ IsLabeledBy c S} =
        ⋃ j, (fun S : Fin m → Cube (Fin n) × Bool => S j) ⁻¹' {p | p.2 ≠ c p.1} := by
      ext S; simp [IsLabeledBy]
    rw [e]
    refine measure_iUnion_null fun j => ?_
    apply Measure.pi_eval_preimage_null
    rw [exampleLaw, Measure.map_apply (measurable_of_countable _) (cl_meas _)]
    simp
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hempty : ∀ U : Conjunction (Fin 0), U = ∅ :=
      fun U => Finset.eq_empty_of_forall_notMem (fun l _ => l.1.elim0)
    have : {S : Fin m → Cube (Fin 0) × Bool | ε < errorOf D c (evalConj (eliminate S))} = ∅ := by
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have h1 : ∀ x : Cube (Fin 0), evalConj (eliminate S) x = c x := by
        intro x
        rw [hc, hempty (eliminate S), hempty T]
      simp [errorOf, h1, hε.le]
    rw [this, measure_empty]; exact bot_le
  have hn : (0:ℝ) < n := by exact_mod_cast hnpos
  set q : ℝ := ε / (2 * n) with hq
  have hqpos : 0 < q := by positivity
  set pz : Fin n × Bool → ℝ := fun z => D.real {x | c x = true ∧ x z.1 ≠ z.2} with hpz
  set Bad : Finset (Fin n × Bool) := Finset.univ.filter (fun z => q < pz z) with hBad
  set A : Fin n × Bool → Set (Cube (Fin n) × Bool) :=
    fun z => {p | p.2 = true → p.1 z.1 = z.2} with hAdef
  have hsub : {S | ε < errorOf D c (evalConj (eliminate S))} ⊆
      {S | ¬ IsLabeledBy c S} ∪ ⋃ z ∈ Bad, Set.univ.pi (fun _ : Fin m => A z) := by
    intro S hS
    by_cases hlab : IsLabeledBy c S
    · right
      have hT := cl_sub T S hlab
      have hset : {x | evalConj (eliminate S) x ≠ c x} ⊆
          ⋃ z ∈ eliminate S, {x | c x = true ∧ x z.1 ≠ z.2} := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        have hh : evalConj (eliminate S) x = false := by
          by_contra hne
          have htrue : evalConj (eliminate S) x = true := by simpa using hne
          have hcx : c x = true := by
            simp only [hc, evalConj, decide_eq_true_eq] at htrue ⊢
            exact fun l hl => htrue l (hT hl)
          exact hx (htrue.trans hcx.symm)
        have hcx : c x = true := by
          cases hcc : c x
          · exact absurd (hh.trans hcc.symm) hx
          · rfl
        simp only [evalConj, decide_eq_false_iff_not, not_forall] at hh
        obtain ⟨z, hz, hxz⟩ := hh
        rw [Set.mem_iUnion₂]
        exact ⟨z, hz, hcx, hxz⟩
      have herr : errorOf D c (evalConj (eliminate S)) ≤ ∑ z ∈ eliminate S, pz z := by
        unfold errorOf
        calc (D {x | evalConj (eliminate S) x ≠ c x}).toReal
            ≤ (D (⋃ z ∈ eliminate S, {x | c x = true ∧ x z.1 ≠ z.2})).toReal :=
              ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hset)
          _ ≤ ∑ z ∈ eliminate S, pz z := measureReal_biUnion_finset_le _ _
      have hbad : ∃ z ∈ eliminate S, q < pz z := by
        by_contra hno
        push Not at hno
        have h1 : ∑ z ∈ eliminate S, pz z ≤ ∑ z ∈ eliminate S, q := Finset.sum_le_sum hno
        have hcard : ((eliminate S).card : ℝ) ≤ 2 * n := by
          have : (eliminate S).card ≤ 2 * n := by
            calc (eliminate S).card ≤ (Finset.univ : Finset (Fin n × Bool)).card :=
                  Finset.card_le_univ _
              _ = 2 * n := by simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring
          exact_mod_cast this
        rw [Finset.sum_const, nsmul_eq_mul] at h1
        have h2 : ((eliminate S).card : ℝ) * q ≤ ε := by
          calc _ ≤ (2 * n : ℝ) * q := mul_le_mul_of_nonneg_right hcard hqpos.le
            _ = ε := by rw [hq]; field_simp
        simp only [Set.mem_setOf_eq] at hS
        linarith
      obtain ⟨z, hz, hzbad⟩ := hbad
      rw [Set.mem_iUnion₂]
      refine ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzbad⟩, ?_⟩
      intro j _
      simp only [eliminate, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact hz j
    · left; exact hlab
  have hL : Real.log (2 * n) + Real.log (1 / δ) ≤ q * m := by
    have h1 := mul_le_mul_of_nonneg_left hm hqpos.le
    have e : q * (2 * n / ε * (Real.log (2 * n) + Real.log (1 / δ))) =
        Real.log (2 * n) + Real.log (1 / δ) := by rw [hq]; field_simp
    linarith
  have hbadbound : ∀ z ∈ Bad, sampleLaw D c m (Set.univ.pi (fun _ : Fin m => A z)) ≤
      ENNReal.ofReal (δ / (2 * n)) := by
    intro z hz
    have hzq : q < pz z := (Finset.mem_filter.mp hz).2
    have hp1 : pz z ≤ 1 := by
      simp only [hpz]
      exact measureReal_le_one
    rw [sampleLaw, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hA : exampleLaw D c (A z) = ENNReal.ofReal (1 - pz z) := by
      rw [exampleLaw, Measure.map_apply (measurable_of_countable _) (cl_meas _)]
      have hpre : (fun x => (x, c x)) ⁻¹' (A z) = {x | c x = true ∧ x z.1 ≠ z.2}ᶜ := by
        ext x
        simp only [hAdef, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_compl_iff, not_and,
          not_not]
      rw [hpre, prob_compl_eq_one_sub (cl_meas' _)]
      simp only [hpz, Measure.real]
      rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [hA, ← ENNReal.ofReal_pow (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    have hq1 : q ≤ 1 := by linarith
    calc (1 - pz z) ^ m ≤ (1 - q) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ ≤ (Real.exp (-q)) ^ m :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-q)]) m
      _ = Real.exp (-(q * m)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(Real.log (2 * n) + Real.log (1 / δ))) := Real.exp_le_exp.mpr (by linarith)
      _ = δ / (2 * n) := by
          rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log (by positivity),
            Real.exp_log (by positivity)]
          field_simp
  calc sampleLaw D c m {S | ε < errorOf D c (evalConj (eliminate S))}
      ≤ sampleLaw D c m ({S | ¬ IsLabeledBy c S} ∪
          ⋃ z ∈ Bad, Set.univ.pi (fun _ : Fin m => A z)) := measure_mono hsub
    _ ≤ sampleLaw D c m {S | ¬ IsLabeledBy c S} +
          sampleLaw D c m (⋃ z ∈ Bad, Set.univ.pi (fun _ : Fin m => A z)) := measure_union_le _ _
    _ = sampleLaw D c m (⋃ z ∈ Bad, Set.univ.pi (fun _ : Fin m => A z)) := by
          rw [hnull, zero_add]
    _ ≤ ∑ z ∈ Bad, sampleLaw D c m (Set.univ.pi (fun _ : Fin m => A z)) :=
          measure_biUnion_finset_le _ _
    _ ≤ ∑ z ∈ Bad, ENNReal.ofReal (δ / (2 * n)) := Finset.sum_le_sum hbadbound
    _ = ENNReal.ofReal (∑ z ∈ Bad, δ / (2 * n)) :=
          (ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)).symm
    _ ≤ ENNReal.ofReal δ := by
          apply ENNReal.ofReal_le_ofReal
          rw [Finset.sum_const, nsmul_eq_mul]
          have hcard : (Bad.card : ℝ) ≤ 2 * n := by
            have : Bad.card ≤ 2 * n := by
              calc Bad.card ≤ (Finset.univ : Finset (Fin n × Bool)).card := Finset.card_le_univ _
                _ = 2 * n := by simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; ring
            exact_mod_cast this
          calc (Bad.card : ℝ) * (δ / (2 * n)) ≤ (2 * n) * (δ / (2 * n)) :=
                mul_le_mul_of_nonneg_right hcard (by positivity)
            _ = δ := by field_simp

theorem cl_main {n : ℕ} (T : Conjunction (Fin n)) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 2 * n / ε * (Real.log (2 * n) + Real.log (1 / δ)) ≤ m) :
    (∀ S : Fin m → Cube (Fin n) × Bool, IsLabeledBy (evalConj T) S →
      IsConsistent (evalConj (eliminate S)) S) ∧
    sampleLaw D (evalConj T) m {S | ε < errorOf D (evalConj T) (evalConj (eliminate S))} ≤
      ENNReal.ofReal δ ∧
    PACLearnable (conjunctionClass (Fin n)) (conjunctionClass (Fin n)) := by
  refine ⟨fun S hS => cl_consistent T S hS, cl_bound T D hε hδ hδ1 m hm, ?_⟩
  intro ε' δ' hε' _ hδ' hδ'2
  refine ⟨⌈2 * n / ε' * (Real.log (2 * n) + Real.log (1 / δ'))⌉₊,
    fun S => evalConj (eliminate S), fun S => ⟨eliminate S, rfl⟩, ?_⟩
  intro c' hc' _ D' hD'
  obtain ⟨T', rfl⟩ := hc'
  haveI := hD'
  exact cl_bound T' D' hε' hδ' (by linarith) _ (Nat.le_ceil _)

end ComputationalLearning

open ComputationalLearning

theorem solution {n : ℕ} (T : Conjunction (Fin n)) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 2 * n / ε * (Real.log (2 * n) + Real.log (1 / δ)) ≤ m) :
    (∀ S : Fin m → Cube (Fin n) × Bool, IsLabeledBy (evalConj T) S →
      IsConsistent (evalConj (eliminate S)) S) ∧
    sampleLaw D (evalConj T) m {S | ε < errorOf D (evalConj T) (evalConj (eliminate S))} ≤
      ENNReal.ofReal δ ∧
    PACLearnable (conjunctionClass (Fin n)) (conjunctionClass (Fin n)) := by
  exact cl_main T D hε hδ hδ1 m hm
