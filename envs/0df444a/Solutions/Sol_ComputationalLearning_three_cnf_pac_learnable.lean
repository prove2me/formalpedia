-- Prove2me | solution 1 for ComputationalLearning.three_cnf_pac_learnable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T03:02:08.789793+00:00
-- url     : https://prove2.me/submissions/64abf9af-1907-4648-9037-455632c29ef8

import Mathlib
import Definitions.Def_ComputationalLearning_PAC

open MeasureTheory

namespace ComputationalLearning

section Gen

variable {X ι : Type} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
  [Fintype ι] [DecidableEq ι]

/-- The sample with every instance replaced by its feature vector `φ x`. -/
def fsample {m : ℕ} (φ : X → Cube ι) (S : Fin m → X × Bool) : Fin m → Cube ι × Bool :=
  fun j => (φ (S j).1, (S j).2)

lemma g_meas (s : Set (X × Bool)) : MeasurableSet s :=
  (Set.to_countable s).measurableSet

lemma g_meas' (s : Set X) : MeasurableSet s :=
  (Set.to_countable s).measurableSet

lemma g_sub {m : ℕ} (T : Conjunction ι) (S : Fin m → Cube ι × Bool)
    (hS : IsLabeledBy (evalConj T) S) : T ⊆ eliminate S := by
  intro l hl
  simp only [eliminate, Finset.mem_filter, Finset.mem_univ, true_and]
  intro j hj
  have h2 : evalConj T (S j).1 = true := by rw [← hS j, hj]
  simp only [evalConj, decide_eq_true_eq] at h2
  exact h2 l hl

lemma g_consistent {m : ℕ} (T : Conjunction ι) (S : Fin m → Cube ι × Bool)
    (hS : IsLabeledBy (evalConj T) S) : IsConsistent (evalConj (eliminate S)) S := by
  intro i
  have hsub := g_sub T S hS
  cases h : (S i).2
  · have hT : evalConj T (S i).1 = false := by rw [← hS i, h]
    simp only [evalConj, decide_eq_false_iff_not] at hT ⊢
    intro hall
    exact hT fun l hl => hall l (hsub hl)
  · simp only [evalConj, decide_eq_true_eq]
    intro l hl
    simp only [eliminate, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    exact hl i h

lemma card_literals : (Finset.univ : Finset (ι × Bool)).card = 2 * Fintype.card ι := by
  simp [Fintype.card_prod, Fintype.card_bool]; ring

theorem g_bound (φ : X → Cube ι) (T : Conjunction ι) (D : Measure X)
    [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (_hδ1 : δ < 1) (m : ℕ)
    (hm : 2 * (Fintype.card ι : ℝ) / ε *
      (Real.log (2 * Fintype.card ι) + Real.log (1 / δ)) ≤ m) :
    sampleLaw D (fun x => evalConj T (φ x)) m
      {S | ε < errorOf D (fun x => evalConj T (φ x))
        (fun x => evalConj (eliminate (fsample φ S)) (φ x))} ≤ ENNReal.ofReal δ := by
  classical
  set c : X → Bool := fun x => evalConj T (φ x) with hc
  set N := Fintype.card ι with hN
  haveI : IsProbabilityMeasure (exampleLaw D c) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  -- unlabeled samples form a null set
  have hnull : sampleLaw D c m {S | ¬ IsLabeledBy c S} = 0 := by
    have e : {S : Fin m → X × Bool | ¬ IsLabeledBy c S} =
        ⋃ j, (fun S : Fin m → X × Bool => S j) ⁻¹' {p | p.2 ≠ c p.1} := by
      ext S; simp [IsLabeledBy]
    rw [e]
    refine measure_iUnion_null fun j => ?_
    apply Measure.pi_eval_preimage_null
    rw [exampleLaw, Measure.map_apply (measurable_of_countable _) (g_meas _)]
    simp
  rcases Nat.eq_zero_or_pos N with hn0 | hnpos
  · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn0
    have hempty : ∀ U : Conjunction ι, U = ∅ :=
      fun U => Finset.eq_empty_of_forall_notMem (fun l _ => (IsEmpty.false l.1).elim)
    have : {S : Fin m → X × Bool | ε < errorOf D c
        (fun x => evalConj (eliminate (fsample φ S)) (φ x))} = ∅ := by
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have h1 : ∀ x : X, evalConj (eliminate (fsample φ S)) (φ x) = c x := by
        intro x
        rw [hc]
        simp only
        rw [hempty (eliminate (fsample φ S)), hempty T]
      simp [errorOf, h1, hε.le]
    rw [this, measure_empty]; exact bot_le
  have hn : (0:ℝ) < N := by exact_mod_cast hnpos
  set q : ℝ := ε / (2 * N) with hq
  have hqpos : 0 < q := by positivity
  set pz : ι × Bool → ℝ := fun z => D.real {x | c x = true ∧ φ x z.1 ≠ z.2} with hpz
  set Bad : Finset (ι × Bool) := Finset.univ.filter (fun z => q < pz z) with hBad
  set A : ι × Bool → Set (X × Bool) :=
    fun z => {p | p.2 = true → φ p.1 z.1 = z.2} with hAdef
  have hsub : {S | ε < errorOf D c (fun x => evalConj (eliminate (fsample φ S)) (φ x))} ⊆
      {S | ¬ IsLabeledBy c S} ∪ ⋃ z ∈ Bad, Set.univ.pi (fun _ : Fin m => A z) := by
    intro S hS
    by_cases hlab : IsLabeledBy c S
    · right
      have hlab' : IsLabeledBy (evalConj T) (fsample φ S) := fun j => hlab j
      have hT := g_sub T (fsample φ S) hlab'
      have hset : {x | evalConj (eliminate (fsample φ S)) (φ x) ≠ c x} ⊆
          ⋃ z ∈ eliminate (fsample φ S), {x | c x = true ∧ φ x z.1 ≠ z.2} := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        have hh : evalConj (eliminate (fsample φ S)) (φ x) = false := by
          by_contra hne
          have htrue : evalConj (eliminate (fsample φ S)) (φ x) = true := by simpa using hne
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
      have herr : errorOf D c (fun x => evalConj (eliminate (fsample φ S)) (φ x)) ≤
          ∑ z ∈ eliminate (fsample φ S), pz z := by
        unfold errorOf
        calc (D {x | evalConj (eliminate (fsample φ S)) (φ x) ≠ c x}).toReal
            ≤ (D (⋃ z ∈ eliminate (fsample φ S), {x | c x = true ∧ φ x z.1 ≠ z.2})).toReal :=
              ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hset)
          _ ≤ ∑ z ∈ eliminate (fsample φ S), pz z := measureReal_biUnion_finset_le _ _
      have hbad : ∃ z ∈ eliminate (fsample φ S), q < pz z := by
        by_contra hno
        push Not at hno
        have h1 : ∑ z ∈ eliminate (fsample φ S), pz z ≤ ∑ z ∈ eliminate (fsample φ S), q :=
          Finset.sum_le_sum hno
        have hcard : ((eliminate (fsample φ S)).card : ℝ) ≤ 2 * N := by
          have : (eliminate (fsample φ S)).card ≤ 2 * N := by
            calc (eliminate (fsample φ S)).card ≤ (Finset.univ : Finset (ι × Bool)).card :=
                  Finset.card_le_univ _
              _ = 2 * N := card_literals
          exact_mod_cast this
        rw [Finset.sum_const, nsmul_eq_mul] at h1
        have h2 : ((eliminate (fsample φ S)).card : ℝ) * q ≤ ε := by
          calc _ ≤ (2 * N : ℝ) * q := mul_le_mul_of_nonneg_right hcard hqpos.le
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
  have hL : Real.log (2 * N) + Real.log (1 / δ) ≤ q * m := by
    have h1 := mul_le_mul_of_nonneg_left hm hqpos.le
    have e : q * (2 * N / ε * (Real.log (2 * N) + Real.log (1 / δ))) =
        Real.log (2 * N) + Real.log (1 / δ) := by rw [hq]; field_simp
    linarith
  have hbadbound : ∀ z ∈ Bad, sampleLaw D c m (Set.univ.pi (fun _ : Fin m => A z)) ≤
      ENNReal.ofReal (δ / (2 * N)) := by
    intro z hz
    have hzq : q < pz z := (Finset.mem_filter.mp hz).2
    have hp1 : pz z ≤ 1 := by
      simp only [hpz]
      exact measureReal_le_one
    rw [sampleLaw, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hA : exampleLaw D c (A z) = ENNReal.ofReal (1 - pz z) := by
      rw [exampleLaw, Measure.map_apply (measurable_of_countable _) (g_meas _)]
      have hpre : (fun x => (x, c x)) ⁻¹' (A z) = {x | c x = true ∧ φ x z.1 ≠ z.2}ᶜ := by
        ext x
        simp only [hAdef, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_compl_iff, not_and,
          not_not]
      rw [hpre, prob_compl_eq_one_sub (g_meas' _)]
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
      _ ≤ Real.exp (-(Real.log (2 * N) + Real.log (1 / δ))) := Real.exp_le_exp.mpr (by linarith)
      _ = δ / (2 * N) := by
          rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log (by positivity),
            Real.exp_log (by positivity)]
          field_simp
  calc sampleLaw D c m {S | ε < errorOf D c (fun x => evalConj (eliminate (fsample φ S)) (φ x))}
      ≤ sampleLaw D c m ({S | ¬ IsLabeledBy c S} ∪
          ⋃ z ∈ Bad, Set.univ.pi (fun _ : Fin m => A z)) := measure_mono hsub
    _ ≤ sampleLaw D c m {S | ¬ IsLabeledBy c S} +
          sampleLaw D c m (⋃ z ∈ Bad, Set.univ.pi (fun _ : Fin m => A z)) := measure_union_le _ _
    _ = sampleLaw D c m (⋃ z ∈ Bad, Set.univ.pi (fun _ : Fin m => A z)) := by
          rw [hnull, zero_add]
    _ ≤ ∑ z ∈ Bad, sampleLaw D c m (Set.univ.pi (fun _ : Fin m => A z)) :=
          measure_biUnion_finset_le _ _
    _ ≤ ∑ z ∈ Bad, ENNReal.ofReal (δ / (2 * N)) := Finset.sum_le_sum hbadbound
    _ = ENNReal.ofReal (∑ z ∈ Bad, δ / (2 * N)) :=
          (ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)).symm
    _ ≤ ENNReal.ofReal δ := by
          apply ENNReal.ofReal_le_ofReal
          rw [Finset.sum_const, nsmul_eq_mul]
          have hcard : (Bad.card : ℝ) ≤ 2 * N := by
            have : Bad.card ≤ 2 * N := by
              calc Bad.card ≤ (Finset.univ : Finset (ι × Bool)).card := Finset.card_le_univ _
                _ = 2 * N := card_literals
            exact_mod_cast this
          calc (Bad.card : ℝ) * (δ / (2 * N)) ≤ (2 * N) * (δ / (2 * N)) :=
                mul_le_mul_of_nonneg_right hcard (by positivity)
            _ = δ := by field_simp

end Gen

section CNF

variable {n : ℕ}

/-- The clause `¬u ∨ ¬u ∨ ¬u`, i.e. the single negated literal `¬u`. -/
def negLit (u : Fin n × Bool) : Clause n := ((u.1, !u.2), (u.1, !u.2), (u.1, !u.2))

lemma evalClause_negLit (u : Fin n × Bool) (a : Cube (Fin n)) :
    evalClause (negLit u) a = true ↔ a u.1 ≠ u.2 := by
  obtain ⟨i, b⟩ := u
  simp only [evalClause, negLit, decide_eq_true_eq, or_self, ne_eq]
  cases h : a i <;> cases b <;> simp

lemma evalClause_false (k : Clause n) (a : Cube (Fin n)) :
    evalClause k a = false ↔ a k.1.1 ≠ k.1.2 ∧ a k.2.1.1 ≠ k.2.1.2 ∧ a k.2.2.1 ≠ k.2.2.2 := by
  simp only [evalClause, decide_eq_false_iff_not, not_or, ne_eq]

/-- The target 3-CNF formula as a conjunction over the expanded variables. -/
def liftCNF (F : ThreeCNF n) : Conjunction (Clause n) := F.image (fun k => (k, true))

lemma evalThreeCNF_eq (F : ThreeCNF n) (a : Cube (Fin n)) :
    evalThreeCNF F a = evalConj (liftCNF F) (expand a) := by
  rw [Bool.eq_iff_iff]
  simp only [evalThreeCNF, evalConj, decide_eq_true_eq]
  simp only [expand]
  constructor
  · intro h l hl
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hl
    exact h k hk
  · intro h k hk
    exact h (k, true) (Finset.mem_image.mpr ⟨k, hk, rfl⟩)

/-- A conjunction over the expanded variables, read back as a 3-CNF formula: a positive literal
`y_k` is the clause `k`, a negative literal `¬y_{u ∨ v ∨ w}` is the three unit clauses `¬u`, `¬v`,
`¬w`. -/
def toCNF (E : Conjunction (Clause n)) : ThreeCNF n :=
  (E.filter (fun l => l.2 = true)).image Prod.fst ∪
    (E.filter (fun l => l.2 = false)).biUnion
      (fun l => {negLit l.1.1, negLit l.1.2.1, negLit l.1.2.2})

lemma evalConj_expand_eq (E : Conjunction (Clause n)) (a : Cube (Fin n)) :
    evalConj E (expand a) = evalThreeCNF (toCNF E) a := by
  rw [Bool.eq_iff_iff]
  simp only [evalConj, evalThreeCNF, decide_eq_true_eq]
  simp only [expand]
  constructor
  · intro h k hk
    simp only [toCNF, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_biUnion,
      Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with ⟨l, ⟨hl, hl2⟩, rfl⟩ | ⟨l, ⟨hl, hl2⟩, hk⟩
    · have := h l hl
      rw [hl2] at this
      exact this
    · have := h l hl
      rw [hl2] at this
      rw [evalClause_false] at this
      rcases hk with rfl | rfl | rfl
      · exact (evalClause_negLit _ _).mpr this.1
      · exact (evalClause_negLit _ _).mpr this.2.1
      · exact (evalClause_negLit _ _).mpr this.2.2
  · intro h l hl
    have mneg : ∀ k ∈ ({negLit l.1.1, negLit l.1.2.1, negLit l.1.2.2} : Finset (Clause n)),
        l.2 = false → k ∈ toCNF E := fun k hk hl2 =>
      Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨l, Finset.mem_filter.mpr ⟨hl, hl2⟩, hk⟩))
    cases hl2 : l.2
    · rw [evalClause_false]
      refine ⟨(evalClause_negLit _ _).mp (h _ (mneg _ (by simp) hl2)),
        (evalClause_negLit _ _).mp (h _ (mneg _ (by simp) hl2)),
        (evalClause_negLit _ _).mp (h _ (mneg _ (by simp) hl2))⟩
    · exact h _ (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
        ⟨l, Finset.mem_filter.mpr ⟨hl, hl2⟩, rfl⟩)))

lemma learnThreeCNF_mem {m : ℕ} (S : Fin m → Cube (Fin n) × Bool) :
    learnThreeCNF S ∈ threeCNFClass n :=
  ⟨toCNF (eliminate (expandSample S)), funext fun a => evalConj_expand_eq _ a⟩

lemma learnThreeCNF_eq {m : ℕ} (S : Fin m → Cube (Fin n) × Bool) :
    learnThreeCNF S = fun a => evalConj (eliminate (fsample expand S)) (expand a) := rfl

lemma evalThreeCNF_fun (F : ThreeCNF n) :
    evalThreeCNF F = fun a => evalConj (liftCNF F) (expand a) :=
  funext fun a => evalThreeCNF_eq F a

theorem cnf_bound (F : ThreeCNF n) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 2 * (Fintype.card (Clause n) : ℝ) / ε *
      (Real.log (2 * Fintype.card (Clause n)) + Real.log (1 / δ)) ≤ m) :
    sampleLaw D (evalThreeCNF F) m {S | ε < errorOf D (evalThreeCNF F) (learnThreeCNF S)} ≤
      ENNReal.ofReal δ := by
  have h := g_bound expand (liftCNF F) D hε hδ hδ1 m hm
  simpa only [evalThreeCNF_fun, learnThreeCNF_eq] using h

theorem cnf_main (F : ThreeCNF n) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 2 * (Fintype.card (Clause n) : ℝ) / ε *
      (Real.log (2 * Fintype.card (Clause n)) + Real.log (1 / δ)) ≤ m) :
    (∀ S : Fin m → Cube (Fin n) × Bool, IsLabeledBy (evalThreeCNF F) S →
      IsConsistent (learnThreeCNF S) S) ∧
    (∀ S : Fin m → Cube (Fin n) × Bool, learnThreeCNF S ∈ threeCNFClass n) ∧
    sampleLaw D (evalThreeCNF F) m {S | ε < errorOf D (evalThreeCNF F) (learnThreeCNF S)} ≤
      ENNReal.ofReal δ ∧
    PACLearnable (threeCNFClass n) (threeCNFClass n) := by
  refine ⟨fun S hS => ?_, learnThreeCNF_mem, cnf_bound F D hε hδ hδ1 m hm, ?_⟩
  · have hS' : IsLabeledBy (evalConj (liftCNF F)) (expandSample S) := by
      intro j
      simp only [expandSample]
      rw [hS j, evalThreeCNF_eq]
    have := g_consistent (liftCNF F) (expandSample S) hS'
    intro i
    exact this i
  · intro ε' δ' hε' _ hδ' hδ'2
    refine ⟨⌈2 * (Fintype.card (Clause n) : ℝ) / ε' *
      (Real.log (2 * Fintype.card (Clause n)) + Real.log (1 / δ'))⌉₊,
      learnThreeCNF, learnThreeCNF_mem, ?_⟩
    intro c' hc' _ D' hD'
    obtain ⟨F', rfl⟩ := hc'
    haveI := hD'
    exact cnf_bound F' D' hε' hδ' (by linarith) _ (Nat.le_ceil _)

end CNF

end ComputationalLearning

open ComputationalLearning

theorem solution {n : ℕ} (F : ThreeCNF n) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 2 * (Fintype.card (Clause n) : ℝ) / ε *
      (Real.log (2 * Fintype.card (Clause n)) + Real.log (1 / δ)) ≤ m) :
    (∀ S : Fin m → Cube (Fin n) × Bool, IsLabeledBy (evalThreeCNF F) S →
      IsConsistent (learnThreeCNF S) S) ∧
    (∀ S : Fin m → Cube (Fin n) × Bool, learnThreeCNF S ∈ threeCNFClass n) ∧
    sampleLaw D (evalThreeCNF F) m {S | ε < errorOf D (evalThreeCNF F) (learnThreeCNF S)} ≤
      ENNReal.ofReal δ ∧
    PACLearnable (threeCNFClass n) (threeCNFClass n) := by
  exact cnf_main F D hε hδ hδ1 m hm
