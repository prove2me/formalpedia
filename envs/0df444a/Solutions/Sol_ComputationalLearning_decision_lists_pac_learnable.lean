-- Prove2me | solution 1 for ComputationalLearning.decision_lists_pac_learnable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T03:40:35.014307+00:00
-- url     : https://prove2.me/submissions/f89ddccf-b5dd-4d28-a24c-f532ceb197a6

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

end OccamCard

section DL

variable {n k : ℕ}

/-- Invariant of a greedy prefix: removed examples are classified correctly by the first item
they satisfy; remaining examples satisfy no item. -/
lemma gp_inv {m : ℕ} {S : Fin m → Cube (Fin n) × Bool} {steps : List (Condition n k × Bool)}
    {R : Finset (Fin m)} (h : IsGreedyPrefix S steps R) :
    (∀ j, j ∉ R → ∃ p, steps.find? (fun p => evalCondition p.1 (S j).1) = some p ∧
      p.2 = (S j).2) ∧
    (∀ j ∈ R, steps.find? (fun p => evalCondition p.1 (S j).1) = none) := by
  induction h with
  | nil => exact ⟨fun j hj => absurd (Finset.mem_univ j) hj, fun j _ => rfl⟩
  | @cons steps R c b hprev huse ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [List.find?_append]
      by_cases hjR : j ∈ R
      · have hjs : j ∈ satisfying S R c := by
          by_contra hns; exact hj (Finset.mem_sdiff.mpr ⟨hjR, hns⟩)
        rw [ih2 j hjR]
        have hev : evalCondition c (S j).1 = true := (Finset.mem_filter.mp hjs).2
        refine ⟨(c, b), ?_, (huse.2 j hjs).symm⟩
        simp [hev]
      · obtain ⟨p, hp, hp2⟩ := ih1 j hjR
        rw [hp]
        exact ⟨p, rfl, hp2⟩
    · obtain ⟨hjR, hjs⟩ := Finset.mem_sdiff.mp hj
      rw [List.find?_append, ih2 j hjR]
      have hev : evalCondition c (S j).1 = false := by
        by_contra hne
        exact hjs (Finset.mem_filter.mpr ⟨hjR, by simpa using hne⟩)
      simp [hev]

lemma gp_consistent {m : ℕ} {S : Fin m → Cube (Fin n) × Bool} {L : DecisionList n k}
    (h : IsGreedyOutput S L) : IsConsistent (evalDL L) S := by
  intro j
  obtain ⟨p, hp, hp2⟩ := (gp_inv h).1 j (Finset.notMem_empty j)
  unfold evalDL
  rw [hp]
  exact hp2

/-- The conditions of a greedy prefix are distinct, and no remaining example satisfies a used
condition. -/
lemma gp_nodup {m : ℕ} {S : Fin m → Cube (Fin n) × Bool} {steps : List (Condition n k × Bool)}
    {R : Finset (Fin m)} (h : IsGreedyPrefix S steps R) :
    (steps.map Prod.fst).Nodup ∧ ∀ q ∈ steps, satisfying S R q.1 = ∅ := by
  induction h with
  | nil => exact ⟨List.nodup_nil, fun q hq => absurd hq List.not_mem_nil⟩
  | @cons steps R c b hprev huse ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hsub : ∀ c' : Condition n k,
        satisfying S (R \ satisfying S R c) c' ⊆ satisfying S R c' := by
      intro c' j hj
      simp only [satisfying, Finset.mem_filter, Finset.mem_sdiff] at hj ⊢
      exact ⟨hj.1.1, hj.2⟩
    refine ⟨?_, fun q hq => ?_⟩
    · rw [List.map_append, List.nodup_append]
      refine ⟨ih1, List.nodup_singleton _, ?_⟩
      intro a ha b' hb' hab
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb'
      subst hb'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      have h0 := ih2 q hq
      rw [hab] at h0
      obtain ⟨j, hj⟩ := huse.1
      rw [h0] at hj
      exact Finset.notMem_empty j hj
    · rcases List.mem_append.mp hq with hq | hq
      · exact Finset.subset_empty.mp ((hsub q.1).trans (ih2 q hq).le)
      · simp only [List.mem_singleton] at hq
        subst hq
        ext j
        constructor
        · intro hj
          simp only [satisfying, Finset.mem_filter, Finset.mem_sdiff] at hj
          exact absurd ⟨hj.1.1, hj.2⟩ hj.1.2
        · intro hj
          exact absurd hj (Finset.notMem_empty j)

/-- On a sample labeled by a decision list, a useful condition exists while examples remain. -/
lemma dl_useful (hn : 0 < n) (L₀ : DecisionList n k) {m : ℕ} (S : Fin m → Cube (Fin n) × Bool)
    (hS : IsLabeledBy (evalDL L₀) S) (R : Finset (Fin m)) (hR : R.Nonempty) :
    ∃ (c : Condition n k) (b : Bool), IsUseful S R c b := by
  classical
  set P : Condition n k × Bool → Bool :=
    fun p => decide (∃ j ∈ R, evalCondition p.1 (S j).1 = true) with hP
  cases hf : L₀.1.find? P with
  | none =>
    obtain ⟨j0, hj0⟩ := hR
    refine ⟨fun _ => (⟨0, hn⟩, (S j0).1 ⟨0, hn⟩), L₀.2, ⟨j0, ?_⟩, ?_⟩
    · simp [satisfying, hj0, evalCondition]
    · intro j hj
      have hjR : j ∈ R := (Finset.mem_filter.mp hj).1
      rw [hS j]
      unfold evalDL
      have hnone : L₀.1.find? (fun p => evalCondition p.1 (S j).1) = none := by
        rw [List.find?_eq_none] at hf ⊢
        intro p hp hev
        have hfp := hf p hp
        simp only [hP, decide_eq_true_eq, not_exists, not_and] at hfp
        exact hfp j hjR (by simpa using hev)
      rw [hnone]
  | some p =>
    obtain ⟨hPp, l₁, l₂, hsplit, hbefore⟩ := List.find?_eq_some_iff_append.mp hf
    simp only [hP, decide_eq_true_eq] at hPp
    obtain ⟨j1, hj1R, hj1⟩ := hPp
    refine ⟨p.1, p.2, ⟨j1, Finset.mem_filter.mpr ⟨hj1R, hj1⟩⟩, ?_⟩
    intro j hj
    obtain ⟨hjR, hjc⟩ := Finset.mem_filter.mp hj
    rw [hS j]
    unfold evalDL
    have hl₁ : l₁.find? (fun q => evalCondition q.1 (S j).1) = none := by
      rw [List.find?_eq_none]
      intro a ha hev
      have hb := hbefore a ha
      simp only [hP, Bool.not_eq_true', decide_eq_false_iff_not, not_exists, not_and] at hb
      exact hb j hjR (by simpa using hev)
    have hfind : L₀.1.find? (fun q => evalCondition q.1 (S j).1) = some p := by
      rw [hsplit, List.find?_append, hl₁, Option.none_or, List.find?_cons_of_pos]
      simpa using hjc
    rw [hfind]

lemma dl_terminates (hn : 0 < n) (L₀ : DecisionList n k) {m : ℕ}
    (S : Fin m → Cube (Fin n) × Bool) (hS : IsLabeledBy (evalDL L₀) S) :
    ∀ (N : ℕ) (steps : List (Condition n k × Bool)) (R : Finset (Fin m)),
      R.card ≤ N → IsGreedyPrefix S steps R →
        ∃ steps' : List (Condition n k × Bool), IsGreedyPrefix S steps' ∅ := by
  intro N
  induction N with
  | zero =>
    intro steps R hR h
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hR)] at h
    exact ⟨steps, h⟩
  | succ N ih =>
    intro steps R hR h
    rcases R.eq_empty_or_nonempty with h0 | hne
    · rw [h0] at h; exact ⟨steps, h⟩
    · obtain ⟨c, b, hu⟩ := dl_useful hn L₀ S hS R hne
      have hlt : (R \ satisfying S R c).card < R.card := by
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
        intro heq
        obtain ⟨j, hj⟩ := hu.1
        have hjR : j ∈ R := (Finset.mem_filter.mp hj).1
        have hj' : j ∈ R \ satisfying S R c := by rw [heq]; exact hjR
        exact (Finset.mem_sdiff.mp hj').2 hj
      exact ih (steps ++ [(c, b)]) (R \ satisfying S R c) (by omega) (IsGreedyPrefix.cons h hu)

lemma dl_lists (M : ℕ) (α : Type*) [Fintype α] (hα : Fintype.card α = 2 * M) :
    ∃ Ls : Finset (List α), Ls.card ≤ (2 * M + 1) ^ M ∧
      ∀ l : List α, l.length ≤ M → l ∈ Ls := by
  classical
  refine ⟨(Finset.range (M + 1)).biUnion
    (fun ℓ => (Finset.univ : Finset (Fin ℓ → α)).image List.ofFn), ?_, ?_⟩
  · calc _ ≤ ∑ ℓ ∈ Finset.range (M + 1),
          ((Finset.univ : Finset (Fin ℓ → α)).image List.ofFn).card := Finset.card_biUnion_le
      _ ≤ ∑ ℓ ∈ Finset.range (M + 1), (2 * M) ^ ℓ := Finset.sum_le_sum fun ℓ _ => by
          calc _ ≤ (Finset.univ : Finset (Fin ℓ → α)).card := Finset.card_image_le
            _ = (2 * M) ^ ℓ := by simp [hα]
      _ ≤ (2 * M + 1) ^ M := by
          rw [add_pow]
          apply Finset.sum_le_sum
          intro ℓ hℓ
          simp only [one_pow, mul_one]
          have : 1 ≤ M.choose ℓ := Nat.choose_pos (by simp at hℓ; omega)
          exact Nat.le_mul_of_pos_right _ this
  · intro l hl
    rw [Finset.mem_biUnion]
    exact ⟨l.length, Finset.mem_range.mpr (Nat.lt_succ_of_le hl),
      Finset.mem_image.mpr ⟨l.get, Finset.mem_univ _, List.ofFn_get l⟩⟩

theorem dl_bound (hn : 0 < n) (L₀ : DecisionList n k) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (m : ℕ)
    (hm : 1 / ε * (Real.log (2 * (2 * (Fintype.card (Condition n k) : ℝ) + 1) ^
      Fintype.card (Condition n k)) + Real.log (1 / δ)) ≤ m) :
    sampleLaw D (evalDL L₀) m
      {S | ∃ L : DecisionList n k, IsGreedyOutput S L ∧ ε < errorOf D (evalDL L₀) (evalDL L)} ≤
      ENNReal.ofReal δ := by
  classical
  set M := Fintype.card (Condition n k) with hM
  obtain ⟨Ls, hLs, hmem⟩ := dl_lists M (Condition n k × Bool)
    (by simp only [Fintype.card_prod, Fintype.card_bool, hM]; ring)
  set H : Finset (Cube (Fin n) → Bool) :=
    (Ls ×ˢ (Finset.univ : Finset Bool)).image (fun lb => evalDL (lb.1, lb.2)) with hH
  have hHcard : H.card ≤ 2 * (2 * M + 1) ^ M := by
    calc H.card ≤ (Ls ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_image_le
      _ = Ls.card * 2 := by simp [Finset.card_product]
      _ ≤ (2 * M + 1) ^ M * 2 := Nat.mul_le_mul_right 2 hLs
      _ = 2 * (2 * M + 1) ^ M := by ring
  have hsub : {S : Fin m → Cube (Fin n) × Bool | ∃ L : DecisionList n k, IsGreedyOutput S L ∧
      ε < errorOf D (evalDL L₀) (evalDL L)} ⊆
      {S | ∃ h ∈ H, IsConsistent h S ∧ ε < errorOf D (evalDL L₀) h} := by
    rintro S ⟨L, hL, herr⟩
    have hlen : L.1.length ≤ M := by
      have := (gp_nodup hL).1
      calc L.1.length = (L.1.map Prod.fst).length := by simp
        _ ≤ M := this.length_le_card
    exact ⟨evalDL L, Finset.mem_image.mpr ⟨(L.1, L.2),
      Finset.mem_product.mpr ⟨hmem _ hlen, Finset.mem_univ _⟩, rfl⟩, gp_consistent hL, herr⟩
  refine (measure_mono hsub).trans ((oc_bad _ (measurable_of_countable _) D H
    (fun h _ => measurable_of_countable _) hε hε1 m).trans (ENNReal.ofReal_le_ofReal ?_))
  have hK : (0:ℝ) < 2 * (2 * (M:ℝ) + 1) ^ M := by positivity
  calc (H.card : ℝ) * (1 - ε) ^ m ≤ (2 * (2 * (M:ℝ) + 1) ^ M) * (1 - ε) ^ m := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) m)
        exact_mod_cast hHcard
    _ ≤ δ := oc_real hK hε hε1 hδ m hm

theorem dl_pac (hn : 0 < n) : PACLearnable (decisionListClass n k) (decisionListClass n k) := by
  classical
  intro ε δ hε hε2 hδ hδ2
  set M := Fintype.card (Condition n k) with hM
  set m := ⌈1 / ε * (Real.log (2 * (2 * (M : ℝ) + 1) ^ M) + Real.log (1 / δ))⌉₊ with hmdef
  set L' : (Fin m → Cube (Fin n) × Bool) → Cube (Fin n) → Bool := fun S =>
    if h : ∃ L : DecisionList n k, IsGreedyOutput S L then evalDL (Classical.choose h)
    else evalDL ([], false) with hL'
  refine ⟨m, L', ?_, ?_⟩
  · intro S
    simp only [hL']
    split_ifs with h
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · intro c hc _ D hD
    obtain ⟨L₀, rfl⟩ := hc
    haveI := hD
    have hsub : {S : Fin m → Cube (Fin n) × Bool | ε < errorOf D (evalDL L₀) (L' S)} ⊆
        {S | ¬ IsLabeledBy (evalDL L₀) S} ∪
        {S | ∃ L : DecisionList n k, IsGreedyOutput S L ∧
          ε < errorOf D (evalDL L₀) (evalDL L)} := by
      intro S hS
      by_cases hlab : IsLabeledBy (evalDL L₀) S
      · right
        obtain ⟨steps', hsteps'⟩ :=
          dl_terminates hn L₀ S hlab _ [] Finset.univ le_rfl IsGreedyPrefix.nil
        have hex : ∃ L : DecisionList n k, IsGreedyOutput S L := ⟨(steps', false), hsteps'⟩
        have hS' : ε < errorOf D (evalDL L₀) (L' S) := hS
        simp only [hL', dif_pos hex] at hS'
        exact ⟨Classical.choose hex, Classical.choose_spec hex, hS'⟩
      · left; exact hlab
    calc sampleLaw D (evalDL L₀) m {S | ε < errorOf D (evalDL L₀) (L' S)}
        ≤ sampleLaw D (evalDL L₀) m ({S | ¬ IsLabeledBy (evalDL L₀) S} ∪
            {S | ∃ L : DecisionList n k, IsGreedyOutput S L ∧
              ε < errorOf D (evalDL L₀) (evalDL L)}) := measure_mono hsub
      _ ≤ sampleLaw D (evalDL L₀) m {S | ¬ IsLabeledBy (evalDL L₀) S} +
            sampleLaw D (evalDL L₀) m {S | ∃ L : DecisionList n k, IsGreedyOutput S L ∧
              ε < errorOf D (evalDL L₀) (evalDL L)} := measure_union_le _ _
      _ ≤ 0 + ENNReal.ofReal δ := by
          rw [oc_null _ (measurable_of_countable _) D m]
          gcongr
          exact dl_bound hn L₀ D hε (by linarith) hδ m (Nat.le_ceil _)
      _ = ENNReal.ofReal δ := zero_add _

theorem dl_main (hn : 0 < n) (L₀ : DecisionList n k)
    (D : Measure (Cube (Fin n))) [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 1 / ε * (Real.log (2 * (2 * (Fintype.card (Condition n k) : ℝ) + 1) ^
      Fintype.card (Condition n k)) + Real.log (1 / δ)) ≤ m) :
    (∀ S : Fin m → Cube (Fin n) × Bool, IsLabeledBy (evalDL L₀) S →
      ∀ (steps : List (Condition n k × Bool)) (R : Finset (Fin m)),
        IsGreedyPrefix S steps R → R.Nonempty →
          ∃ (c : Condition n k) (b : Bool), IsUseful S R c b) ∧
    (∀ (S : Fin m → Cube (Fin n) × Bool) (L : DecisionList n k),
      IsGreedyOutput S L → IsConsistent (evalDL L) S) ∧
    sampleLaw D (evalDL L₀) m
      {S | ∃ L : DecisionList n k, IsGreedyOutput S L ∧ ε < errorOf D (evalDL L₀) (evalDL L)} ≤
      ENNReal.ofReal δ ∧
    PACLearnable (decisionListClass n k) (decisionListClass n k) :=
  ⟨fun S hS _ R _ hR => dl_useful hn L₀ S hS R hR, fun _ _ h => gp_consistent h,
    dl_bound hn L₀ D hε hε1 hδ m hm, dl_pac hn⟩

end DL

end ComputationalLearning

open ComputationalLearning

theorem solution {n k : ℕ} (hn : 0 < n) (L₀ : DecisionList n k)
    (D : Measure (Cube (Fin n))) [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 1 / ε * (Real.log (2 * (2 * (Fintype.card (Condition n k) : ℝ) + 1) ^
      Fintype.card (Condition n k)) + Real.log (1 / δ)) ≤ m) :
    (∀ S : Fin m → Cube (Fin n) × Bool, IsLabeledBy (evalDL L₀) S →
      ∀ (steps : List (Condition n k × Bool)) (R : Finset (Fin m)),
        IsGreedyPrefix S steps R → R.Nonempty → ∃ (c : Condition n k) (b : Bool), IsUseful S R c b) ∧
    (∀ (S : Fin m → Cube (Fin n) × Bool) (L : DecisionList n k),
      IsGreedyOutput S L → IsConsistent (evalDL L) S) ∧
    sampleLaw D (evalDL L₀) m
      {S | ∃ L : DecisionList n k, IsGreedyOutput S L ∧ ε < errorOf D (evalDL L₀) (evalDL L)} ≤
      ENNReal.ofReal δ ∧
    PACLearnable (decisionListClass n k) (decisionListClass n k) := by
  exact dl_main hn L₀ D hε hε1 hδ hδ1 m hm
