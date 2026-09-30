-- Prove2me | solution 1 for ComputationalLearning.rectangles_pac_learnable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T03:10:36.072848+00:00
-- url     : https://prove2.me/submissions/926e702f-f5df-4da9-9cf1-1f94807d7b7c

import Mathlib
import Definitions.Def_ComputationalLearning_PAC

open MeasureTheory

namespace ComputationalLearning

/-- The target rectangle `[a₁, b₁] × [a₂, b₂]` as a set. -/
def rectSet (a b : ℝ × ℝ) : Set (ℝ × ℝ) := {p | a.1 ≤ p.1 ∧ p.1 ≤ b.1 ∧ a.2 ≤ p.2 ∧ p.2 ≤ b.2}

lemma rect_iff (a b : ℝ × ℝ) (p : ℝ × ℝ) : rectConcept a b p = true ↔ p ∈ rectSet a b := by
  simp [rectConcept, rectSet]

lemma rectSet_meas (a b : ℝ × ℝ) : MeasurableSet (rectSet a b) := by
  simp only [rectSet, Set.ofPred_and]
  exact (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)))

lemma rect_meas (a b : ℝ × ℝ) : Measurable (rectConcept a b) := by
  apply measurable_to_bool
  have : rectConcept a b ⁻¹' {true} = rectSet a b := by
    ext p; simp only [Set.mem_preimage, Set.mem_singleton_iff, rect_iff]
  rw [this]; exact rectSet_meas a b

/-- On a sample labeled by the target, the tightest fit lies inside the target. -/
lemma tf_sub {m : ℕ} (a b : ℝ × ℝ) (S : Fin m → (ℝ × ℝ) × Bool)
    (hS : IsLabeledBy (rectConcept a b) S) (x : ℝ × ℝ) (hx : tightestFit S x = true) :
    x ∈ rectSet a b := by
  unfold tightestFit at hx
  split_ifs at hx with hJ
  · rw [rect_iff] at hx
    simp only [rectSet, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hx
    have hpos : ∀ j ∈ Finset.univ.filter (fun j : Fin m => (S j).2 = true),
        (S j).1 ∈ rectSet a b := by
      intro j hj
      rw [Finset.mem_filter] at hj
      have := hj.2
      rw [hS j] at this
      exact (rect_iff a b _).mp this
    exact ⟨le_trans (Finset.le_inf' hJ _ fun j hj => (hpos j hj).1) h1,
      le_trans h2 (Finset.sup'_le hJ _ fun j hj => (hpos j hj).2.1),
      le_trans (Finset.le_inf' hJ _ fun j hj => (hpos j hj).2.2.1) h3,
      le_trans h4 (Finset.sup'_le hJ _ fun j hj => (hpos j hj).2.2.2)⟩

lemma tf_consistent {m : ℕ} (a b : ℝ × ℝ) (S : Fin m → (ℝ × ℝ) × Bool)
    (hS : IsLabeledBy (rectConcept a b) S) : IsConsistent (tightestFit S) S := by
  intro i
  cases hi : (S i).2
  · by_contra hne
    have htrue : tightestFit S (S i).1 = true := by simpa using hne
    have hmem := tf_sub a b S hS _ htrue
    have h2 : rectConcept a b (S i).1 = true := (rect_iff _ _ _).mpr hmem
    rw [← hS i, hi] at h2
    exact Bool.false_ne_true h2
  · have hiJ : i ∈ Finset.univ.filter (fun j : Fin m => (S j).2 = true) := by simp [hi]
    have hJ : (Finset.univ.filter (fun j : Fin m => (S j).2 = true)).Nonempty := ⟨i, hiJ⟩
    unfold tightestFit
    rw [dif_pos hJ, rect_iff]
    simp only [rectSet, Set.mem_setOf_eq]
    exact ⟨Finset.inf'_le _ hiJ, Finset.le_sup' (fun j => (S j).1.1) hiJ,
      Finset.inf'_le _ hiJ, Finset.le_sup' (fun j => (S j).1.2) hiJ⟩

lemma tf_mem {m : ℕ} (S : Fin m → (ℝ × ℝ) × Bool) : tightestFit S ∈ rectangleClass := by
  unfold tightestFit
  split_ifs with hJ
  · exact ⟨_, _, rfl⟩
  · refine ⟨(1, 0), (0, 0), ?_⟩
    funext p
    unfold rectConcept
    symm
    rw [decide_eq_false_iff_not]
    rintro ⟨h1, h2, -, -⟩
    dsimp only at h1 h2
    linarith

/-- A quantile along the linear functional `f` of the measure restricted to `R`: a threshold `t`
such that the closed strip `R ∩ {f ≤ t}` has mass at least `e` and the open strip `R ∩ {f < t}`
has mass at most `e`. -/
lemma side_quantile (D : Measure (ℝ × ℝ)) [IsFiniteMeasure D] (R : Set (ℝ × ℝ))
    (hR : MeasurableSet R) (f : ℝ × ℝ → ℝ) (hf : Measurable f) (L U : ℝ)
    (hL : ∀ p ∈ R, L ≤ f p) (hU : ∀ p ∈ R, f p ≤ U) (e : ENNReal) (he : e ≤ D R) :
    ∃ t : ℝ, e ≤ D (R ∩ {p | f p ≤ t}) ∧ D (R ∩ {p | f p < t}) ≤ e := by
  by_cases he0 : e = 0
  · refine ⟨L, by simp [he0], ?_⟩
    have : R ∩ {p | f p < L} = ∅ := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_and, not_lt]
      exact hL p
    rw [this, measure_empty]; exact zero_le
  set G : ℝ → ENNReal := fun t => D (R ∩ {p | f p ≤ t}) with hG
  have hGmono : Monotone G := fun s t hst =>
    measure_mono (Set.inter_subset_inter_right _
      (fun p (hp : f p ≤ s) => (le_trans hp hst : f p ≤ t)))
  set T := {t : ℝ | e ≤ G t} with hT
  have hUmem : U ∈ T := by
    show e ≤ D (R ∩ {p | f p ≤ U})
    rwa [Set.inter_eq_left.mpr (show R ⊆ {p | f p ≤ U} from fun p hp => hU p hp)]
  have hbdd : BddBelow T := by
    refine ⟨L, fun t ht => ?_⟩
    by_contra hlt
    push Not at hlt
    have hempty : R ∩ {p | f p ≤ t} = ∅ := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_and, not_le]
      intro hp
      linarith [hL p hp]
    have ht' : e ≤ D (R ∩ {p | f p ≤ t}) := ht
    rw [hempty, measure_empty] at ht'
    exact he0 (le_antisymm ht' (zero_le))
  set t0 := sInf T with ht0
  have hmeas : ∀ t, MeasurableSet (R ∩ {p | f p ≤ t}) := fun t =>
    hR.inter (measurableSet_le hf measurable_const)
  have hinv : ∀ i j : ℕ, i ≤ j → 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity)
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  refine ⟨t0, ?_, ?_⟩
  · have hInter : R ∩ {p | f p ≤ t0} = ⋂ n : ℕ, R ∩ {p | f p ≤ t0 + 1 / ((n : ℝ) + 1)} := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hp, hle⟩ n
        have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
        exact ⟨hp, by linarith⟩
      · intro h
        refine ⟨(h 0).1, ?_⟩
        by_contra hgt
        push Not at hgt
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hgt)
        have := (h n).2
        linarith
    have hanti : Antitone (fun n : ℕ => R ∩ {p | f p ≤ t0 + 1 / ((n : ℝ) + 1)}) := by
      intro i j hij
      apply Set.inter_subset_inter_right
      intro p hp
      simp only [Set.mem_setOf_eq] at hp ⊢
      linarith [hinv i j hij]
    rw [hInter, hanti.measure_iInter (fun n => (hmeas _).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩]
    refine le_iInf fun n => ?_
    have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    obtain ⟨s, hs, hslt⟩ := exists_lt_of_csInf_lt ⟨U, hUmem⟩ (lt_add_of_pos_right t0 hpos)
    exact le_trans hs (hGmono hslt.le)
  · have hUnion : R ∩ {p | f p < t0} = ⋃ n : ℕ, R ∩ {p | f p ≤ t0 - 1 / ((n : ℝ) + 1)} := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hp, hlt⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
        exact ⟨n, hp, by linarith⟩
      · rintro ⟨n, hp, hle⟩
        have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
        exact ⟨hp, by linarith⟩
    have hmono : Monotone (fun n : ℕ => R ∩ {p | f p ≤ t0 - 1 / ((n : ℝ) + 1)}) := by
      intro i j hij
      apply Set.inter_subset_inter_right
      intro p hp
      simp only [Set.mem_setOf_eq] at hp ⊢
      linarith [hinv i j hij]
    rw [hUnion, hmono.measure_iUnion]
    refine iSup_le fun n => ?_
    have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
    have hnot : t0 - 1 / ((n:ℝ) + 1) ∉ T := by
      intro hmem
      have := csInf_le hbdd hmem
      linarith
    have hlt : G (t0 - 1 / ((n:ℝ) + 1)) < e := not_le.mp hnot
    exact hlt.le

/-- The probability that no example falls in a set `W` of mass at least `ε/4`. -/
lemma side_prob (a b : ℝ × ℝ) (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D]
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (m : ℕ)
    (hm : 4 / ε * Real.log (4 / δ) ≤ m)
    (W : Set (ℝ × ℝ)) (hW : MeasurableSet W) (hWe : ENNReal.ofReal (ε / 4) ≤ D W) :
    sampleLaw D (rectConcept a b) m
        (Set.univ.pi (fun _ : Fin m => {q : (ℝ × ℝ) × Bool | q.1 ∉ W})) ≤
      ENNReal.ofReal (δ / 4) := by
  have hcm := rect_meas a b
  have hφ : Measurable (fun x : ℝ × ℝ => (x, rectConcept a b x)) := measurable_id.prodMk hcm
  haveI : IsProbabilityMeasure (exampleLaw D (rectConcept a b)) :=
    Measure.isProbabilityMeasure_map hφ.aemeasurable
  rw [sampleLaw, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hA : exampleLaw D (rectConcept a b) {q : (ℝ × ℝ) × Bool | q.1 ∉ W} = 1 - D W := by
    rw [exampleLaw, Measure.map_apply hφ
      (show MeasurableSet {q : (ℝ × ℝ) × Bool | q.1 ∉ W} from (measurable_fst hW).compl)]
    have : (fun x : ℝ × ℝ => (x, rectConcept a b x)) ⁻¹' {q : (ℝ × ℝ) × Bool | q.1 ∉ W} =
        Wᶜ := by
      ext x; simp
    rw [this, prob_compl_eq_one_sub hW]
  rw [hA]
  have hq : (0:ℝ) ≤ ε / 4 := by positivity
  have h1 : 1 - D W ≤ ENNReal.ofReal (1 - ε / 4) := by
    rw [ENNReal.ofReal_sub 1 hq, ENNReal.ofReal_one]
    exact tsub_le_tsub_left hWe 1
  calc (1 - D W) ^ m ≤ ENNReal.ofReal (1 - ε / 4) ^ m := pow_le_pow_left₀ (zero_le) h1 m
    _ = ENNReal.ofReal ((1 - ε / 4) ^ m) := (ENNReal.ofReal_pow (by linarith) m).symm
    _ ≤ ENNReal.ofReal (δ / 4) := by
      apply ENNReal.ofReal_le_ofReal
      have hL : Real.log (4 / δ) ≤ ε / 4 * m := by
        have h := mul_le_mul_of_nonneg_left hm hq
        have e : ε / 4 * (4 / ε * Real.log (4 / δ)) = Real.log (4 / δ) := by field_simp
        linarith
      calc (1 - ε / 4) ^ m ≤ (Real.exp (-(ε / 4))) ^ m :=
            pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-(ε / 4))]) m
        _ = Real.exp (-(ε / 4 * m)) := by rw [← Real.exp_nat_mul]; ring_nf
        _ ≤ Real.exp (-Real.log (4 / δ)) := Real.exp_le_exp.mpr (by linarith)
        _ = δ / 4 := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]

theorem rect_bound (a b : ℝ × ℝ) (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (m : ℕ)
    (hm : 4 / ε * Real.log (4 / δ) ≤ m) :
    sampleLaw D (rectConcept a b) m {S | ε < errorOf D (rectConcept a b) (tightestFit S)} ≤
      ENNReal.ofReal δ := by
  classical
  set c := rectConcept a b with hc
  set R := rectSet a b with hRdef
  have hcm : Measurable c := rect_meas a b
  have hRm : MeasurableSet R := rectSet_meas a b
  have hφ : Measurable (fun x : ℝ × ℝ => (x, c x)) := measurable_id.prodMk hcm
  haveI : IsProbabilityMeasure (exampleLaw D c) :=
    Measure.isProbabilityMeasure_map hφ.aemeasurable
  have hnull : sampleLaw D c m {S | ¬ IsLabeledBy c S} = 0 := by
    have e : {S : Fin m → (ℝ × ℝ) × Bool | ¬ IsLabeledBy c S} =
        ⋃ j, (fun S : Fin m → (ℝ × ℝ) × Bool => S j) ⁻¹' {p | p.2 ≠ c p.1} := by
      ext S; simp [IsLabeledBy]
    rw [e]
    refine measure_iUnion_null fun j => ?_
    apply Measure.pi_eval_preimage_null
    have hms : MeasurableSet {p : (ℝ × ℝ) × Bool | p.2 ≠ c p.1} :=
      (measurableSet_eq_fun measurable_snd (hcm.comp measurable_fst)).compl
    rw [exampleLaw, Measure.map_apply hφ hms]
    simp
  have herrR : ∀ S : Fin m → (ℝ × ℝ) × Bool, IsLabeledBy c S →
      {x | tightestFit S x ≠ c x} ⊆ R := by
    intro S hS x hx
    by_contra hxR
    have hcx : c x = false := by
      cases h : c x
      · rfl
      · exact absurd ((rect_iff a b x).mp h) hxR
    have htf : tightestFit S x = true := by
      cases h : tightestFit S x
      · exact absurd (h.trans hcx.symm) hx
      · rfl
    exact hxR (tf_sub a b S hS x htf)
  by_cases hsmall : D.real R ≤ ε
  · have hsub : {S : Fin m → (ℝ × ℝ) × Bool | ε < errorOf D c (tightestFit S)} ⊆
        {S | ¬ IsLabeledBy c S} := by
      intro S hS hlab
      have h1 : errorOf D c (tightestFit S) ≤ D.real R := by
        unfold errorOf
        exact measureReal_mono (herrR S hlab)
      simp only [Set.mem_setOf_eq] at hS
      linarith
    calc sampleLaw D c m {S | ε < errorOf D c (tightestFit S)}
        ≤ sampleLaw D c m {S | ¬ IsLabeledBy c S} := measure_mono hsub
      _ = 0 := hnull
      _ ≤ _ := zero_le
  push Not at hsmall
  have hε1 : ε < 1 := lt_of_lt_of_le hsmall measureReal_le_one
  have hq : (0:ℝ) ≤ ε / 4 := by positivity
  set e := ENNReal.ofReal (ε / 4) with he
  have heR : e ≤ D R := by
    apply ENNReal.ofReal_le_of_le_toReal
    have : ε / 4 ≤ D.real R := by linarith
    exact this
  obtain ⟨t1, hW1, hG1⟩ := side_quantile D R hRm (fun p => p.1) measurable_fst a.1 b.1
    (fun p hp => hp.1) (fun p hp => hp.2.1) e heR
  obtain ⟨t2, hW2, hG2⟩ := side_quantile D R hRm (fun p => -p.1) measurable_fst.neg (-b.1) (-a.1)
    (fun p hp => neg_le_neg hp.2.1) (fun p hp => neg_le_neg hp.1) e heR
  obtain ⟨t3, hW3, hG3⟩ := side_quantile D R hRm (fun p => p.2) measurable_snd a.2 b.2
    (fun p hp => hp.2.2.1) (fun p hp => hp.2.2.2) e heR
  obtain ⟨t4, hW4, hG4⟩ := side_quantile D R hRm (fun p => -p.2) measurable_snd.neg (-b.2) (-a.2)
    (fun p hp => neg_le_neg hp.2.2.2) (fun p hp => neg_le_neg hp.2.2.1) e heR
  set W1 := R ∩ {p : ℝ × ℝ | p.1 ≤ t1} with hW1def
  set W2 := R ∩ {p : ℝ × ℝ | -p.1 ≤ t2} with hW2def
  set W3 := R ∩ {p : ℝ × ℝ | p.2 ≤ t3} with hW3def
  set W4 := R ∩ {p : ℝ × ℝ | -p.2 ≤ t4} with hW4def
  set G1 := R ∩ {p : ℝ × ℝ | p.1 < t1} with hG1def
  set G2 := R ∩ {p : ℝ × ℝ | -p.1 < t2} with hG2def
  set G3 := R ∩ {p : ℝ × ℝ | p.2 < t3} with hG3def
  set G4 := R ∩ {p : ℝ × ℝ | -p.2 < t4} with hG4def
  have hW1m : MeasurableSet W1 := hRm.inter (measurableSet_le measurable_fst measurable_const)
  have hW2m : MeasurableSet W2 :=
    hRm.inter (measurableSet_le measurable_fst.neg measurable_const)
  have hW3m : MeasurableSet W3 := hRm.inter (measurableSet_le measurable_snd measurable_const)
  have hW4m : MeasurableSet W4 :=
    hRm.inter (measurableSet_le measurable_snd.neg measurable_const)
  have hGr : ∀ G : Set (ℝ × ℝ), D G ≤ e → D.real G ≤ ε / 4 := fun G hG =>
    ENNReal.toReal_le_of_le_ofReal hq hG
  have hGr1 := hGr G1 hG1
  have hGr2 := hGr G2 hG2
  have hGr3 := hGr G3 hG3
  have hGr4 := hGr G4 hG4
  set A1 := Set.univ.pi (fun _ : Fin m => {q : (ℝ × ℝ) × Bool | q.1 ∉ W1}) with hA1
  set A2 := Set.univ.pi (fun _ : Fin m => {q : (ℝ × ℝ) × Bool | q.1 ∉ W2}) with hA2
  set A3 := Set.univ.pi (fun _ : Fin m => {q : (ℝ × ℝ) × Bool | q.1 ∉ W3}) with hA3
  set A4 := Set.univ.pi (fun _ : Fin m => {q : (ℝ × ℝ) × Bool | q.1 ∉ W4}) with hA4
  have hwit : ∀ (S : Fin m → (ℝ × ℝ) × Bool) (W : Set (ℝ × ℝ)),
      S ∉ Set.univ.pi (fun _ : Fin m => {q : (ℝ × ℝ) × Bool | q.1 ∉ W}) → ∃ j, (S j).1 ∈ W := by
    intro S W hS
    by_contra hno
    push Not at hno
    exact hS (fun j _ => hno j)
  have hcover : {S : Fin m → (ℝ × ℝ) × Bool | ε < errorOf D c (tightestFit S)} ⊆
      {S | ¬ IsLabeledBy c S} ∪ A1 ∪ A2 ∪ A3 ∪ A4 := by
    intro S hS
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨⟨⟨⟨hlab, h1⟩, h2⟩, h3⟩, h4⟩ := hnot
    have hlab' : IsLabeledBy c S := by simpa using hlab
    obtain ⟨j1, hj1⟩ := hwit S W1 h1
    obtain ⟨j2, hj2⟩ := hwit S W2 h2
    obtain ⟨j3, hj3⟩ := hwit S W3 h3
    obtain ⟨j4, hj4⟩ := hwit S W4 h4
    have hJ : ∀ j, (S j).1 ∈ R → j ∈ Finset.univ.filter (fun j : Fin m => (S j).2 = true) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hlab' j]
      exact (rect_iff a b _).mpr hj
    have hJne : (Finset.univ.filter (fun j : Fin m => (S j).2 = true)).Nonempty :=
      ⟨j1, hJ j1 hj1.1⟩
    have herr : {x | tightestFit S x ≠ c x} ⊆ G1 ∪ G2 ∪ G3 ∪ G4 := by
      intro x hx
      have hxR := herrR S hlab' hx
      have hcx : c x = true := (rect_iff a b x).mpr hxR
      have htf : tightestFit S x = false := by
        cases h : tightestFit S x
        · rfl
        · exact absurd (h.trans hcx.symm) hx
      unfold tightestFit at htf
      rw [dif_pos hJne] at htf
      simp only [rectConcept, decide_eq_false_iff_not, not_and_or, not_le] at htf
      have i1 := Finset.inf'_le (fun j => (S j).1.1) (hJ j1 hj1.1)
      have i2 := Finset.le_sup' (fun j => (S j).1.1) (hJ j2 hj2.1)
      have i3 := Finset.inf'_le (fun j => (S j).1.2) (hJ j3 hj3.1)
      have i4 := Finset.le_sup' (fun j => (S j).1.2) (hJ j4 hj4.1)
      have k1 : (S j1).1.1 ≤ t1 := hj1.2
      have k2 : -(S j2).1.1 ≤ t2 := hj2.2
      have k3 : (S j3).1.2 ≤ t3 := hj3.2
      have k4 : -(S j4).1.2 ≤ t4 := hj4.2
      rcases htf with h | h | h | h
      · left; left; left
        exact ⟨hxR, show x.1 < t1 by linarith⟩
      · left; left; right
        exact ⟨hxR, show -x.1 < t2 by linarith⟩
      · left; right
        exact ⟨hxR, show x.2 < t3 by linarith⟩
      · right
        exact ⟨hxR, show -x.2 < t4 by linarith⟩
    have hsum : errorOf D c (tightestFit S) ≤ ε := by
      unfold errorOf
      have hle : D.real {x | tightestFit S x ≠ c x} ≤
          D.real G1 + D.real G2 + D.real G3 + D.real G4 := by
        calc D.real {x | tightestFit S x ≠ c x} ≤ D.real (G1 ∪ G2 ∪ G3 ∪ G4) :=
              measureReal_mono herr
          _ ≤ D.real (G1 ∪ G2 ∪ G3) + D.real G4 := measureReal_union_le _ _
          _ ≤ D.real (G1 ∪ G2) + D.real G3 + D.real G4 := by
              gcongr; exact measureReal_union_le _ _
          _ ≤ D.real G1 + D.real G2 + D.real G3 + D.real G4 := by
              gcongr; exact measureReal_union_le _ _
      have : D.real {x | tightestFit S x ≠ c x} = (D {x | tightestFit S x ≠ c x}).toReal := rfl
      linarith
    simp only [Set.mem_setOf_eq] at hS
    linarith
  have hp1 := side_prob a b D hε hε1 hδ m hm W1 hW1m hW1
  have hp2 := side_prob a b D hε hε1 hδ m hm W2 hW2m hW2
  have hp3 := side_prob a b D hε hε1 hδ m hm W3 hW3m hW3
  have hp4 := side_prob a b D hε hε1 hδ m hm W4 hW4m hW4
  calc sampleLaw D c m {S | ε < errorOf D c (tightestFit S)}
      ≤ sampleLaw D c m ({S | ¬ IsLabeledBy c S} ∪ A1 ∪ A2 ∪ A3 ∪ A4) := measure_mono hcover
    _ ≤ sampleLaw D c m {S | ¬ IsLabeledBy c S} + sampleLaw D c m A1 + sampleLaw D c m A2 +
          sampleLaw D c m A3 + sampleLaw D c m A4 := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ 0 + ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) +
          ENNReal.ofReal (δ / 4) := by
        rw [hnull]
        gcongr
    _ = ENNReal.ofReal δ := by
        have h4 : δ / 4 + δ / 4 + δ / 4 + δ / 4 = δ := by ring
        rw [zero_add, ← ENNReal.ofReal_add, ← ENNReal.ofReal_add, ← ENNReal.ofReal_add, h4] <;>
          positivity

theorem rect_main (a b : ℝ × ℝ) (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 4 / ε * Real.log (4 / δ) ≤ m) :
    (∀ S : Fin m → (ℝ × ℝ) × Bool, IsLabeledBy (rectConcept a b) S →
      IsConsistent (tightestFit S) S) ∧
    sampleLaw D (rectConcept a b) m {S | ε < errorOf D (rectConcept a b) (tightestFit S)} ≤
      ENNReal.ofReal δ ∧
    PACLearnable rectangleClass rectangleClass := by
  refine ⟨fun S hS => tf_consistent a b S hS, rect_bound a b D hε hδ m hm, ?_⟩
  intro ε' δ' hε' _ hδ' _
  refine ⟨⌈4 / ε' * Real.log (4 / δ')⌉₊, tightestFit, tf_mem, ?_⟩
  intro c' hc' _ D' hD'
  obtain ⟨a', b', rfl⟩ := hc'
  haveI := hD'
  exact rect_bound a' b' D' hε' hδ' _ (Nat.le_ceil _)

end ComputationalLearning

open ComputationalLearning

theorem solution (a b : ℝ × ℝ) (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D]
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 4 / ε * Real.log (4 / δ) ≤ m) :
    (∀ S : Fin m → (ℝ × ℝ) × Bool, IsLabeledBy (rectConcept a b) S →
      IsConsistent (tightestFit S) S) ∧
    sampleLaw D (rectConcept a b) m {S | ε < errorOf D (rectConcept a b) (tightestFit S)} ≤
      ENNReal.ofReal δ ∧
    PACLearnable rectangleClass rectangleClass := by
  exact rect_main a b D hε hδ hδ1 m hm
