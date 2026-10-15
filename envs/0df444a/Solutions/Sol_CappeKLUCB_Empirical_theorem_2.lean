-- Prove2me | solution 1 for CappeKLUCB.Empirical.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T09:46:32.436007+00:00
-- url     : https://prove2.me/submissions/6bcffd1b-8406-4463-95a5-a6f3120a871d

import Mathlib
import Definitions.Def_CappeKLUCB_Empirical_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
open scoped ENNReal NNReal

namespace CappeKLUCB.Empirical

/-- In the initialization rounds `1..K` an index run plays each arm at most once. -/
lemma init_card_le_one {Ω : Type*} {K : ℕ} {U : Fin K → ℕ → Ω → ℝ} {I : ℕ → Ω → Fin K}
    (hrun : CappeKLUCB.ExpFam.IsIndexRun U I) (a : Fin K) (ω : Ω) :
    ((Finset.range K).filter (fun s => I (s + 1) ω = a)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_range] at hx hy
  by_contra hne
  have key : ∀ x y, x < K → y < K → I (x + 1) ω = a → I (y + 1) ω = a → x < y → False := by
    intro x y hxK hyK hxa hya hxy
    have h0 := (hrun ω y).1 hyK
    unfold pullCount at h0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
    exact h0 (Finset.mem_range.mpr hxy) (by rw [hxa, hya])
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x y hx.1 hy.1 hx.2 hy.2 h
  · exact key y x hy.1 hx.1 hy.2 hx.2 h

lemma pullCount_le_init_add {Ω : Type*} {K : ℕ} {U : Fin K → ℕ → Ω → ℝ} {I : ℕ → Ω → Fin K}
    (hrun : CappeKLUCB.ExpFam.IsIndexRun U I) (a : Fin K) (T : ℕ) (ω : Ω) :
    (pullCount I a T ω : ℝ) ≤
      1 + ∑ t ∈ Finset.Ico K T, Set.indicator {ω | I (t + 1) ω = a} (1 : Ω → ℝ) ω := by
  have hsub : (Finset.range T).filter (fun s => I (s + 1) ω = a) ⊆
      (Finset.range K).filter (fun s => I (s + 1) ω = a) ∪
        (Finset.Ico K T).filter (fun s => I (s + 1) ω = a) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico] at hs ⊢
    by_cases hsK : s < K
    · exact Or.inl ⟨hsK, hs.2⟩
    · exact Or.inr ⟨⟨by omega, hs.1⟩, hs.2⟩
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 := init_card_le_one hrun a ω
  have h3 : (((Finset.Ico K T).filter (fun s => I (s + 1) ω = a)).card : ℝ) =
      ∑ t ∈ Finset.Ico K T, Set.indicator {ω | I (t + 1) ω = a} (1 : Ω → ℝ) ω := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp [Set.indicator_apply]
  have h4 : (pullCount I a T ω : ℝ) ≤ (((Finset.range K).filter (fun s => I (s + 1) ω = a)).card : ℝ)
      + (((Finset.Ico K T).filter (fun s => I (s + 1) ω = a)).card : ℝ) := by
    unfold pullCount; exact_mod_cast h1
  have h5 : (((Finset.range K).filter (fun s => I (s + 1) ω = a)).card : ℝ) ≤ 1 := by
    exact_mod_cast h2
  linarith

lemma init_injOn {Ω : Type*} {K : ℕ} {U : Fin K → ℕ → Ω → ℝ} {I : ℕ → Ω → Fin K}
    (hrun : CappeKLUCB.ExpFam.IsIndexRun U I) (ω : Ω) :
    Set.InjOn (fun s => I (s + 1) ω) (Finset.range K : Set ℕ) := by
  have key : ∀ x y, y < K → I (x + 1) ω = I (y + 1) ω → x < y → False := by
    intro x y hyK hxy hlt
    have h0 := (hrun ω y).1 hyK
    unfold pullCount at h0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
    exact h0 (Finset.mem_range.mpr hlt) hxy
  intro x hx y hy hxy
  simp only [Finset.coe_range, Set.mem_Iio] at hx hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x y hy hxy h
  · exact key y x hx hxy.symm h

lemma init_card_eq_one {Ω : Type*} {K : ℕ} {U : Fin K → ℕ → Ω → ℝ} {I : ℕ → Ω → Fin K}
    (hrun : CappeKLUCB.ExpFam.IsIndexRun U I) (a : Fin K) (ω : Ω) :
    ((Finset.range K).filter (fun s => I (s + 1) ω = a)).card = 1 := by
  have h1 := init_card_le_one hrun a ω
  have hsurj : (Finset.range K).image (fun s => I (s + 1) ω) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn (init_injOn hrun ω), Finset.card_range, Fintype.card_fin]
  have hmem : a ∈ (Finset.range K).image (fun s => I (s + 1) ω) := by
    rw [hsurj]; exact Finset.mem_univ a
  obtain ⟨s, hs, hsa⟩ := Finset.mem_image.mp hmem
  have h2 : 0 < ((Finset.range K).filter (fun s => I (s + 1) ω = a)).card :=
    Finset.card_pos.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, hsa⟩⟩
  omega

lemma pullCount_eq_init_add {Ω : Type*} {K : ℕ} {U : Fin K → ℕ → Ω → ℝ} {I : ℕ → Ω → Fin K}
    (hrun : CappeKLUCB.ExpFam.IsIndexRun U I) (a : Fin K) (t : ℕ) (hKt : K ≤ t) (ω : Ω) :
    pullCount I a t ω = 1 + ((Finset.Ico K t).filter (fun s => I (s + 1) ω = a)).card := by
  unfold pullCount
  have hr : Finset.range t = Finset.range K ∪ Finset.Ico K t := by
    ext s; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  rw [hr, Finset.filter_union, Finset.card_union_of_disjoint, init_card_eq_one hrun a ω]
  rw [Finset.disjoint_left]
  intro s h1 h2
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at h1 h2
  omega

lemma pullCount_bounds {Ω : Type*} {K : ℕ} {U : Fin K → ℕ → Ω → ℝ} {I : ℕ → Ω → Fin K}
    (hrun : CappeKLUCB.ExpFam.IsIndexRun U I) (a : Fin K) (t : ℕ) (hKt : K ≤ t) (ω : Ω) :
    1 ≤ pullCount I a t ω ∧ pullCount I a t ω ≤ t + 1 - K := by
  rw [pullCount_eq_init_add hrun a t hKt ω]
  have := (Finset.card_filter_le (Finset.Ico K t) (fun s => I (s + 1) ω = a)).trans
    (Nat.card_Ico K t).le
  omega

lemma pullCount_mono {Ω : Type*} {K : ℕ} (I : ℕ → Ω → Fin K) (a : Fin K) {t t' : ℕ}
    (h : t ≤ t') (ω : Ω) : pullCount I a t ω ≤ pullCount I a t' ω := by
  unfold pullCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

lemma pullCount_succ_of_eq {Ω : Type*} {K : ℕ} (I : ℕ → Ω → Fin K) (a : Fin K) (t : ℕ) (ω : Ω)
    (h : I (t + 1) ω = a) : pullCount I a (t + 1) ω = pullCount I a t ω + 1 := by
  unfold pullCount
  rw [Finset.range_add_one, Finset.filter_insert, if_pos h, Finset.card_insert_of_notMem]
  simp

lemma measurable_pullCount {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (I : ℕ → Ω → Fin K)
    (hI : ∀ t, Measurable (I t)) (a : Fin K) (t : ℕ) :
    Measurable (fun ω => pullCount I a t ω) := by
  have : (fun ω => pullCount I a t ω) =
      fun ω => ∑ s ∈ Finset.range t, if I (s + 1) ω = a then 1 else 0 := by
    funext ω; unfold pullCount; rw [Finset.card_filter]
  rw [this]
  refine Finset.measurable_sum _ (fun s _ => ?_)
  exact Measurable.ite ((hI (s + 1)) (measurableSet_singleton a)) measurable_const measurable_const

lemma sum_measureReal_inter_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (C : ι → Set α) (hC : ∀ i, MeasurableSet (C i)) (S : Finset ι)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (C i) (C j)) (B : Set α) :
    ∑ i ∈ S, μ.real (B ∩ C i) ≤ μ.real B := by
  classical
  induction S using Finset.induction_on generalizing B with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    have hd' : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (C x) (C y) := fun x hx y hy hxy =>
      hd x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    have h1 := ih hd' (B \ C i)
    have heq : ∀ j ∈ S, μ.real ((B \ C i) ∩ C j) = μ.real (B ∩ C j) := by
      intro j hj
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      have hdis := hd i (Finset.mem_insert_self i S) j (Finset.mem_insert_of_mem hj) hij
      congr 1
      ext x
      simp only [Set.mem_inter_iff, Set.mem_sdiff]
      constructor
      · rintro ⟨⟨hb, _⟩, hc⟩; exact ⟨hb, hc⟩
      · rintro ⟨hb, hc⟩; exact ⟨⟨hb, fun hci => Set.disjoint_left.mp hdis hci hc⟩, hc⟩
    rw [Finset.sum_congr rfl heq] at h1
    have h2 := measureReal_inter_add_sdiff (μ := μ) (s := B) (hC i)
    linarith


/-! ## Empirical measures and the confidence region -/

lemma empMeasure_isProb (x : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    IsProbabilityMeasure (empMeasure x n) := by
  constructor
  unfold empMeasure
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
  have h0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  exact ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top n)

lemma empMeasure_compl (x : ℕ → ℝ) (n : ℕ) (S : Finset ℝ) (hS : empSupp x n ⊆ S) :
    empMeasure x n (↑S : Set ℝ)ᶜ = 0 := by
  unfold empMeasure
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  have : ∀ k ∈ Finset.range n, Measure.dirac (x k) (↑S : Set ℝ)ᶜ = 0 := by
    intro k hk
    rw [Measure.dirac_apply' _ (S.measurableSet.compl)]
    have hx : x k ∈ S := hS (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
    simp [hx]
  rw [Finset.sum_eq_zero this, smul_zero]

lemma inC_mono {μ γ γ' : ℝ} {ν : Measure ℝ} (h : γ ≤ γ') (hC : InC μ γ ν) : InC μ γ' ν := by
  obtain ⟨ν', h1, h2, h3⟩ := hC
  exact ⟨ν', h1, h2, h3.trans (ENNReal.ofReal_le_ofReal h)⟩

/-- If the empirical index exceeds `μdag`, the empirical measure lies in `𝒞_{μdag, ε}`. -/
lemma inC_of_lt_elUpper (x : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hx : ∀ k, x k ∈ Set.Icc (0 : ℝ) 1) (μdag ε : ℝ)
    (h : μdag < elUpper (empSupp x n) (empMeasure x n) ε) :
    InC μdag ε (empMeasure x n) := by
  have := empMeasure_isProb x hn
  have hne : Set.Nonempty {m : ℝ | ∃ ν' : Measure ℝ, IsProbabilityMeasure ν' ∧
      ν' (↑(insert 1 (empSupp x n)) : Set ℝ)ᶜ = 0 ∧
      InformationTheory.klDiv (empMeasure x n) ν' ≤ ENNReal.ofReal ε ∧ m = mean ν'} := by
    refine ⟨mean (empMeasure x n), empMeasure x n, inferInstance,
      empMeasure_compl x n _ (Finset.subset_insert _ _), ?_, rfl⟩
    rw [InformationTheory.klDiv_self]; exact zero_le
  obtain ⟨m, ⟨ν', hP, hsupp, hkl, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hne h
  refine ⟨ν', ⟨hP, insert 1 (empSupp x n), ?_, hsupp⟩, hlt, hkl⟩
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact ⟨zero_le_one, le_rfl⟩
  · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    exact hx k

lemma f₂_mono {t T : ℕ} (ht : 2 ≤ t) (h : t ≤ T) : f₂ t ≤ f₂ T := by
  have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hTt : (t : ℝ) ≤ T := by exact_mod_cast h
  have h1 : Real.log t ≤ Real.log T := Real.log_le_log (by linarith) hTt
  have h2 : 0 < Real.log t := Real.log_pos (by linarith)
  have h3 : Real.log (Real.log t) ≤ Real.log (Real.log T) := Real.log_le_log h2 h1
  unfold f₂; linarith

lemma f₂_pos {T : ℕ} (hT : 3 ≤ T) : 0 < f₂ T := by
  have hT' : (3 : ℝ) ≤ T := by exact_mod_cast hT
  have h3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  have hlx : Real.log 3 ≤ Real.log T := Real.log_le_log (by norm_num) hT'
  have : 0 < Real.log (Real.log T) := Real.log_pos (by linarith)
  unfold f₂; linarith

/-! ## expected_draws_split -/

theorem eds_aux {K : ℕ} (hK : 2 ≤ K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (hF : ∀ a, IsFinSupp01 (P.map (X a 0))) (hbdd : ∀ a k ω, X a k ω ∈ Set.Icc (0 : ℝ) 1)
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t)) (hrun : IsEmpKLUCBRun f₂ X I)
    (a astar : Fin K) (hastar : μ astar = bestMean μ) (μdag : ℝ) (T : ℕ) :
    ∫ ω, (pullCount I a T ω : ℝ) ∂P ≤
      1 + ∑ t ∈ Finset.Ico K T, P.real {ω | μdag ≥ index f₂ X I astar t ω}
        + ∑ t ∈ Finset.Ico K T,
            P.real {ω | InC μdag (f₂ t / (pullCount I a t ω : ℝ))
                (empMeasure (fun k => X a k ω) (pullCount I a t ω)) ∧ I (t + 1) ω = a} := by
  have hms : ∀ t, MeasurableSet {ω | I (t + 1) ω = a} := fun t =>
    (hI (t + 1)) (measurableSet_singleton a)
  have hint : ∀ t, Integrable (Set.indicator {ω | I (t + 1) ω = a} (1 : Ω → ℝ)) P := fun t =>
    (integrable_const (1 : ℝ)).indicator (hms t)
  have hmono : ∫ ω, (pullCount I a T ω : ℝ) ∂P ≤
      ∫ ω, (1 + ∑ t ∈ Finset.Ico K T, Set.indicator {ω | I (t + 1) ω = a} (1 : Ω → ℝ) ω) ∂P := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => by positivity)) ?_
      (Filter.Eventually.of_forall (fun ω => pullCount_le_init_add hrun a T ω))
    exact (integrable_const 1).add (integrable_finsetSum _ (fun t _ => hint t))
  have heq : ∫ ω, (1 + ∑ t ∈ Finset.Ico K T, Set.indicator {ω | I (t + 1) ω = a} (1 : Ω → ℝ) ω) ∂P
      = 1 + ∑ t ∈ Finset.Ico K T, P.real {ω | I (t + 1) ω = a} := by
    rw [integral_add (integrable_const 1) (integrable_finsetSum _ (fun t _ => hint t)),
      integral_finsetSum _ (fun t _ => hint t)]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    congr 1
    refine Finset.sum_congr rfl (fun t _ => ?_)
    exact integral_indicator_one (hms t)
  have hpt : ∀ t ∈ Finset.Ico K T, P.real {ω | I (t + 1) ω = a} ≤
      P.real {ω | μdag ≥ index f₂ X I astar t ω} +
        P.real {ω | InC μdag (f₂ t / (pullCount I a t ω : ℝ))
                (empMeasure (fun k => X a k ω) (pullCount I a t ω)) ∧ I (t + 1) ω = a} := by
    intro t ht
    have hKt : K ≤ t := (Finset.mem_Ico.mp ht).1
    have hsub : {ω | I (t + 1) ω = a} ⊆ {ω | μdag ≥ index f₂ X I astar t ω} ∪
        {ω | InC μdag (f₂ t / (pullCount I a t ω : ℝ))
                (empMeasure (fun k => X a k ω) (pullCount I a t ω)) ∧ I (t + 1) ω = a} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      by_cases hc : μdag ≥ index f₂ X I astar t ω
      · exact Or.inl hc
      · right
        refine ⟨?_, hω⟩
        have hmax := (hrun ω t).2 hKt astar
        rw [hω] at hmax
        push Not at hc
        have hlt : μdag < index f₂ X I a t ω := lt_of_lt_of_le hc hmax
        exact inC_of_lt_elUpper (fun k => X a k ω) (pullCount_bounds hrun a t hKt ω).1
          (fun k => hbdd a k ω) μdag _ hlt
    exact (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib] at hsum
  linarith [hmono, heq, hsum]

/-! ## local_times_8 -/

theorem lt8_aux {K : ℕ} (hK : 2 ≤ K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (hF : ∀ a, IsFinSupp01 (P.map (X a 0))) (hbdd : ∀ a k ω, X a k ω ∈ Set.Icc (0 : ℝ) 1)
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t)) (hrun : IsEmpKLUCBRun f₂ X I)
    (a : Fin K) (μdag : ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Ico K T,
        P.real {ω | InC μdag (f₂ t / (pullCount I a t ω : ℝ))
            (empMeasure (fun k => X a k ω) (pullCount I a t ω)) ∧ I (t + 1) ω = a}
      ≤ ∑ n ∈ Finset.Icc 1 (T - K),
          P.real {ω | InC μdag (f₂ T / (n : ℝ)) (empMeasure (fun k => X a k ω) n)} := by
  set B : ℕ → Set Ω := fun n => {ω | InC μdag (f₂ T / (n : ℝ)) (empMeasure (fun k => X a k ω) n)}
    with hB
  set C : ℕ → ℕ → Set Ω := fun n t => {ω | pullCount I a t ω = n ∧ I (t + 1) ω = a} with hCdef
  have hCm : ∀ n t, MeasurableSet (C n t) := fun n t =>
    ((measurable_pullCount I hI a t) (measurableSet_singleton n)).inter
      ((hI (t + 1)) (measurableSet_singleton a))
  have hstep : ∀ t ∈ Finset.Ico K T,
      P.real {ω | InC μdag (f₂ t / (pullCount I a t ω : ℝ))
            (empMeasure (fun k => X a k ω) (pullCount I a t ω)) ∧ I (t + 1) ω = a} ≤
        ∑ n ∈ Finset.Icc 1 (T - K), P.real (B n ∩ C n t) := by
    intro t ht
    have hKt : K ≤ t := (Finset.mem_Ico.mp ht).1
    have htT : t < T := (Finset.mem_Ico.mp ht).2
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans (measureReal_biUnion_finset_le _ _)
    intro ω hω
    obtain ⟨hlt, hIa⟩ := hω
    have hb := pullCount_bounds hrun a t hKt ω
    simp only [Set.mem_iUnion]
    refine ⟨pullCount I a t ω, Finset.mem_Icc.mpr ⟨hb.1, by omega⟩, ?_, rfl, hIa⟩
    show InC μdag (f₂ T / (pullCount I a t ω : ℝ))
      (empMeasure (fun k => X a k ω) (pullCount I a t ω))
    have hpos : (0 : ℝ) < pullCount I a t ω := by exact_mod_cast hb.1
    refine inC_mono ?_ hlt
    exact div_le_div_of_nonneg_right (f₂_mono (by omega) htT.le) hpos.le
  have hdisj : ∀ n, ∀ i ∈ Finset.Ico K T, ∀ j ∈ Finset.Ico K T, i ≠ j →
      Disjoint (C n i) (C n j) := by
    intro n i _ j _ hij
    rw [Set.disjoint_left]
    rintro ω ⟨hi1, hi2⟩ ⟨hj1, hj2⟩
    rcases lt_or_gt_of_ne hij with h | h
    · have := pullCount_mono I a (Nat.succ_le_of_lt h) ω
      rw [pullCount_succ_of_eq I a i ω hi2] at this
      omega
    · have := pullCount_mono I a (Nat.succ_le_of_lt h) ω
      rw [pullCount_succ_of_eq I a j ω hj2] at this
      omega
  calc ∑ t ∈ Finset.Ico K T,
        P.real {ω | InC μdag (f₂ t / (pullCount I a t ω : ℝ))
            (empMeasure (fun k => X a k ω) (pullCount I a t ω)) ∧ I (t + 1) ω = a}
      ≤ ∑ t ∈ Finset.Ico K T, ∑ n ∈ Finset.Icc 1 (T - K), P.real (B n ∩ C n t) :=
        Finset.sum_le_sum hstep
    _ = ∑ n ∈ Finset.Icc 1 (T - K), ∑ t ∈ Finset.Ico K T, P.real (B n ∩ C n t) :=
        Finset.sum_comm
    _ ≤ ∑ n ∈ Finset.Icc 1 (T - K), P.real (B n) := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        exact sum_measureReal_inter_le P (C n) (hCm n) _ (hdisj n) (B n)

/-! ## general_bound_10 -/

theorem gb10_aux {K : ℕ} (hK : 2 ≤ K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (hF : ∀ a, IsFinSupp01 (P.map (X a 0))) (hbdd : ∀ a k ω, X a k ω ∈ Set.Icc (0 : ℝ) 1)
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t)) (hrun : IsEmpKLUCBRun f₂ X I)
    (a astar : Fin K) (hastar : μ astar = bestMean μ) (ha : μ a < bestMean μ)
    (μdag : ℝ) (T : ℕ) (hT : 3 ≤ T) :
    ∫ ω, (pullCount I a T ω : ℝ) ∂P ≤
      f₂ T / (Kinf (P.map (X a 0)) (bestMean μ)).toReal
        + ∑ n ∈ Finset.Icc (⌈f₂ T / (Kinf (P.map (X a 0)) (bestMean μ)).toReal⌉₊ + 1) (T - K),
            P.real {ω | InC μdag (f₂ T / (n : ℝ)) (empMeasure (fun k => X a k ω) n)}
        + ∑ t ∈ Finset.Ico K T, P.real {ω | μdag ≥ index f₂ X I astar t ω}
        + 2 := by
  set D := (Kinf (P.map (X a 0)) (bestMean μ)).toReal with hD
  have hx0 : 0 ≤ f₂ T / D := div_nonneg (f₂_pos hT).le ENNReal.toReal_nonneg
  have hceil : ((⌈f₂ T / D⌉₊ : ℕ) : ℝ) < f₂ T / D + 1 := Nat.ceil_lt_add_one hx0
  have hE := eds_aux hK P X μ hX hF hbdd I hI hrun a astar hastar μdag T
  have hL := lt8_aux hK P X μ hX hF hbdd I hI hrun a μdag T
  set n0 := ⌈f₂ T / D⌉₊ with hn0
  set E : ℕ → ℝ := fun n =>
    P.real {ω | InC μdag (f₂ T / (n : ℝ)) (empMeasure (fun k => X a k ω) n)} with hEdef
  have hsub : Finset.Icc 1 (T - K) ⊆ Finset.Icc 1 n0 ∪ Finset.Icc (n0 + 1) (T - K) := by
    intro n hn
    simp only [Finset.mem_Icc, Finset.mem_union] at hn ⊢
    omega
  have hdisj : Disjoint (Finset.Icc 1 n0) (Finset.Icc (n0 + 1) (T - K)) := by
    rw [Finset.disjoint_left]
    intro n h1 h2
    simp only [Finset.mem_Icc] at h1 h2
    omega
  have hsplit : ∑ n ∈ Finset.Icc 1 (T - K), E n ≤
      (n0 : ℝ) + ∑ n ∈ Finset.Icc (n0 + 1) (T - K), E n := by
    calc ∑ n ∈ Finset.Icc 1 (T - K), E n
        ≤ ∑ n ∈ Finset.Icc 1 n0 ∪ Finset.Icc (n0 + 1) (T - K), E n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => measureReal_nonneg)
      _ = ∑ n ∈ Finset.Icc 1 n0, E n + ∑ n ∈ Finset.Icc (n0 + 1) (T - K), E n :=
          Finset.sum_union hdisj
      _ ≤ (n0 : ℝ) + ∑ n ∈ Finset.Icc (n0 + 1) (T - K), E n := by
          gcongr
          calc ∑ n ∈ Finset.Icc 1 n0, E n ≤ ∑ n ∈ Finset.Icc 1 n0, (1 : ℝ) :=
                Finset.sum_le_sum (fun _ _ => measureReal_le_one)
            _ = n0 := by simp
  linarith

/-! ## Honda-Takemura duality and the suboptimal-arm tail (PROVED) -/


/-- A measure carried by a finite set is the sum of its atoms. -/
lemma eq_sum_dirac (ν : Measure ℝ) (S : Finset ℝ) (h : ν (↑S : Set ℝ)ᶜ = 0) :
    ν = ∑ x ∈ S, ν {x} • Measure.dirac x := by
  classical
  ext A hA
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
  rw [← measure_inter_conull h (s := A)]
  have : A ∩ (↑S : Set ℝ) = ↑(S.filter (· ∈ A)) := by
    ext x; simp [and_comm]
  rw [this, ← sum_measure_singleton, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ A <;> simp [hx, Set.indicator]

lemma integral_finsupp (ν : Measure ℝ) [IsFiniteMeasure ν] (S : Finset ℝ)
    (h : ν (↑S : Set ℝ)ᶜ = 0) (f : ℝ → ℝ) :
    ∫ x, f x ∂ν = ∑ x ∈ S, (ν {x}).toReal * f x := by
  conv_lhs => rw [eq_sum_dirac ν S h]
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_smul_measure, integral_dirac]
    simp [smul_eq_mul]
  · intro x _
    exact (integrable_dirac (by simp)).smul_measure (by simp)


lemma integrable_finsupp (ν : Measure ℝ) [IsFiniteMeasure ν] (S : Finset ℝ)
    (h : ν (↑S : Set ℝ)ᶜ = 0) (f : ℝ → ℝ) : Integrable f ν := by
  rw [eq_sum_dirac ν S h]
  refine integrable_finsetSum_measure.2 fun x _ => ?_
  exact (integrable_dirac (by simp)).smul_measure (by simp)

lemma rnDeriv_atom (ν ν' : Measure ℝ) [IsFiniteMeasure ν] [IsFiniteMeasure ν'] (hac : ν ≪ ν')
    (x : ℝ) (hx : 0 < ν' {x}) :
    (ν.rnDeriv ν' x).toReal = (ν {x}).toReal / (ν' {x}).toReal := by
  have h1 := Measure.setLIntegral_rnDeriv hac {x}
  rw [lintegral_singleton] at h1
  have h2 : (ν.rnDeriv ν' x).toReal * (ν' {x}).toReal = (ν {x}).toReal := by
    rw [← ENNReal.toReal_mul, h1]
  have h3 : (ν' {x}).toReal ≠ 0 := (ENNReal.toReal_pos hx.ne' (measure_ne_top _ _)).ne'
  field_simp
  exact h2

lemma ac_of_pos (ν ν' : Measure ℝ) (S : Finset ℝ) (hS : ν (↑S : Set ℝ)ᶜ = 0)
    (hpos : ∀ x ∈ S, 0 < ν {x} → 0 < ν' {x}) : ν ≪ ν' := by
  classical
  intro A hA
  rw [← measure_inter_conull hS (s := A)]
  have : A ∩ (↑S : Set ℝ) = ↑(S.filter (· ∈ A)) := by
    ext x; simp [and_comm]
  rw [this, ← sum_measure_singleton]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.mem_filter] at hx
  have h1 : ν' {x} = 0 := measure_mono_null (Set.singleton_subset_iff.2 hx.2) hA
  by_contra hne
  exact absurd h1 (hpos x hx.1 (pos_iff_ne_zero.2 hne)).ne'

lemma toReal_klDiv_finsupp (ν ν' : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (S : Finset ℝ) (hS : ν (↑S : Set ℝ)ᶜ = 0) (hpos : ∀ x ∈ S, 0 < ν {x} → 0 < ν' {x}) :
    InformationTheory.klDiv ν ν' ≠ ∞ ∧ (InformationTheory.klDiv ν ν').toReal =
      ∑ x ∈ S, (ν {x}).toReal * Real.log ((ν {x}).toReal / (ν' {x}).toReal) := by
  have hac := ac_of_pos ν ν' S hS hpos
  have hint : Integrable (llr ν ν') ν := integrable_finsupp ν S hS _
  refine ⟨InformationTheory.klDiv_ne_top hac hint, ?_⟩
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac (by simp), integral_finsupp ν S hS]
  refine Finset.sum_congr rfl fun x hx => ?_
  by_cases h0 : ν {x} = 0
  · simp [h0]
  · rw [llr, rnDeriv_atom ν ν' hac x (hpos x hx (pos_iff_ne_zero.2 h0))]

lemma integral_affine (ν' : Measure ℝ) [IsProbabilityMeasure ν'] (T : Finset ℝ)
    (hT : ν' (↑T : Set ℝ)ᶜ = 0) (μ l : ℝ) :
    ∫ x, (1 - l * (x - μ)) ∂ν' = 1 - l * (∫ x, x ∂ν' - μ) := by
  have hi : Integrable (fun x : ℝ => x) ν' := integrable_finsupp ν' T hT _
  have h1 : Integrable (fun x : ℝ => l * (x - μ)) ν' := (hi.sub (integrable_const μ)).const_mul l
  have h2 : ∫ x, (1 - l * (x - μ)) ∂ν' = ∫ _x, (1:ℝ) ∂ν' - ∫ x, l * (x - μ) ∂ν' :=
    integral_sub (integrable_const _) h1
  have h3 : ∫ x, l * (x - μ) ∂ν' = l * (∫ x, x ∂ν' - μ) := by
    rw [integral_const_mul, integral_sub hi (integrable_const μ), integral_const]
    simp
  rw [h2, h3]
  simp

/-- Weak duality: for every `ν' ∈ ℱ` with `E ν' > μ` and every `λ ∈ [0, 1/(1-μ))`,
`E_ν log(1 - λ (X - μ)) ≤ KL(ν, ν')`. -/
lemma weak_dual (ν ν' : Measure ℝ) [IsProbabilityMeasure ν] (S : Finset ℝ)
    (hS : ν (↑S : Set ℝ)ᶜ = 0) (hS1 : ∀ x ∈ S, x ≤ 1)
    (hν' : IsFinSupp01 ν') (μ : ℝ) (hmean : μ < mean ν') (l : ℝ) (hl0 : 0 ≤ l)
    (hl1 : l * (1 - μ) ≤ 1) (hwp : ∀ x ∈ S, 0 < ν {x} → 0 < 1 - l * (x - μ)) :
    ENNReal.ofReal (∫ x, Real.log (1 - l * (x - μ)) ∂ν) ≤ InformationTheory.klDiv ν ν' := by
  classical
  obtain ⟨hprob', S', hS'sub, hS'⟩ := hν'
  by_cases hk : InformationTheory.klDiv ν ν' = ∞
  · rw [hk]; exact le_top
  have hac : ν ≪ ν' := by
    by_contra h; exact hk (InformationTheory.klDiv_of_not_ac h)
  have hpos : ∀ x ∈ S, 0 < ν {x} → 0 < ν' {x} := by
    intro x _ hx
    by_contra h
    have h0 : ν' {x} = 0 := by simpa using h
    exact hx.ne' (hac h0)
  obtain ⟨-, hKL⟩ := toReal_klDiv_finsupp ν ν' S hS hpos
  have hne : InformationTheory.klDiv ν ν' ≠ ∞ := hk
  rw [← ENNReal.ofReal_toReal hne]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hKL, integral_finsupp ν S hS]
  -- the union carrying ν'
  set T := S ∪ S' with hT
  have hTnull : ν' (↑T : Set ℝ)ᶜ = 0 := by
    refine measure_mono_null ?_ hS'
    intro x hx hx'
    exact hx (by simp [hT, Finset.mem_union, hx'])
  have hw : ∀ x ∈ S, 0 ≤ 1 - l * (x - μ) := by
    intro x hx
    nlinarith [hS1 x hx]
  -- termwise inequality
  have hterm : ∀ x ∈ S, (ν {x}).toReal - (ν' {x}).toReal * (1 - l * (x - μ)) ≤
      (ν {x}).toReal * Real.log ((ν {x}).toReal / (ν' {x}).toReal) -
        (ν {x}).toReal * Real.log (1 - l * (x - μ)) := by
    intro x hx
    have hw0 := hw x hx
    have hq0 : 0 ≤ (ν' {x}).toReal := ENNReal.toReal_nonneg
    have hp0 : 0 ≤ (ν {x}).toReal := ENNReal.toReal_nonneg
    by_cases hp : ν {x} = 0
    · simp [hp]; positivity
    · have hpp : 0 < (ν {x}).toReal := ENNReal.toReal_pos hp (measure_ne_top _ _)
      have hqq : 0 < (ν' {x}).toReal :=
        ENNReal.toReal_pos (hpos x hx (pos_iff_ne_zero.2 hp)).ne' (measure_ne_top _ _)
      have hwpos : 0 < 1 - l * (x - μ) := hwp x hx (pos_iff_ne_zero.2 hp)
      set p := (ν {x}).toReal
      set q := (ν' {x}).toReal
      set w := 1 - l * (x - μ)
      have hlog := Real.log_le_sub_one_of_pos (show 0 < q * w / p by positivity)
      have key : Real.log (p / q) - Real.log w = - Real.log (q * w / p) := by
        rw [Real.log_div hpp.ne' hqq.ne', Real.log_div (by positivity) hpp.ne',
          Real.log_mul hqq.ne' hwpos.ne']
        ring
      have h4 : p * (q * w / p - 1) = q * w - p := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hlog hp0]
  have hsumq : ∑ x ∈ S, (ν' {x}).toReal * (1 - l * (x - μ)) ≤ 1 - l * (mean ν' - μ) := by
    have e := integral_affine ν' T hTnull μ l
    rw [integral_finsupp ν' T hTnull] at e
    unfold mean
    rw [← e]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) ?_
    intro i hi hiS
    have hi' : i ∈ S' := by
      rcases Finset.mem_union.1 hi with h | h
      · exact absurd h hiS
      · exact h
    have hi1 : i ≤ 1 := (hS'sub hi').2
    exact mul_nonneg ENNReal.toReal_nonneg (by nlinarith)
  have hsum1 : ∑ x ∈ S, (ν {x}).toReal = 1 := by
    have := integral_finsupp ν S hS (fun _ => (1:ℝ))
    simpa using this.symm
  have hsumT := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum1] at hsumT
  have hm : 0 ≤ l * (mean ν' - μ) := mul_nonneg hl0 (by linarith)
  linarith


/-- The finitely supported measure with atom weights `ω` on the finite set `T`. -/
noncomputable def pm (T : Finset ℝ) (ω : ℝ → ℝ) : Measure ℝ :=
  ∑ x ∈ T, ENNReal.ofReal (ω x) • Measure.dirac x

lemma pm_singleton (T : Finset ℝ) (ω : ℝ → ℝ) (y : ℝ) :
    pm T ω {y} = if y ∈ T then ENNReal.ofReal (ω y) else 0 := by
  classical
  unfold pm
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton y), smul_eq_mul]
  have : ∀ x ∈ T, ENNReal.ofReal (ω x) * ({y} : Set ℝ).indicator 1 x =
      if y = x then ENNReal.ofReal (ω x) else 0 := by
    intro x _
    by_cases h : y = x <;> simp [Set.indicator, h, eq_comm]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]

lemma pm_compl (T : Finset ℝ) (ω : ℝ → ℝ) : pm T ω (↑T : Set ℝ)ᶜ = 0 := by
  classical
  unfold pm
  rw [Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  simp [Measure.dirac_apply' _ (MeasurableSet.compl (T.measurableSet)), Set.indicator, hx]

lemma pm_univ (T : Finset ℝ) (ω : ℝ → ℝ) : pm T ω Set.univ = ∑ x ∈ T, ENNReal.ofReal (ω x) := by
  unfold pm
  rw [Measure.finsetSum_apply]
  simp

lemma pm_prob (T : Finset ℝ) (ω : ℝ → ℝ) (h0 : ∀ x ∈ T, 0 ≤ ω x) (h1 : ∑ x ∈ T, ω x = 1) :
    IsProbabilityMeasure (pm T ω) := by
  refine ⟨?_⟩
  rw [pm_univ, ← ENNReal.ofReal_sum_of_nonneg h0, h1]
  simp

lemma pm_toReal_singleton (T : Finset ℝ) (ω : ℝ → ℝ) (h0 : ∀ x ∈ T, 0 ≤ ω x) (y : ℝ) :
    (pm T ω {y}).toReal = if y ∈ T then ω y else 0 := by
  rw [pm_singleton]
  by_cases hy : y ∈ T
  · simp [hy, ENNReal.toReal_ofReal (h0 y hy)]
  · simp [hy]

lemma mean_pm (T : Finset ℝ) (ω : ℝ → ℝ) (h0 : ∀ x ∈ T, 0 ≤ ω x) (h1 : ∑ x ∈ T, ω x = 1) :
    mean (pm T ω) = ∑ x ∈ T, ω x * x := by
  haveI := pm_prob T ω h0 h1
  unfold mean
  rw [integral_finsupp (pm T ω) T (pm_compl T ω) (fun x => x)]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [pm_toReal_singleton T ω h0, if_pos hx]

lemma pm_finSupp (T : Finset ℝ) (ω : ℝ → ℝ) (h0 : ∀ x ∈ T, 0 ≤ ω x) (h1 : ∑ x ∈ T, ω x = 1)
    (hT : (↑T : Set ℝ) ⊆ Set.Icc 0 1) : IsFinSupp01 (pm T ω) :=
  ⟨pm_prob T ω h0 h1, T, hT, pm_compl T ω⟩


lemma sum_insert_one (S : Finset ℝ) (f : ℝ → ℝ) (h : (1:ℝ) ∉ S → f 1 = 0) :
    ∑ x ∈ insert (1:ℝ) S, f x = ∑ x ∈ S, f x := by
  classical
  by_cases h1 : (1:ℝ) ∈ S
  · rw [Finset.insert_eq_of_mem h1]
  · rw [Finset.sum_insert h1, h h1, zero_add]

/-- Construction step of strong duality: a dual point `l` with `Z ≤ 1` and a nonnegative mean
defect yields a witness of `Kinf ≤ H(l)`. -/
lemma kinf_le_of_dual_point (ν : Measure ℝ) [IsProbabilityMeasure ν] (S : Finset ℝ)
    (hS : ν (↑S : Set ℝ)ᶜ = 0) (hS01 : ∀ x ∈ S, x ∈ Set.Icc (0:ℝ) 1) (μ : ℝ) (hμ1 : μ < 1)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l * (1 - μ) ≤ 1)
    (hwp : ∀ x ∈ S, 0 < ν {x} → 0 < 1 - l * (x - μ))
    (hZ : ∑ x ∈ S, (ν {x}).toReal / (1 - l * (x - μ)) ≤ 1)
    (hΦ : 0 ≤ ∑ x ∈ S, (ν {x}).toReal * (x - μ) / (1 - l * (x - μ)) +
      (1 - ∑ x ∈ S, (ν {x}).toReal / (1 - l * (x - μ))) * (1 - μ)) :
    Kinf ν μ ≤ ENNReal.ofReal (∫ x, Real.log (1 - l * (x - μ)) ∂ν) := by
  classical
  set Z := ∑ x ∈ S, (ν {x}).toReal / (1 - l * (x - μ)) with hZdef
  set Φ := ∑ x ∈ S, (ν {x}).toReal * (x - μ) / (1 - l * (x - μ)) with hΦdef
  set H := ∫ x, Real.log (1 - l * (x - μ)) ∂ν with hH
  have hp1 : ∑ x ∈ S, (ν {x}).toReal = 1 := by
    have := integral_finsupp ν S hS (fun _ => (1:ℝ))
    simpa using this.symm
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  -- η = 1 - exp(-ε)
  set η : ℝ := 1 - Real.exp (-(ε:ℝ)) with hη
  have hεpos : (0:ℝ) < ε := by exact_mod_cast hε
  have hexp0 : 0 < Real.exp (-(ε:ℝ)) := Real.exp_pos _
  have hexp1 : Real.exp (-(ε:ℝ)) < 1 := by
    simpa using Real.exp_lt_exp.2 (show -(ε:ℝ) < 0 by linarith)
  have hη0 : 0 < η := by rw [hη]; linarith
  have hη1 : η < 1 := by rw [hη]; linarith
  have hlogη : - Real.log (1 - η) = ε := by
    rw [hη]; simp
  -- the witness
  set T := insert (1:ℝ) S with hT
  set ω : ℝ → ℝ := fun x => (1 - η) * ((ν {x}).toReal / (1 - l * (x - μ))) +
    (if x = 1 then (1 - η) * (1 - Z) + η else 0) with hω
  have hpdiv : ∀ x, 0 ≤ (ν {x}).toReal / (1 - l * (x - μ)) ∨ ν {x} = 0 ∨ True := fun _ => Or.inr (Or.inr trivial)
  have hnn : ∀ x ∈ S, 0 ≤ (ν {x}).toReal / (1 - l * (x - μ)) := by
    intro x hx
    by_cases hp : ν {x} = 0
    · simp [hp]
    · exact div_nonneg ENNReal.toReal_nonneg (hwp x hx (pos_iff_ne_zero.2 hp)).le
  have hν1 : (1:ℝ) ∉ S → ν {1} = 0 := by
    intro h1
    exact measure_mono_null (Set.singleton_subset_iff.2 (by simpa using h1)) hS
  have hf1 : (1:ℝ) ∉ S → (ν {(1:ℝ)}).toReal / (1 - l * (1 - μ)) = 0 := by
    intro h1; simp [hν1 h1]
  have hnnT : ∀ x ∈ T, 0 ≤ (ν {x}).toReal / (1 - l * (x - μ)) := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · by_cases h1 : (1:ℝ) ∈ S
      · exact hnn _ h1
      · rw [hf1 h1]
    · exact hnn x hx
  have hZT : ∑ x ∈ T, (ν {x}).toReal / (1 - l * (x - μ)) = Z :=
    sum_insert_one S _ hf1
  have hω0 : ∀ x ∈ T, 0 ≤ ω x := by
    intro x hx
    simp only [hω]
    have h1 := hnnT x hx
    have h2 : 0 ≤ (if x = 1 then (1 - η) * (1 - Z) + η else 0) := by
      split_ifs
      · nlinarith
      · exact le_rfl
    nlinarith
  have hωsum : ∑ x ∈ T, ω x = 1 := by
    simp only [hω]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hZT, Finset.sum_ite_eq' T 1]
    rw [if_pos (Finset.mem_insert_self _ _)]
    ring
  have hTsub : (↑T : Set ℝ) ⊆ Set.Icc 0 1 := by
    intro x hx
    have hx' : x ∈ T := by exact_mod_cast hx
    rcases Finset.mem_insert.1 hx' with rfl | hx2
    · simp
    · exact hS01 x hx2
  have hfs := pm_finSupp T ω hω0 hωsum hTsub
  have hmean : μ < mean (pm T ω) := by
    rw [mean_pm T ω hω0 hωsum]
    have e1 : ∑ x ∈ T, ω x * x - μ = ∑ x ∈ T, ω x * (x - μ) := by
      have : ∑ x ∈ T, ω x * (x - μ) = ∑ x ∈ T, ω x * x - μ * ∑ x ∈ T, ω x := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [this, hωsum]; ring
    have e2 : ∑ x ∈ T, ω x * (x - μ) = (1 - η) * Φ + ((1 - η) * (1 - Z) + η) * (1 - μ) := by
      simp only [hω]
      have : ∀ x ∈ T, ((1 - η) * ((ν {x}).toReal / (1 - l * (x - μ))) +
          (if x = 1 then (1 - η) * (1 - Z) + η else 0)) * (x - μ) =
          (1 - η) * ((ν {x}).toReal * (x - μ) / (1 - l * (x - μ))) +
          (if x = 1 then ((1 - η) * (1 - Z) + η) * (1 - μ) else 0) := by
        intro x _
        by_cases hx : x = 1
        · subst hx; simp; ring
        · simp [hx]; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_ite_eq' T 1, if_pos (Finset.mem_insert_self _ _)]
      congr 2
      have hh : ∀ x, (1 - l * (x - μ)) ≠ 0 ∨ True := fun _ => Or.inr trivial
      rw [hΦdef]
      exact (sum_insert_one S (fun x => (ν {x}).toReal * (x - μ) / (1 - l * (x - μ)))
        (fun h1 => by simp [hν1 h1]))
    have : 0 < ((1 - η) * (Φ + (1 - Z) * (1 - μ)) + η * (1 - μ)) := by
      have : 0 ≤ (1 - η) * (Φ + (1 - Z) * (1 - μ)) := mul_nonneg (by linarith) hΦ
      nlinarith
    linarith [e1, e2]
  -- the divergence bound
  have hpos : ∀ x ∈ S, 0 < ν {x} → 0 < (pm T ω) {x} := by
    intro x hx hνx
    haveI := pm_prob T ω hω0 hωsum
    rw [pm_singleton, if_pos (Finset.mem_insert_of_mem hx)]
    refine ENNReal.ofReal_pos.2 ?_
    have hp : 0 < (ν {x}).toReal := ENNReal.toReal_pos hνx.ne' (measure_ne_top _ _)
    have hq : 0 < (ν {x}).toReal / (1 - l * (x - μ)) := div_pos hp (hwp x hx hνx)
    simp only [hω]
    have h2 : 0 ≤ (if x = 1 then (1 - η) * (1 - Z) + η else 0) := by
      split_ifs
      · nlinarith
      · exact le_rfl
    nlinarith
  haveI := pm_prob T ω hω0 hωsum
  obtain ⟨hne, hKL⟩ := toReal_klDiv_finsupp ν (pm T ω) S hS hpos
  have hbound : ∑ x ∈ S, (ν {x}).toReal * Real.log ((ν {x}).toReal / ((pm T ω) {x}).toReal) ≤
      H - Real.log (1 - η) := by
    have hHs : H = ∑ x ∈ S, (ν {x}).toReal * Real.log (1 - l * (x - μ)) :=
      integral_finsupp ν S hS _
    have : ∀ x ∈ S, (ν {x}).toReal * Real.log ((ν {x}).toReal / ((pm T ω) {x}).toReal) ≤
        (ν {x}).toReal * Real.log (1 - l * (x - μ)) - (ν {x}).toReal * Real.log (1 - η) := by
      intro x hx
      by_cases hp0 : ν {x} = 0
      · simp [hp0]
      · have hνx : 0 < ν {x} := pos_iff_ne_zero.2 hp0
        have hp : 0 < (ν {x}).toReal := ENNReal.toReal_pos hp0 (measure_ne_top _ _)
        have hw := hwp x hx hνx
        have hq : 0 < ((pm T ω) {x}).toReal :=
          ENNReal.toReal_pos (hpos x hx hνx).ne' (measure_ne_top _ _)
        have hqω : ((pm T ω) {x}).toReal = ω x := by
          rw [pm_toReal_singleton T ω hω0, if_pos (Finset.mem_insert_of_mem hx)]
        rw [hqω] at hq ⊢
        have hωge : (1 - η) * ((ν {x}).toReal / (1 - l * (x - μ))) ≤ ω x := by
          simp only [hω]
          have h2 : 0 ≤ (if x = 1 then (1 - η) * (1 - Z) + η else 0) := by
            split_ifs
            · nlinarith
            · exact le_rfl
          linarith
        have hle : (ν {x}).toReal / ω x ≤ (1 - l * (x - μ)) / (1 - η) := by
          rw [div_le_div_iff₀ hq (by linarith)]
          have : (1 - η) * ((ν {x}).toReal / (1 - l * (x - μ))) * (1 - l * (x - μ)) =
              (1 - η) * (ν {x}).toReal := by field_simp
          nlinarith [mul_le_mul_of_nonneg_right hωge hw.le]
        have hlog := Real.log_le_log (div_pos hp hq) hle
        rw [Real.log_div hw.ne' (by linarith)] at hlog
        nlinarith [mul_le_mul_of_nonneg_left hlog hp.le]
    refine le_trans (Finset.sum_le_sum this) ?_
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, hHs]
    linarith
  have hKLle : InformationTheory.klDiv ν (pm T ω) ≤ ENNReal.ofReal (H + ε) := by
    rw [← ENNReal.ofReal_toReal hne]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hKL]
    linarith [hbound, hlogη]
  have hKinf : Kinf ν μ ≤ InformationTheory.klDiv ν (pm T ω) := by
    unfold Kinf
    exact iInf_le_of_le _ (iInf_le_of_le hfs (iInf_le_of_le hmean le_rfl))
  calc Kinf ν μ ≤ ENNReal.ofReal (H + ε) := hKinf.trans hKLle
    _ ≤ ENNReal.ofReal H + ENNReal.ofReal ε := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal H + ε := by rw [ENNReal.ofReal_coe_nnreal]


lemma dual_point_witness (ν : Measure ℝ) [IsProbabilityMeasure ν] (S : Finset ℝ)
    (hS : ν (↑S : Set ℝ)ᶜ = 0) (hS01 : ∀ x ∈ S, x ∈ Set.Icc (0:ℝ) 1) (μ : ℝ) (hμ1 : μ < 1)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l * (1 - μ) ≤ 1)
    (hwp : ∀ x ∈ S, 0 < ν {x} → 0 < 1 - l * (x - μ))
    (hZ : ∑ x ∈ S, (ν {x}).toReal / (1 - l * (x - μ)) ≤ 1)
    (hΦ : 0 ≤ ∑ x ∈ S, (ν {x}).toReal * (x - μ) / (1 - l * (x - μ)) +
      (1 - ∑ x ∈ S, (ν {x}).toReal / (1 - l * (x - μ))) * (1 - μ)) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ ν' : Measure ℝ, IsProbabilityMeasure ν' ∧
      ν' (↑(insert (1:ℝ) S) : Set ℝ)ᶜ = 0 ∧ μ < mean ν' ∧
      InformationTheory.klDiv ν ν' ≤ ENNReal.ofReal ((∫ x, Real.log (1 - l * (x - μ)) ∂ν) + ε) := by
  classical
  set Z := ∑ x ∈ S, (ν {x}).toReal / (1 - l * (x - μ)) with hZdef
  set Φ := ∑ x ∈ S, (ν {x}).toReal * (x - μ) / (1 - l * (x - μ)) with hΦdef
  set H := ∫ x, Real.log (1 - l * (x - μ)) ∂ν with hH
  have hp1 : ∑ x ∈ S, (ν {x}).toReal = 1 := by
    have := integral_finsupp ν S hS (fun _ => (1:ℝ))
    simpa using this.symm
  intro ε hε
  -- η = 1 - exp(-ε)
  set η : ℝ := 1 - Real.exp (-(ε:ℝ)) with hη
  have hεpos : (0:ℝ) < ε := by exact_mod_cast hε
  have hexp0 : 0 < Real.exp (-(ε:ℝ)) := Real.exp_pos _
  have hexp1 : Real.exp (-(ε:ℝ)) < 1 := by
    simpa using Real.exp_lt_exp.2 (show -(ε:ℝ) < 0 by linarith)
  have hη0 : 0 < η := by rw [hη]; linarith
  have hη1 : η < 1 := by rw [hη]; linarith
  have hlogη : - Real.log (1 - η) = ε := by
    rw [hη]; simp
  -- the witness
  set T := insert (1:ℝ) S with hT
  set ω : ℝ → ℝ := fun x => (1 - η) * ((ν {x}).toReal / (1 - l * (x - μ))) +
    (if x = 1 then (1 - η) * (1 - Z) + η else 0) with hω
  have hpdiv : ∀ x, 0 ≤ (ν {x}).toReal / (1 - l * (x - μ)) ∨ ν {x} = 0 ∨ True := fun _ => Or.inr (Or.inr trivial)
  have hnn : ∀ x ∈ S, 0 ≤ (ν {x}).toReal / (1 - l * (x - μ)) := by
    intro x hx
    by_cases hp : ν {x} = 0
    · simp [hp]
    · exact div_nonneg ENNReal.toReal_nonneg (hwp x hx (pos_iff_ne_zero.2 hp)).le
  have hν1 : (1:ℝ) ∉ S → ν {1} = 0 := by
    intro h1
    exact measure_mono_null (Set.singleton_subset_iff.2 (by simpa using h1)) hS
  have hf1 : (1:ℝ) ∉ S → (ν {(1:ℝ)}).toReal / (1 - l * (1 - μ)) = 0 := by
    intro h1; simp [hν1 h1]
  have hnnT : ∀ x ∈ T, 0 ≤ (ν {x}).toReal / (1 - l * (x - μ)) := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · by_cases h1 : (1:ℝ) ∈ S
      · exact hnn _ h1
      · rw [hf1 h1]
    · exact hnn x hx
  have hZT : ∑ x ∈ T, (ν {x}).toReal / (1 - l * (x - μ)) = Z :=
    sum_insert_one S _ hf1
  have hω0 : ∀ x ∈ T, 0 ≤ ω x := by
    intro x hx
    simp only [hω]
    have h1 := hnnT x hx
    have h2 : 0 ≤ (if x = 1 then (1 - η) * (1 - Z) + η else 0) := by
      split_ifs
      · nlinarith
      · exact le_rfl
    nlinarith
  have hωsum : ∑ x ∈ T, ω x = 1 := by
    simp only [hω]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hZT, Finset.sum_ite_eq' T 1]
    rw [if_pos (Finset.mem_insert_self _ _)]
    ring
  have hTsub : (↑T : Set ℝ) ⊆ Set.Icc 0 1 := by
    intro x hx
    have hx' : x ∈ T := by exact_mod_cast hx
    rcases Finset.mem_insert.1 hx' with rfl | hx2
    · simp
    · exact hS01 x hx2
  have hfs := pm_finSupp T ω hω0 hωsum hTsub
  have hmean : μ < mean (pm T ω) := by
    rw [mean_pm T ω hω0 hωsum]
    have e1 : ∑ x ∈ T, ω x * x - μ = ∑ x ∈ T, ω x * (x - μ) := by
      have : ∑ x ∈ T, ω x * (x - μ) = ∑ x ∈ T, ω x * x - μ * ∑ x ∈ T, ω x := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [this, hωsum]; ring
    have e2 : ∑ x ∈ T, ω x * (x - μ) = (1 - η) * Φ + ((1 - η) * (1 - Z) + η) * (1 - μ) := by
      simp only [hω]
      have : ∀ x ∈ T, ((1 - η) * ((ν {x}).toReal / (1 - l * (x - μ))) +
          (if x = 1 then (1 - η) * (1 - Z) + η else 0)) * (x - μ) =
          (1 - η) * ((ν {x}).toReal * (x - μ) / (1 - l * (x - μ))) +
          (if x = 1 then ((1 - η) * (1 - Z) + η) * (1 - μ) else 0) := by
        intro x _
        by_cases hx : x = 1
        · subst hx; simp; ring
        · simp [hx]; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_ite_eq' T 1, if_pos (Finset.mem_insert_self _ _)]
      congr 2
      have hh : ∀ x, (1 - l * (x - μ)) ≠ 0 ∨ True := fun _ => Or.inr trivial
      rw [hΦdef]
      exact (sum_insert_one S (fun x => (ν {x}).toReal * (x - μ) / (1 - l * (x - μ)))
        (fun h1 => by simp [hν1 h1]))
    have : 0 < ((1 - η) * (Φ + (1 - Z) * (1 - μ)) + η * (1 - μ)) := by
      have : 0 ≤ (1 - η) * (Φ + (1 - Z) * (1 - μ)) := mul_nonneg (by linarith) hΦ
      nlinarith
    linarith [e1, e2]
  -- the divergence bound
  have hpos : ∀ x ∈ S, 0 < ν {x} → 0 < (pm T ω) {x} := by
    intro x hx hνx
    haveI := pm_prob T ω hω0 hωsum
    rw [pm_singleton, if_pos (Finset.mem_insert_of_mem hx)]
    refine ENNReal.ofReal_pos.2 ?_
    have hp : 0 < (ν {x}).toReal := ENNReal.toReal_pos hνx.ne' (measure_ne_top _ _)
    have hq : 0 < (ν {x}).toReal / (1 - l * (x - μ)) := div_pos hp (hwp x hx hνx)
    simp only [hω]
    have h2 : 0 ≤ (if x = 1 then (1 - η) * (1 - Z) + η else 0) := by
      split_ifs
      · nlinarith
      · exact le_rfl
    nlinarith
  haveI := pm_prob T ω hω0 hωsum
  obtain ⟨hne, hKL⟩ := toReal_klDiv_finsupp ν (pm T ω) S hS hpos
  have hbound : ∑ x ∈ S, (ν {x}).toReal * Real.log ((ν {x}).toReal / ((pm T ω) {x}).toReal) ≤
      H - Real.log (1 - η) := by
    have hHs : H = ∑ x ∈ S, (ν {x}).toReal * Real.log (1 - l * (x - μ)) :=
      integral_finsupp ν S hS _
    have : ∀ x ∈ S, (ν {x}).toReal * Real.log ((ν {x}).toReal / ((pm T ω) {x}).toReal) ≤
        (ν {x}).toReal * Real.log (1 - l * (x - μ)) - (ν {x}).toReal * Real.log (1 - η) := by
      intro x hx
      by_cases hp0 : ν {x} = 0
      · simp [hp0]
      · have hνx : 0 < ν {x} := pos_iff_ne_zero.2 hp0
        have hp : 0 < (ν {x}).toReal := ENNReal.toReal_pos hp0 (measure_ne_top _ _)
        have hw := hwp x hx hνx
        have hq : 0 < ((pm T ω) {x}).toReal :=
          ENNReal.toReal_pos (hpos x hx hνx).ne' (measure_ne_top _ _)
        have hqω : ((pm T ω) {x}).toReal = ω x := by
          rw [pm_toReal_singleton T ω hω0, if_pos (Finset.mem_insert_of_mem hx)]
        rw [hqω] at hq ⊢
        have hωge : (1 - η) * ((ν {x}).toReal / (1 - l * (x - μ))) ≤ ω x := by
          simp only [hω]
          have h2 : 0 ≤ (if x = 1 then (1 - η) * (1 - Z) + η else 0) := by
            split_ifs
            · nlinarith
            · exact le_rfl
          linarith
        have hle : (ν {x}).toReal / ω x ≤ (1 - l * (x - μ)) / (1 - η) := by
          rw [div_le_div_iff₀ hq (by linarith)]
          have : (1 - η) * ((ν {x}).toReal / (1 - l * (x - μ))) * (1 - l * (x - μ)) =
              (1 - η) * (ν {x}).toReal := by field_simp
          nlinarith [mul_le_mul_of_nonneg_right hωge hw.le]
        have hlog := Real.log_le_log (div_pos hp hq) hle
        rw [Real.log_div hw.ne' (by linarith)] at hlog
        nlinarith [mul_le_mul_of_nonneg_left hlog hp.le]
    refine le_trans (Finset.sum_le_sum this) ?_
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, hHs]
    linarith
  have hKLle : InformationTheory.klDiv ν (pm T ω) ≤ ENNReal.ofReal (H + ε) := by
    rw [← ENNReal.ofReal_toReal hne]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hKL]
    linarith [hbound, hlogη]
  exact ⟨pm T ω, pm_prob T ω hω0 hωsum, pm_compl T ω, hmean, hKLle⟩


section dual
variable (ν : Measure ℝ) (S : Finset ℝ) (μ : ℝ)

/-- `Z(l) = E_ν 1/(1 - l (X - μ))`. -/
noncomputable def Zf (l : ℝ) : ℝ := ∑ x ∈ S, (ν {x}).toReal / (1 - l * (x - μ))

/-- `Φ(l) = E_ν (X - μ)/(1 - l (X - μ))`. -/
noncomputable def Phif (l : ℝ) : ℝ := ∑ x ∈ S, (ν {x}).toReal * (x - μ) / (1 - l * (x - μ))

lemma l_mul_Phif (l : ℝ) (hp1 : ∑ x ∈ S, (ν {x}).toReal = 1)
    (hw : ∀ x ∈ S, 0 < ν {x} → 0 < 1 - l * (x - μ)) :
    l * Phif ν S μ l = Zf ν S μ l - 1 := by
  unfold Phif Zf
  have e : ∑ x ∈ S, (ν {x}).toReal / (1 - l * (x - μ)) - 1 =
      ∑ x ∈ S, ((ν {x}).toReal / (1 - l * (x - μ)) - (ν {x}).toReal) := by
    rw [Finset.sum_sub_distrib, hp1]
  rw [Finset.mul_sum, e]
  refine Finset.sum_congr rfl fun x hx => ?_
  by_cases hp : ν {x} = 0
  · simp [hp]
  · have := (hw x hx (pos_iff_ne_zero.2 hp)).ne'
    field_simp
    ring

lemma Phif_zero [IsProbabilityMeasure ν] (hS : ν (↑S : Set ℝ)ᶜ = 0) :
    Phif ν S μ 0 = (∫ x, x ∂ν) - μ := by
  have hp1 : ∑ x ∈ S, (ν {x}).toReal = 1 := by
    have := integral_finsupp ν S hS (fun _ => (1:ℝ))
    simpa using this.symm
  have hm := integral_finsupp ν S hS (fun x => x)
  unfold Phif
  simp only [zero_mul, sub_zero, div_one]
  have : ∑ x ∈ S, (ν {x}).toReal * (x - μ) =
      ∑ x ∈ S, (ν {x}).toReal * x - μ * ∑ x ∈ S, (ν {x}).toReal := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hm, this, hp1]; ring

lemma Phif_cont (b : ℝ)
    (hw : ∀ l ∈ Set.Icc 0 b, ∀ x ∈ S, 0 < ν {x} → 0 < 1 - l * (x - μ)) :
    ContinuousOn (Phif ν S μ) (Set.Icc 0 b) := by
  unfold Phif
  refine continuousOn_finsetSum _ fun x hx => ?_
  by_cases hp : ν {x} = 0
  · simp [hp]; exact continuousOn_const
  · refine ContinuousOn.div continuousOn_const (by fun_prop) fun l hl => ?_
    exact (hw l hl x hx (pos_iff_ne_zero.2 hp)).ne'

lemma exists_zero_Phif [IsProbabilityMeasure ν] (hS : ν (↑S : Set ℝ)ᶜ = 0) (hlt : (∫ x, x ∂ν) < μ)
    (b : ℝ) (hb : 0 < b)
    (hw : ∀ l ∈ Set.Icc 0 b, ∀ x ∈ S, 0 < ν {x} → 0 < 1 - l * (x - μ))
    (hpos : 0 < Phif ν S μ b) : ∃ l ∈ Set.Ioo 0 b, Phif ν S μ l = 0 := by
  have h0 : Phif ν S μ 0 < 0 := by rw [Phif_zero ν S μ hS]; linarith
  have := intermediate_value_Ioo hb.le (Phif_cont ν S μ b hw) (show (0:ℝ) ∈ Set.Ioo _ _ from ⟨h0, hpos⟩)
  obtain ⟨l, hl, hl0⟩ := this
  exact ⟨l, hl, hl0⟩

end dual


/-- Strong duality (Honda–Takemura) for a finitely supported `ν ∈ ℱ` with `E ν < μ < 1`: there is a
dual point `l ∈ [0, 1/(1-μ)]` with `Kinf ν μ ≤ E_ν log(1 - l (X - μ))`. -/
theorem strong_dual (ν : Measure ℝ) [IsProbabilityMeasure ν] (S : Finset ℝ)
    (hS : ν (↑S : Set ℝ)ᶜ = 0) (hS01 : ∀ x ∈ S, x ∈ Set.Icc (0:ℝ) 1) (μ : ℝ) (hμ1 : μ < 1)
    (hlt : (∫ x, x ∂ν) < μ) :
    ∃ l : ℝ, 0 ≤ l ∧ l * (1 - μ) ≤ 1 ∧ (∀ x ∈ S, 0 < ν {x} → 0 < 1 - l * (x - μ)) ∧
      Kinf ν μ ≤ ENNReal.ofReal (∫ x, Real.log (1 - l * (x - μ)) ∂ν) := by
  classical
  have hp1 : ∑ x ∈ S, (ν {x}).toReal = 1 := by
    have := integral_finsupp ν S hS (fun _ => (1:ℝ))
    simpa using this.symm
  have hμ : 0 < 1 - μ := by linarith
  -- positivity of the denominators
  have key : ∀ b : ℝ, 0 ≤ b → b * (1 - μ) ≤ 1 → (ν {1} = 0 ∨ b * (1 - μ) < 1) →
      ∀ l ∈ Set.Icc 0 b, ∀ x ∈ S, 0 < ν {x} → 0 < 1 - l * (x - μ) := by
    intro b hb0 hb1 hb l hl x hx hνx
    have hx1 := (hS01 x hx).2
    have hlb := hl.2
    have hl0 := hl.1
    have h1 : l * (x - μ) ≤ l * (1 - μ) := by nlinarith
    have h2 : l * (1 - μ) ≤ b * (1 - μ) := by nlinarith
    rcases hb with h0 | hlt1
    · by_cases hxe : x = 1
      · subst hxe; exact absurd h0 hνx.ne'
      · have hxl : x < 1 := lt_of_le_of_ne hx1 hxe
        by_cases hl00 : l = 0
        · simp [hl00]
        · have hlpos : 0 < l := lt_of_le_of_ne hl0 (Ne.symm hl00)
          nlinarith
    · linarith
  -- finishing from a zero of Phi
  have finish_zero : ∀ l : ℝ, 0 < l → l * (1 - μ) ≤ 1 →
      (∀ x ∈ S, 0 < ν {x} → 0 < 1 - l * (x - μ)) → Phif ν S μ l = 0 →
      ∃ l : ℝ, 0 ≤ l ∧ l * (1 - μ) ≤ 1 ∧ (∀ x ∈ S, 0 < ν {x} → 0 < 1 - l * (x - μ)) ∧
        Kinf ν μ ≤ ENNReal.ofReal (∫ x, Real.log (1 - l * (x - μ)) ∂ν) := by
    intro l hl hl1 hwl hΦ0
    refine ⟨l, hl.le, hl1, hwl, ?_⟩
    have hZ := l_mul_Phif ν S μ l hp1 hwl
    rw [hΦ0, mul_zero] at hZ
    refine kinf_le_of_dual_point ν S hS hS01 μ hμ1 l hl.le hl1 hwl ?_ ?_
    · have : Zf ν S μ l = 1 := by linarith
      unfold Zf at this; linarith
    · have : Zf ν S μ l = 1 := by linarith
      unfold Zf at this; unfold Phif at hΦ0
      rw [this, hΦ0]; simp
  by_cases h1 : ν {1} = 0
  · -- case A
    set L : ℝ := 1 / (1 - μ) with hL
    have hLpos : 0 < L := by positivity
    have hL1 : L * (1 - μ) = 1 := by rw [hL]; field_simp
    have hwL := key L hLpos.le hL1.le (Or.inl h1)
    by_cases hΦL : Phif ν S μ L ≤ 0
    · refine ⟨L, hLpos.le, hL1.le, hwL L ⟨hLpos.le, le_rfl⟩, ?_⟩
      have hZ := l_mul_Phif ν S μ L hp1 (hwL L ⟨hLpos.le, le_rfl⟩)
      unfold Zf Phif at hZ
      set Φ := ∑ x ∈ S, (ν {x}).toReal * (x - μ) / (1 - L * (x - μ)) with hΦdef
      set Z := ∑ x ∈ S, (ν {x}).toReal / (1 - L * (x - μ)) with hZdef
      have hLΦ : L * Φ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hLpos.le hΦL
      refine kinf_le_of_dual_point ν S hS hS01 μ hμ1 L hLpos.le hL1.le (hwL L ⟨hLpos.le, le_rfl⟩) ?_ ?_
      · linarith
      · have h1Z : 1 - Z = -(L * Φ) := by linarith
        have : Φ + (1 - Z) * (1 - μ) = 0 := by
          rw [h1Z]; linear_combination (-Φ) * hL1
        rw [this]
    · push Not at hΦL
      obtain ⟨l, hl, hl0⟩ := exists_zero_Phif ν S μ hS hlt L hLpos hwL hΦL
      exact finish_zero l hl.1 (by nlinarith [hl.2]) (hwL l ⟨hl.1.le, hl.2.le⟩) hl0
  · -- case B: an atom at 1
    have h1S : (1:ℝ) ∈ S := by
      by_contra h
      exact h1 (measure_mono_null (Set.singleton_subset_iff.2 (by simpa using h)) hS)
    set p1 : ℝ := (ν {1}).toReal with hp1def
    have hp1pos : 0 < p1 := ENNReal.toReal_pos h1 (measure_ne_top _ _)
    have hp1le : p1 ≤ 1 := by
      have : p1 ≤ ∑ x ∈ S, (ν {x}).toReal :=
        Finset.single_le_sum (f := fun x => (ν {x}).toReal) (fun x _ => ENNReal.toReal_nonneg) h1S
      linarith
    set b : ℝ := (1 - p1 / 2) / (1 - μ) with hb
    have hbpos : 0 < b := by rw [hb]; apply div_pos <;> linarith
    have hb1 : b * (1 - μ) = 1 - p1 / 2 := by rw [hb]; field_simp
    have hwb := key b hbpos.le (by linarith) (Or.inr (by linarith))
    have hZb : 2 ≤ Zf ν S μ b := by
      unfold Zf
      have hterm : (ν {(1:ℝ)}).toReal / (1 - b * (1 - μ)) ≤
          ∑ x ∈ S, (ν {x}).toReal / (1 - b * (x - μ)) := by
        refine Finset.single_le_sum (f := fun x => (ν {x}).toReal / (1 - b * (x - μ)))
          (fun x hx => ?_) h1S
        by_cases hp : ν {x} = 0
        · simp [hp]
        · exact div_nonneg ENNReal.toReal_nonneg
            (hwb b ⟨hbpos.le, le_rfl⟩ x hx (pos_iff_ne_zero.2 hp)).le
      have : (ν {(1:ℝ)}).toReal / (1 - b * (1 - μ)) = 2 := by
        rw [hb1, show (1:ℝ) - (1 - p1 / 2) = p1 / 2 by ring]
        field_simp
        exact hp1def.symm
      linarith
    have hΦb : 0 < Phif ν S μ b := by
      have := l_mul_Phif ν S μ b hp1 (hwb b ⟨hbpos.le, le_rfl⟩)
      by_contra hneg
      push Not at hneg
      nlinarith
    obtain ⟨l, hl, hl0⟩ := exists_zero_Phif ν S μ hS hlt b hbpos hwb hΦb
    exact finish_zero l hl.1 (by nlinarith [hl.2]) (hwb l ⟨hl.1.le, hl.2.le⟩) hl0


theorem strong_dual_wit (ν : Measure ℝ) [IsProbabilityMeasure ν] (S : Finset ℝ)
    (hS : ν (↑S : Set ℝ)ᶜ = 0) (hS01 : ∀ x ∈ S, x ∈ Set.Icc (0:ℝ) 1) (μ : ℝ) (hμ1 : μ < 1)
    (hlt : (∫ x, x ∂ν) < μ) :
    ∃ l : ℝ, 0 ≤ l ∧ l * (1 - μ) ≤ 1 ∧ (∀ x ∈ S, 0 < ν {x} → 0 < 1 - l * (x - μ)) ∧
      (∑ x ∈ S, (ν {x}).toReal / (1 - l * (x - μ)) ≤ 1 ∧ 0 ≤ ∑ x ∈ S, (ν {x}).toReal * (x - μ) / (1 - l * (x - μ)) + (1 - ∑ x ∈ S, (ν {x}).toReal / (1 - l * (x - μ))) * (1 - μ)) := by
  classical
  have hp1 : ∑ x ∈ S, (ν {x}).toReal = 1 := by
    have := integral_finsupp ν S hS (fun _ => (1:ℝ))
    simpa using this.symm
  have hμ : 0 < 1 - μ := by linarith
  -- positivity of the denominators
  have key : ∀ b : ℝ, 0 ≤ b → b * (1 - μ) ≤ 1 → (ν {1} = 0 ∨ b * (1 - μ) < 1) →
      ∀ l ∈ Set.Icc 0 b, ∀ x ∈ S, 0 < ν {x} → 0 < 1 - l * (x - μ) := by
    intro b hb0 hb1 hb l hl x hx hνx
    have hx1 := (hS01 x hx).2
    have hlb := hl.2
    have hl0 := hl.1
    have h1 : l * (x - μ) ≤ l * (1 - μ) := by nlinarith
    have h2 : l * (1 - μ) ≤ b * (1 - μ) := by nlinarith
    rcases hb with h0 | hlt1
    · by_cases hxe : x = 1
      · subst hxe; exact absurd h0 hνx.ne'
      · have hxl : x < 1 := lt_of_le_of_ne hx1 hxe
        by_cases hl00 : l = 0
        · simp [hl00]
        · have hlpos : 0 < l := lt_of_le_of_ne hl0 (Ne.symm hl00)
          nlinarith
    · linarith
  -- finishing from a zero of Phi
  have finish_zero : ∀ l : ℝ, 0 < l → l * (1 - μ) ≤ 1 →
      (∀ x ∈ S, 0 < ν {x} → 0 < 1 - l * (x - μ)) → Phif ν S μ l = 0 →
      ∃ l : ℝ, 0 ≤ l ∧ l * (1 - μ) ≤ 1 ∧ (∀ x ∈ S, 0 < ν {x} → 0 < 1 - l * (x - μ)) ∧
        (∑ x ∈ S, (ν {x}).toReal / (1 - l * (x - μ)) ≤ 1 ∧ 0 ≤ ∑ x ∈ S, (ν {x}).toReal * (x - μ) / (1 - l * (x - μ)) + (1 - ∑ x ∈ S, (ν {x}).toReal / (1 - l * (x - μ))) * (1 - μ)) := by
    intro l hl hl1 hwl hΦ0
    refine ⟨l, hl.le, hl1, hwl, ?_⟩
    have hZ := l_mul_Phif ν S μ l hp1 hwl
    rw [hΦ0, mul_zero] at hZ
    refine ⟨?_, ?_⟩
    · have : Zf ν S μ l = 1 := by linarith
      unfold Zf at this; linarith
    · have : Zf ν S μ l = 1 := by linarith
      unfold Zf at this; unfold Phif at hΦ0
      rw [this, hΦ0]; simp
  by_cases h1 : ν {1} = 0
  · -- case A
    set L : ℝ := 1 / (1 - μ) with hL
    have hLpos : 0 < L := by positivity
    have hL1 : L * (1 - μ) = 1 := by rw [hL]; field_simp
    have hwL := key L hLpos.le hL1.le (Or.inl h1)
    by_cases hΦL : Phif ν S μ L ≤ 0
    · refine ⟨L, hLpos.le, hL1.le, hwL L ⟨hLpos.le, le_rfl⟩, ?_⟩
      have hZ := l_mul_Phif ν S μ L hp1 (hwL L ⟨hLpos.le, le_rfl⟩)
      unfold Zf Phif at hZ
      set Φ := ∑ x ∈ S, (ν {x}).toReal * (x - μ) / (1 - L * (x - μ)) with hΦdef
      set Z := ∑ x ∈ S, (ν {x}).toReal / (1 - L * (x - μ)) with hZdef
      have hLΦ : L * Φ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hLpos.le hΦL
      refine ⟨?_, ?_⟩
      · linarith
      · have h1Z : 1 - Z = -(L * Φ) := by linarith
        have : Φ + (1 - Z) * (1 - μ) = 0 := by
          rw [h1Z]; linear_combination (-Φ) * hL1
        rw [this]
    · push Not at hΦL
      obtain ⟨l, hl, hl0⟩ := exists_zero_Phif ν S μ hS hlt L hLpos hwL hΦL
      exact finish_zero l hl.1 (by nlinarith [hl.2]) (hwL l ⟨hl.1.le, hl.2.le⟩) hl0
  · -- case B: an atom at 1
    have h1S : (1:ℝ) ∈ S := by
      by_contra h
      exact h1 (measure_mono_null (Set.singleton_subset_iff.2 (by simpa using h)) hS)
    set p1 : ℝ := (ν {1}).toReal with hp1def
    have hp1pos : 0 < p1 := ENNReal.toReal_pos h1 (measure_ne_top _ _)
    have hp1le : p1 ≤ 1 := by
      have : p1 ≤ ∑ x ∈ S, (ν {x}).toReal :=
        Finset.single_le_sum (f := fun x => (ν {x}).toReal) (fun x _ => ENNReal.toReal_nonneg) h1S
      linarith
    set b : ℝ := (1 - p1 / 2) / (1 - μ) with hb
    have hbpos : 0 < b := by rw [hb]; apply div_pos <;> linarith
    have hb1 : b * (1 - μ) = 1 - p1 / 2 := by rw [hb]; field_simp
    have hwb := key b hbpos.le (by linarith) (Or.inr (by linarith))
    have hZb : 2 ≤ Zf ν S μ b := by
      unfold Zf
      have hterm : (ν {(1:ℝ)}).toReal / (1 - b * (1 - μ)) ≤
          ∑ x ∈ S, (ν {x}).toReal / (1 - b * (x - μ)) := by
        refine Finset.single_le_sum (f := fun x => (ν {x}).toReal / (1 - b * (x - μ)))
          (fun x hx => ?_) h1S
        by_cases hp : ν {x} = 0
        · simp [hp]
        · exact div_nonneg ENNReal.toReal_nonneg
            (hwb b ⟨hbpos.le, le_rfl⟩ x hx (pos_iff_ne_zero.2 hp)).le
      have : (ν {(1:ℝ)}).toReal / (1 - b * (1 - μ)) = 2 := by
        rw [hb1, show (1:ℝ) - (1 - p1 / 2) = p1 / 2 by ring]
        field_simp
        exact hp1def.symm
      linarith
    have hΦb : 0 < Phif ν S μ b := by
      have := l_mul_Phif ν S μ b hp1 (hwb b ⟨hbpos.le, le_rfl⟩)
      by_contra hneg
      push Not at hneg
      nlinarith
    obtain ⟨l, hl, hl0⟩ := exists_zero_Phif ν S μ hS hlt b hbpos hwb hΦb
    exact finish_zero l hl.1 (by nlinarith [hl.2]) (hwb l ⟨hl.1.le, hl.2.le⟩) hl0



lemma log_one_add_ge (u : ℝ) (hu : -1/2 ≤ u) : u - 2 * u ^ 2 ≤ Real.log (1 + u) := by
  have h1 : 0 < 1 + u := by linarith
  have h2 := Real.one_sub_inv_le_log_of_pos h1
  have h3 : u - 2 * u ^ 2 ≤ 1 - (1 + u)⁻¹ := by
    have : 1 - (1 + u)⁻¹ = u / (1 + u) := by field_simp; ring
    rw [this, le_div_iff₀ h1]
    nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) (show 0 ≤ 1 + 2 * u by linarith)]
  linarith

/-- A small positive dual point has positive dual value. -/
lemma exists_small_dual_pos (ν : Measure ℝ) [IsProbabilityMeasure ν] (S : Finset ℝ)
    (hS : ν (↑S : Set ℝ)ᶜ = 0) (hS01 : ∀ x ∈ S, x ∈ Set.Icc (0:ℝ) 1) (μ : ℝ) (hμ0 : 0 ≤ μ)
    (hμ1 : μ < 1) (hlt : (∫ x, x ∂ν) < μ) :
    ∃ l : ℝ, 0 < l ∧ l ≤ 1 / 2 ∧ 0 < ∫ x, Real.log (1 - l * (x - μ)) ∂ν := by
  have hp1 : ∑ x ∈ S, (ν {x}).toReal = 1 := by
    have := integral_finsupp ν S hS (fun _ => (1:ℝ))
    simpa using this.symm
  have hm := integral_finsupp ν S hS (fun x => x)
  set d := μ - ∫ x, x ∂ν with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  set l : ℝ := min (1/2) (d / 4) with hl
  have hlpos : 0 < l := lt_min (by norm_num) (by linarith)
  have hl2 : l ≤ 1 / 2 := min_le_left _ _
  have hl4 : l ≤ d / 4 := min_le_right _ _
  refine ⟨l, hlpos, hl2, ?_⟩
  rw [integral_finsupp ν S hS]
  have hterm : ∀ x ∈ S, (ν {x}).toReal * (l * (μ - x) - 2 * l ^ 2) ≤
      (ν {x}).toReal * Real.log (1 - l * (x - μ)) := by
    intro x hx
    have hx01 := hS01 x hx
    have hu : -1/2 ≤ l * (μ - x) := by nlinarith [hx01.1, hx01.2]
    have := log_one_add_ge (l * (μ - x)) hu
    have e : 1 - l * (x - μ) = 1 + l * (μ - x) := by ring
    rw [e]
    have hsq : (l * (μ - x)) ^ 2 ≤ l ^ 2 := by
      have : (μ - x) ^ 2 ≤ 1 := by nlinarith [hx01.1, hx01.2]
      nlinarith [sq_nonneg l]
    exact mul_le_mul_of_nonneg_left (by nlinarith) ENNReal.toReal_nonneg
  refine lt_of_lt_of_le ?_ (Finset.sum_le_sum hterm)
  have : ∑ x ∈ S, (ν {x}).toReal * (l * (μ - x) - 2 * l ^ 2) = l * d - 2 * l ^ 2 := by
    have e : ∀ x ∈ S, (ν {x}).toReal * (l * (μ - x) - 2 * l ^ 2) =
        (l * μ - 2 * l ^ 2) * (ν {x}).toReal - l * ((ν {x}).toReal * x) := fun x _ => by ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp1, ← hm]
    rw [hd]; ring
  rw [this]
  nlinarith


/-- Weak duality in the form `ofReal H(l) ≤ Kinf`. -/
lemma ofReal_dual_le_Kinf (ν : Measure ℝ) [IsProbabilityMeasure ν] (S : Finset ℝ)
    (hS : ν (↑S : Set ℝ)ᶜ = 0) (hS01 : ∀ x ∈ S, x ∈ Set.Icc (0:ℝ) 1) (μ l : ℝ) (hl0 : 0 ≤ l)
    (hl1 : l * (1 - μ) ≤ 1) (hwp : ∀ x ∈ S, 0 < ν {x} → 0 < 1 - l * (x - μ)) :
    ENNReal.ofReal (∫ x, Real.log (1 - l * (x - μ)) ∂ν) ≤ Kinf ν μ := by
  unfold Kinf
  refine le_iInf fun ν' => le_iInf fun hν' => le_iInf fun hm => ?_
  exact weak_dual ν ν' S hS (fun x hx => (hS01 x hx).2) hν' μ hm l hl0 hl1 hwp

/-- The infimum `Kinf ν μ` is attained as a dual value, and it is positive and finite. -/
theorem kinf_dual_value (ν : Measure ℝ) [IsProbabilityMeasure ν] (S : Finset ℝ)
    (hS : ν (↑S : Set ℝ)ᶜ = 0) (hS01 : ∀ x ∈ S, x ∈ Set.Icc (0:ℝ) 1) (μ : ℝ) (hμ0 : 0 ≤ μ)
    (hμ1 : μ < 1) (hlt : (∫ x, x ∂ν) < μ) :
    ∃ l : ℝ, 0 ≤ l ∧ l * (1 - μ) ≤ 1 ∧ (∀ x ∈ S, 0 < ν {x} → 0 < 1 - l * (x - μ)) ∧
      Kinf ν μ ≠ ∞ ∧ 0 < (Kinf ν μ).toReal ∧
      (Kinf ν μ).toReal = ∫ x, Real.log (1 - l * (x - μ)) ∂ν := by
  obtain ⟨l, hl0, hl1, hwp, hle⟩ := strong_dual ν S hS hS01 μ hμ1 hlt
  have hge := ofReal_dual_le_Kinf ν S hS hS01 μ l hl0 hl1 hwp
  have heq : Kinf ν μ = ENNReal.ofReal (∫ x, Real.log (1 - l * (x - μ)) ∂ν) := le_antisymm hle hge
  have hfin : Kinf ν μ ≠ ∞ := by rw [heq]; exact ENNReal.ofReal_ne_top
  obtain ⟨l₀, hl₀pos, hl₀2, hH⟩ := exists_small_dual_pos ν S hS hS01 μ hμ0 hμ1 hlt
  have hwp₀ : ∀ x ∈ S, 0 < ν {x} → 0 < 1 - l₀ * (x - μ) := by
    intro x hx _
    have := hS01 x hx
    nlinarith [this.1, this.2]
  have hl₀1 : l₀ * (1 - μ) ≤ 1 := by nlinarith
  have hge₀ := ofReal_dual_le_Kinf ν S hS hS01 μ l₀ hl₀pos.le hl₀1 hwp₀
  have hpos : 0 < (Kinf ν μ).toReal := by
    refine ENNReal.toReal_pos ?_ hfin
    intro h0
    rw [h0] at hge₀
    have := ENNReal.ofReal_pos.2 hH
    exact absurd (lt_of_lt_of_le this hge₀) (lt_irrefl _)
  refine ⟨l, hl0, hl1, hwp, hfin, hpos, ?_⟩
  rw [heq, ENNReal.toReal_ofReal]
  rw [heq] at hpos
  by_contra hneg
  push Not at hneg
  rw [ENNReal.ofReal_of_nonpos hneg.le] at hpos
  simp at hpos




lemma geom_exp_sum_bound (x : ℝ) (hx : 0 < x) (s : Finset ℕ) :
    ∑ n ∈ s, Real.exp (-(n : ℝ) * x) ≤ 1 + 1 / x := by
  set r := Real.exp (-x) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr]; simpa using Real.exp_lt_exp.2 (show -x < 0 by linarith)
  have hterm : ∀ n : ℕ, Real.exp (-(n : ℝ) * x) = r ^ n := by
    intro n; rw [hr, ← Real.exp_nat_mul]; congr 1; ring
  simp_rw [hterm]
  have hsub : s ⊆ Finset.range (s.sup id + 1) := by
    intro n hn; rw [Finset.mem_range]; exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
  calc ∑ n ∈ s, r ^ n ≤ ∑ n ∈ Finset.range (s.sup id + 1), r ^ n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
    _ ≤ 1 / (1 - r) := by
        have := geom_sum_Ico_le_of_lt_one (m := 0) (n := s.sup id + 1) hr0.le hr1
        rw [← Finset.range_eq_Ico] at this
        simpa using this
    _ ≤ 1 + 1 / x := by
        have h1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
        have h2 : r * (1 + x) ≤ 1 := by
          have : r * Real.exp x = 1 := by rw [hr, ← Real.exp_add]; simp
          nlinarith
        have h5 : x / (1 + x) ≤ 1 - r := by
          rw [div_le_iff₀ (by linarith)]; nlinarith
        have h6 := one_div_le_one_div_of_le (by positivity) h5
        refine h6.trans (le_of_eq ?_)
        field_simp
        ring


/-- Counting bound for the tail sum: terms below `f/(𝒦-δ)` count at most once, the others decay
geometrically. -/
lemma sum_tail_bound (K δ σ2 f : ℝ) (hK : 0 < K) (hδ : 0 < δ) (hδK : δ < K) (hσ : 0 < σ2)
    (hf : 0 < f) (N : ℕ) (q : ℕ → ℝ) (hq0 : ∀ n, 0 ≤ q n) (hq1 : ∀ n, q n ≤ 1)
    (hq : ∀ n : ℕ, f ≤ (n : ℝ) * (K - δ) → q n ≤ Real.exp (-(n : ℝ) * (δ ^ 2 / (2 * σ2)))) :
    ∑ n ∈ Finset.Icc (⌈f / K⌉₊ + 1) N, q n ≤ f * δ / (K * (K - δ)) + 1 + 2 * σ2 / δ ^ 2 := by
  classical
  have hKd : 0 < K - δ := by linarith
  set n₁ : ℝ := f / (K - δ) with hn₁
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc (⌈f / K⌉₊ + 1) N) (fun n : ℕ => (n : ℝ) < n₁)]
  have hx : 0 < δ ^ 2 / (2 * σ2) := by positivity
  have hdiff : n₁ - f / K = f * δ / (K * (K - δ)) := by
    rw [hn₁]; field_simp; ring
  have hdiff0 : 0 ≤ n₁ - f / K := by rw [hdiff]; positivity
  have part1 : ∑ n ∈ (Finset.Icc (⌈f / K⌉₊ + 1) N).filter (fun n : ℕ => (n : ℝ) < n₁), q n ≤
      f * δ / (K * (K - δ)) := by
    calc _ ≤ ∑ n ∈ (Finset.Icc (⌈f / K⌉₊ + 1) N).filter (fun n : ℕ => (n : ℝ) < n₁), (1:ℝ) :=
          Finset.sum_le_sum fun n _ => hq1 n
      _ = ((Finset.Icc (⌈f / K⌉₊ + 1) N).filter (fun n : ℕ => (n : ℝ) < n₁)).card := by simp
      _ ≤ f * δ / (K * (K - δ)) := by
          rw [← hdiff]
          have hsub : (Finset.Icc (⌈f / K⌉₊ + 1) N).filter (fun n : ℕ => (n : ℝ) < n₁) ⊆
              Finset.Ioo ⌈f / K⌉₊ ⌈n₁⌉₊ := by
            intro n hn
            rw [Finset.mem_filter, Finset.mem_Icc] at hn
            rw [Finset.mem_Ioo]
            exact ⟨by omega, Nat.lt_ceil.2 hn.2⟩
          refine (Nat.cast_le.2 (Finset.card_le_card hsub)).trans ?_
          rw [Nat.card_Ioo]
          by_cases hle : ⌈n₁⌉₊ ≤ ⌈f / K⌉₊ + 1
          · have : ⌈n₁⌉₊ - ⌈f / K⌉₊ - 1 = 0 := by omega
            rw [this]; simpa using hdiff0
          · push Not at hle
            rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
            have h1 : (⌈n₁⌉₊ : ℝ) < n₁ + 1 := Nat.ceil_lt_add_one (by positivity)
            have h2 : f / K ≤ (⌈f / K⌉₊ : ℝ) := Nat.le_ceil _
            push_cast
            linarith
  have part2 : ∑ n ∈ (Finset.Icc (⌈f / K⌉₊ + 1) N).filter (fun n : ℕ => ¬ (n : ℝ) < n₁), q n ≤
      1 + 2 * σ2 / δ ^ 2 := by
    calc _ ≤ ∑ n ∈ (Finset.Icc (⌈f / K⌉₊ + 1) N).filter (fun n : ℕ => ¬ (n : ℝ) < n₁),
          Real.exp (-(n : ℝ) * (δ ^ 2 / (2 * σ2))) := by
          refine Finset.sum_le_sum fun n hn => hq n ?_
          rw [Finset.mem_filter] at hn
          have := not_lt.1 hn.2
          rw [hn₁, div_le_iff₀ hKd] at this
          exact this
      _ ≤ 1 + 1 / (δ ^ 2 / (2 * σ2)) := geom_exp_sum_bound _ hx _
      _ = 1 + 2 * σ2 / δ ^ 2 := by field_simp
  linarith




/-- Hoeffding lower-deviation bound for a bounded function of i.i.d. coordinates. -/
lemma hoeffding_lower {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hind : iIndepFun Y P) (g : ℝ → ℝ) (hg : Measurable g)
    (c B : ℝ) (hB : 0 < B) (hYm : ∀ k, Measurable (Y k))
    (hbd : ∀ k, ∀ᵐ ω ∂P, |g (Y k ω)| ≤ B) (hmean : ∀ k, ∫ ω, g (Y k ω) ∂P = c)
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    P.real {ω | ∑ i ∈ Finset.range n, g (Y i ω) ≤ (n : ℝ) * (c - δ)} ≤
      Real.exp (-(n : ℝ) * δ ^ 2 / (2 * B ^ 2)) := by
  set Z : ℕ → Ω → ℝ := fun k ω => c - g (Y k ω) with hZ
  have hZind : iIndepFun Z P := hind.comp (fun _ x => c - g x) (fun _ => measurable_const.sub hg)
  have hZmeas : ∀ k, Measurable (Z k) := fun k => measurable_const.sub (hg.comp (hYm k))
  have hZmean : ∀ k, ∫ ω, Z k ω ∂P = 0 := by
    intro k
    have hint : Integrable (fun ω => g (Y k ω)) P := by
      refine Integrable.of_bound (C := B) ((hg.comp (hYm k)).aestronglyMeasurable) ?_
      filter_upwards [hbd k] with ω hω using by simpa using hω
    simp only [hZ]
    rw [integral_sub (integrable_const _) hint, integral_const, hmean k]
    simp
  have hsub : ∀ k, HasSubgaussianMGF (Z k) ((‖(c + B) - (c - B)‖₊ / 2) ^ 2) P := by
    intro k
    have h := hasSubgaussianMGF_of_mem_Icc (μ := P) (X := Z k) (a := c - B) (b := c + B)
      (hZmeas k).aemeasurable (by
        filter_upwards [hbd k] with ω hω
        have := abs_le.1 hω
        constructor <;> simp only [hZ] <;> linarith [this.1, this.2])
    have hm : P[Z k] = 0 := hZmean k
    simpa [hm] using h
  set cB : ℝ≥0 := Real.toNNReal (B ^ 2) with hcB
  have hcBr : (cB : ℝ) = B ^ 2 := Real.coe_toNNReal _ (by positivity)
  have hcpar : ((‖(c + B) - (c - B)‖₊ / 2) ^ 2 : ℝ≥0) = cB := by
    apply NNReal.eq
    rw [hcBr]
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat]
    rw [show (c + B) - (c - B) = 2 * B by ring, abs_of_pos (by positivity)]
    ring
  have key := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hZind (n := n)
    (c := cB) (fun i _ => by rw [← hcpar]; exact hsub i)
    (ε := (n : ℝ) * δ) (by positivity)
  have hset : {ω | ∑ i ∈ Finset.range n, g (Y i ω) ≤ (n : ℝ) * (c - δ)} ⊆
      {ω | (n : ℝ) * δ ≤ ∑ i ∈ Finset.range n, Z i ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, hZ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] at hω ⊢
    nlinarith
  refine (measureReal_mono hset).trans (key.trans (le_of_eq ?_))
  congr 1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (n : ℝ) ≠ 0 := by positivity
    rw [hcBr]
    field_simp




-- NB2 -----------------------------------------------------------------

lemma integral_empMeasure (x : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) (g : ℝ → ℝ) :
    ∫ y, g y ∂(empMeasure x n) = (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, g (x i) := by
  unfold empMeasure
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, one_div]
  · intro i _
    exact integrable_dirac (by simp)

lemma dual_sum_le_of_inC (x : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) (S : Finset ℝ)
    (hxS : ∀ i, i < n → x i ∈ S) (hS01 : ∀ y ∈ S, y ∈ Set.Icc (0:ℝ) 1) (μ l γ : ℝ)
    (hl0 : 0 ≤ l) (hl1 : l * (1 - μ) ≤ 1) (hw : ∀ y ∈ S, 0 < 1 - l * (y - μ)) (hγ : 0 ≤ γ)
    (hC : InC μ γ (empMeasure x n)) :
    ∑ i ∈ Finset.range n, Real.log (1 - l * (x i - μ)) ≤ n * γ := by
  haveI := empMeasure_isProb x hn
  obtain ⟨ν', hν', hm, hkl⟩ := hC
  have hsub : empSupp x n ⊆ S := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hy
    exact hxS i (Finset.mem_range.1 hi)
  have hwd := weak_dual (empMeasure x n) ν' S (empMeasure_compl x n S hsub)
    (fun y hy => (hS01 y hy).2) hν' μ hm l hl0 hl1 (fun y hy _ => hw y hy)
  have h1 := hwd.trans hkl
  rw [ENNReal.ofReal_le_ofReal_iff hγ] at h1
  rw [integral_empMeasure x hn] at h1
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  rw [one_div, inv_mul_le_iff₀ hnpos] at h1
  linarith




lemma exists_pos_support (ν : Measure ℝ) (hν : IsFinSupp01 ν) :
    ∃ S : Finset ℝ, (↑S : Set ℝ) ⊆ Set.Icc 0 1 ∧ ν (↑S : Set ℝ)ᶜ = 0 ∧ ∀ x ∈ S, 0 < ν {x} := by
  classical
  obtain ⟨-, S₀, hS₀, hnull⟩ := hν
  refine ⟨S₀.filter (fun x => 0 < ν {x}), ?_, ?_, ?_⟩
  · intro x hx
    exact hS₀ (Finset.mem_filter.1 (by exact_mod_cast hx)).1
  · have hsub : (↑(S₀.filter (fun x => 0 < ν {x})) : Set ℝ)ᶜ ⊆
        (↑S₀ : Set ℝ)ᶜ ∪ ↑(S₀.filter (fun x => ¬ 0 < ν {x})) := by
      intro x hx
      by_cases h0 : x ∈ S₀
      · right
        have : ¬ 0 < ν {x} := by
          intro hp; exact hx (by simpa [h0] using hp)
        simpa [h0] using this
      · left; simpa using h0
    refine measure_mono_null hsub (measure_union_null hnull ?_)
    rw [← sum_measure_singleton]
    refine Finset.sum_eq_zero fun x hx => ?_
    have := (Finset.mem_filter.1 hx).2
    simpa using this
  · intro x hx
    exact (Finset.mem_filter.1 hx).2


/-- Moving the level from `m` down to `c` costs at most `(m - c)/(1 - m)` per sample in the dual. -/
lemma shift_log_le (y m c l l' : ℝ) (hm1 : m < 1) (hcm : c ≤ m) (hl1 : l * (1 - m) ≤ 1)
    (hl' : l' * (1 - c) = l * (1 - m)) (hw : 0 < 1 - l * (y - m)) :
    0 < 1 - l' * (y - c) ∧
    Real.log (1 - l * (y - m)) ≤ Real.log (1 - l' * (y - c)) + (m - c) / (1 - m) := by
  have h1m : 0 < 1 - m := by linarith
  have h1c : 0 < 1 - c := by linarith
  have hab : (1 - l * (y - m)) * (1 - m) ≤ (1 - l' * (y - c)) * (1 - c) := by
    have e : (1 - l' * (y - c)) * (1 - c) = (1 - c) - l * (1 - m) * (y - c) := by
      linear_combination (-(y - c)) * hl'
    rw [e]
    nlinarith [mul_nonneg (sub_nonneg.2 hcm) (show 0 ≤ 1 - l * (1 - m) by linarith)]
  have hbpos : 0 < 1 - l' * (y - c) := by
    have : 0 < (1 - l * (y - m)) * (1 - m) := mul_pos hw h1m
    by_contra hneg
    push Not at hneg
    nlinarith
  refine ⟨hbpos, ?_⟩
  have hr0 : 0 < (1 - c) / (1 - m) := by positivity
  have hab' : 1 - l * (y - m) ≤ (1 - l' * (y - c)) * ((1 - c) / (1 - m)) := by
    rw [← mul_div_assoc, le_div_iff₀ h1m]; exact hab
  have h2 := Real.log_le_log hw hab'
  rw [Real.log_mul hbpos.ne' hr0.ne'] at h2
  have h3 := Real.log_le_sub_one_of_pos hr0
  have h4 : (1 - c) / (1 - m) - 1 = (m - c) / (1 - m) := by
    rw [div_sub_one h1m.ne']; congr 1; ring
  linarith

/-- Per-`n` tail bound for the suboptimal arm at the shifted level `c ≤ m`. -/
lemma nb_term' {K : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ) (a : Fin K)
    (S : Finset ℝ) (hS : (P.map (X a 0)) (↑S : Set ℝ)ᶜ = 0) (hS01 : ∀ y ∈ S, y ∈ Set.Icc (0:ℝ) 1)
    (m c l B Kc δ f : ℝ) (hm1 : m < 1) (hcm : c ≤ m) (hl0 : 0 ≤ l) (hl1 : l * (1 - m) ≤ 1)
    (hw : ∀ y ∈ S, 0 < 1 - l * (y - m)) (hB : 0 < B)
    (hBS : ∀ y ∈ S, |Real.log (1 - l * (y - m))| ≤ B)
    (hKc : ∫ y, Real.log (1 - l * (y - m)) ∂(P.map (X a 0)) = Kc)
    (hf : 0 ≤ f) (hδ : 0 < δ) (n : ℕ) (hn : 1 ≤ n)
    (hfn : f + n * ((m - c) / (1 - m)) ≤ (n : ℝ) * (Kc - δ)) :
    P.real {ω | InC c (f / n) (empMeasure (fun k => X a k ω) n)} ≤
      Real.exp (-(n : ℝ) * δ ^ 2 / (2 * B ^ 2)) := by
  set g : ℝ → ℝ := fun y => Real.log (1 - l * (y - m)) with hg
  have hgm : Measurable g := by
    simp only [hg]; fun_prop
  have hae : ∀ k, ∀ᵐ ω ∂P, X a k ω ∈ S := by
    intro k
    rw [ae_iff]
    have hmk := hX.measurable a k
    have : P {ω | ¬ X a k ω ∈ S} = (P.map (X a k)) (↑S : Set ℝ)ᶜ := by
      rw [Measure.map_apply hmk S.measurableSet.compl]
      rfl
    rw [this, (hX.identDistrib a k).map_eq]
    exact hS
  have hind : iIndepFun (fun k => X a k) P := by
    have := hX.indep.precomp (g := fun k : ℕ => ((a, k) : Fin K × ℕ))
      (fun k k' h => by simpa using h)
    exact this
  have hbd : ∀ k, ∀ᵐ ω ∂P, |g (X a k ω)| ≤ B := by
    intro k
    filter_upwards [hae k] with ω hω using hBS _ hω
  have hmean : ∀ k, ∫ ω, g (X a k ω) ∂P = Kc := by
    intro k
    have h1 : ∫ ω, g (X a k ω) ∂P = ∫ ω, g (X a 0 ω) ∂P :=
      ((hX.identDistrib a k).comp hgm).integral_eq
    rw [h1, ← hKc, integral_map (hX.measurable a 0).aemeasurable hgm.aestronglyMeasurable]
  have hHoeff := hoeffding_lower P (fun k => X a k) hind g hgm Kc B hB (fun k => hX.measurable a k)
    hbd hmean n δ hδ
  set G : Set Ω := {ω | ∀ k, X a k ω ∈ S} with hG
  have hGnull : P Gᶜ = 0 := by
    have : Gᶜ ⊆ ⋃ k, {ω | ¬ X a k ω ∈ S} := by
      intro ω hω
      simp only [hG, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hω
      obtain ⟨k, hk⟩ := hω
      exact Set.mem_iUnion.2 ⟨k, hk⟩
    refine measure_mono_null this (measure_iUnion_null fun k => ?_)
    have := hae k
    rwa [ae_iff] at this
  have h1m : 0 < 1 - m := by linarith
  have h1c : 0 < 1 - c := by linarith
  have hl' : l * (1 - m) / (1 - c) * (1 - c) = l * (1 - m) := by field_simp
  have hl'0 : 0 ≤ l * (1 - m) / (1 - c) := by positivity
  have hl'1 : l * (1 - m) / (1 - c) * (1 - c) ≤ 1 := by rw [hl']; exact hl1
  have hsh : ∀ y ∈ S, 0 < 1 - l * (1 - m) / (1 - c) * (y - c) ∧
      g y ≤ Real.log (1 - l * (1 - m) / (1 - c) * (y - c)) + (m - c) / (1 - m) :=
    fun y hy => shift_log_le y m c l (l * (1 - m) / (1 - c)) hm1 hcm hl1 hl' (hw y hy)
  have hsub : {ω | InC c (f / n) (empMeasure (fun k => X a k ω) n)} ⊆
      {ω | ∑ i ∈ Finset.range n, g (X a i ω) ≤ (n : ℝ) * (Kc - δ)} ∪ Gᶜ := by
    intro ω hω
    by_cases hωG : ω ∈ G
    · left
      have hnpos : (0:ℝ) < n := by exact_mod_cast hn
      have hdual := dual_sum_le_of_inC (fun k => X a k ω) hn S (fun i _ => hωG i) hS01 c
        (l * (1 - m) / (1 - c)) (f / n) hl'0 hl'1 (fun y hy => (hsh y hy).1) (by positivity) hω
      have hsum : ∑ i ∈ Finset.range n, g (X a i ω) ≤ ∑ i ∈ Finset.range n,
          (Real.log (1 - l * (1 - m) / (1 - c) * (X a i ω - c)) + (m - c) / (1 - m)) :=
        Finset.sum_le_sum fun i _ => (hsh _ (hωG i)).2
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
      have h2 : (n : ℝ) * (f / n) = f := by field_simp
      show ∑ i ∈ Finset.range n, g (X a i ω) ≤ (n : ℝ) * (Kc - δ)
      linarith
    · right; exact hωG
  calc P.real {ω | InC c (f / n) (empMeasure (fun k => X a k ω) n)}
      ≤ P.real ({ω | ∑ i ∈ Finset.range n, g (X a i ω) ≤ (n : ℝ) * (Kc - δ)} ∪ Gᶜ) :=
        measureReal_mono hsub
    _ ≤ P.real {ω | ∑ i ∈ Finset.range n, g (X a i ω) ≤ (n : ℝ) * (Kc - δ)} + P.real Gᶜ :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-(n : ℝ) * δ ^ 2 / (2 * B ^ 2)) + 0 := by
        exact add_le_add hHoeff (by rw [measureReal_def, hGnull]; simp)
    _ = _ := add_zero _

lemma one_lt_log_of_three_le {T : ℕ} (hT : 3 ≤ T) : 1 < Real.log T := by
  have h3 : (3:ℝ) ≤ T := by exact_mod_cast hT
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- Quantitative core for the suboptimal-arm tail sum at the level `m - m/(4 L^{1/5})`. -/
lemma nb_final_core' {K : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ) (a : Fin K)
    (S : Finset ℝ) (hS : (P.map (X a 0)) (↑S : Set ℝ)ᶜ = 0) (hS01 : ∀ y ∈ S, y ∈ Set.Icc (0:ℝ) 1)
    (m l B Kc : ℝ) (hm0 : 0 < m) (hm1 : m < 1) (hl0 : 0 ≤ l) (hl1 : l * (1 - m) ≤ 1)
    (hw : ∀ y ∈ S, 0 < 1 - l * (y - m)) (hB : 0 < B)
    (hBS : ∀ y ∈ S, |Real.log (1 - l * (y - m))| ≤ B)
    (hKc : ∫ y, Real.log (1 - l * (y - m)) ∂(P.map (X a 0)) = Kc) (hKcpos : 0 < Kc)
    (C₀ : ℝ) (hC₀ : C₀ = max (8 * B ^ 2 / (m / (1 - m) / 2) ^ 2)
      (Real.exp ((2 * (m / (1 - m) / 2) / Kc) ^ 5)))
    (T N : ℕ) (hT : 3 ≤ T) (hN : N ≤ T) :
    ∑ n ∈ Finset.Icc (⌈(Real.log T + Real.log (Real.log T)) / Kc⌉₊ + 1) N,
      P.real {ω | InC (m - m / (4 * Real.log T ^ ((1:ℝ) / 5)))
        ((Real.log T + Real.log (Real.log T)) / (n : ℝ)) (empMeasure (fun k => X a k ω) n)} ≤
    2 * m / ((1 - m) * Kc ^ 2) * Real.log T ^ ((4 : ℝ) / 5) + C₀ * Real.log T ^ ((2 : ℝ) / 5) +
      2 * m / ((1 - m) * Kc ^ 2) + 1 := by
  set L := Real.log T with hLdef
  have hL1 : 1 < L := one_lt_log_of_three_le hT
  have hL0 : 0 < L := by linarith
  set f := L + Real.log L with hf
  have hlogL : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos hL0
  have hlogLpos : 0 < Real.log L := Real.log_pos hL1
  have hfpos : 0 < f := by rw [hf]; linarith
  have hf2L : f ≤ 2 * L := by rw [hf]; linarith
  set c₁ : ℝ := m / (1 - m) / 2 with hc₁
  have h1m : 0 < 1 - m := by linarith
  have hc₁pos : 0 < c₁ := by rw [hc₁]; positivity
  set u : ℝ := L ^ ((1:ℝ) / 5) with hu
  have hu1 : 1 ≤ u := Real.one_le_rpow hL1.le (by norm_num)
  have hu0 : 0 < u := by linarith
  have hu5 : u ^ 5 = L := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hu4 : L ^ ((4:ℝ) / 5) = u ^ 4 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hu2 : L ^ ((2:ℝ) / 5) = u ^ 2 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  rw [hu4, hu2]
  set A : ℝ := 2 * m / ((1 - m) * Kc ^ 2) with hA
  have hApos : 0 ≤ A := by rw [hA]; positivity
  have hC₀1 : 8 * B ^ 2 / c₁ ^ 2 ≤ C₀ := by rw [hC₀]; exact le_max_left _ _
  have hC₀2 : Real.exp ((2 * c₁ / Kc) ^ 5) ≤ C₀ := by rw [hC₀]; exact le_max_right _ _
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le (Real.exp_pos _) hC₀2
  set q : ℕ → ℝ := fun n => P.real {ω | InC (m - m / (4 * u)) (f / (n : ℝ))
    (empMeasure (fun k => X a k ω) n)} with hq
  have hq0 : ∀ n, 0 ≤ q n := fun n => measureReal_nonneg
  have hq1 : ∀ n, q n ≤ 1 := fun n => by
    simp only [hq]
    exact measureReal_le_one
  show ∑ n ∈ Finset.Icc (⌈f / Kc⌉₊ + 1) N, q n ≤ A * u ^ 4 + C₀ * u ^ 2 + A + 1
  by_cases hsmall : u < 2 * c₁ / Kc
  · have hcard : ∑ n ∈ Finset.Icc (⌈f / Kc⌉₊ + 1) N, q n ≤ (T : ℝ) := by
      calc _ ≤ ∑ n ∈ Finset.Icc (⌈f / Kc⌉₊ + 1) N, (1:ℝ) := Finset.sum_le_sum fun n _ => hq1 n
        _ = ((Finset.Icc (⌈f / Kc⌉₊ + 1) N).card : ℝ) := by simp
        _ ≤ (T : ℝ) := by
          have : (Finset.Icc (⌈f / Kc⌉₊ + 1) N).card ≤ T := by
            refine (Nat.card_Icc _ _ ▸ ?_)
            omega
          exact_mod_cast this
    have hT_exp : (T : ℝ) ≤ C₀ := by
      have hTpos : (0:ℝ) < T := by exact_mod_cast (by omega : 0 < T)
      calc (T : ℝ) = Real.exp L := by rw [hLdef, Real.exp_log hTpos]
        _ = Real.exp (u ^ 5) := by rw [hu5]
        _ ≤ Real.exp ((2 * c₁ / Kc) ^ 5) :=
          Real.exp_le_exp.2 (pow_le_pow_left₀ hu0.le hsmall.le 5)
        _ ≤ C₀ := hC₀2
    have hu2ge : 1 ≤ u ^ 2 := one_le_pow₀ hu1
    have hmid : C₀ ≤ C₀ * u ^ 2 := by nlinarith
    have hA4 : 0 ≤ A * u ^ 4 := by positivity
    linarith
  · push Not at hsmall
    set δ : ℝ := c₁ / u with hδ
    have hδpos : 0 < δ := by rw [hδ]; positivity
    have hδK : δ ≤ Kc / 2 := by
      rw [hδ, div_le_iff₀ hu0]
      rw [div_le_iff₀ hKcpos] at hsmall
      linarith
    have hshift : (m - (m - m / (4 * u))) / (1 - m) = δ / 2 := by
      rw [hδ, hc₁]; field_simp; ring
    have hB2 : 0 < 4 * B ^ 2 := by positivity
    have htail := sum_tail_bound Kc δ (4 * B ^ 2) f hKcpos hδpos (by linarith) hB2 hfpos N q hq0
      hq1 (by
        intro n hn
        have hnpos : (0:ℝ) < n := by
          by_contra h
          push Not at h
          nlinarith
        have hn1 : 1 ≤ n := by exact_mod_cast (show 0 < n by exact_mod_cast hnpos)
        have hfn : f + n * ((m - (m - m / (4 * u))) / (1 - m)) ≤ (n : ℝ) * (Kc - δ / 2) := by
          rw [hshift]; nlinarith
        have := nb_term' P X μ hX a S hS hS01 m (m - m / (4 * u)) l B Kc (δ / 2) f hm1
          (by have : 0 ≤ m / (4 * u) := by positivity
              linarith) hl0 hl1 hw hB hBS hKc hfpos.le (by positivity) n hn1 hfn
        simp only [hq]
        convert this using 2
        ring)
    have hpart1 : f * δ / (Kc * (Kc - δ)) ≤ A * u ^ 4 := by
      have hKd : Kc / 2 ≤ Kc - δ := by linarith
      have h1 : f * δ / (Kc * (Kc - δ)) ≤ (2 * L) * δ / (Kc * (Kc / 2)) := by
        apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hf2L hδpos.le)
          (by positivity) (mul_le_mul_of_nonneg_left hKd hKcpos.le)
      refine h1.trans (le_of_eq ?_)
      rw [hδ, ← hu5, hA, hc₁]
      field_simp
    have hpart2 : 2 * (4 * B ^ 2) / δ ^ 2 ≤ C₀ * u ^ 2 := by
      have : 2 * (4 * B ^ 2) / δ ^ 2 = (8 * B ^ 2 / c₁ ^ 2) * u ^ 2 := by
        rw [hδ]; field_simp; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hC₀1 (by positivity)
    linarith

/-- The shifted tail-sum bound for the suboptimal arm, for given `ν` and `m`, with constant `M₀`. -/
def NBBound' (ν : Measure ℝ) (m M₀ : ℝ) : Prop :=
  ∀ {K : ℕ} (_hK : 2 ≤ K) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (_hX : IsStochasticBandit P X μ)
    (_hbdd : ∀ a k ω, X a k ω ∈ Set.Icc (0 : ℝ) 1) (a : Fin K)
    (_hν : P.map (X a 0) = ν) (_hm : bestMean μ = m) (T : ℕ) (_hT : 3 ≤ T),
    ∑ n ∈ Finset.Icc (⌈f₂ T / (Kinf ν m).toReal⌉₊ + 1) (T - K),
      P.real {ω | InC (m - m / (4 * Real.log T ^ ((1:ℝ) / 5))) (f₂ T / (n : ℝ))
        (empMeasure (fun k => X a k ω) n)} ≤
    2 * m / ((1 - m) * (Kinf ν m).toReal ^ 2) * Real.log T ^ ((4 : ℝ) / 5)
      + M₀ * Real.log T ^ ((2 : ℝ) / 5)
      + 2 * m / ((1 - m) * (Kinf ν m).toReal ^ 2) + 1

lemma nb_exists' (ν : Measure ℝ) (m : ℝ) (hfs : IsFinSupp01 ν) (hm0 : 0 < m) (hm1 : m < 1)
    (hlt : mean ν < m) : ∃ M₀ : ℝ, 0 < M₀ ∧ NBBound' ν m M₀ := by
  classical
  haveI : IsProbabilityMeasure ν := hfs.1
  obtain ⟨S, hS01', hS, hSpos⟩ := exists_pos_support ν hfs
  have hS01 : ∀ y ∈ S, y ∈ Set.Icc (0:ℝ) 1 := fun y hy => hS01' (by exact_mod_cast hy)
  obtain ⟨l, hl0, hl1, hwp, hfin, hKpos, hKval⟩ :=
    kinf_dual_value ν S hS hS01 m hm0.le hm1 (by simpa [mean] using hlt)
  have hw : ∀ y ∈ S, 0 < 1 - l * (y - m) := fun y hy => hwp y hy (hSpos y hy)
  set B : ℝ := 1 + ∑ y ∈ S, |Real.log (1 - l * (y - m))| with hB
  have hBpos : 0 < B := by
    rw [hB]; have := Finset.sum_nonneg (fun y (_ : y ∈ S) => abs_nonneg (Real.log (1 - l * (y - m))))
    linarith
  have hBS : ∀ y ∈ S, |Real.log (1 - l * (y - m))| ≤ B := by
    intro y hy
    have := Finset.single_le_sum (f := fun y => |Real.log (1 - l * (y - m))|)
      (fun y _ => abs_nonneg _) hy
    rw [hB]; linarith
  set Kc : ℝ := (Kinf ν m).toReal with hKc
  set C₀ : ℝ := max (8 * B ^ 2 / (m / (1 - m) / 2) ^ 2)
      (Real.exp ((2 * (m / (1 - m) / 2) / Kc) ^ 5)) with hC₀
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)
  refine ⟨C₀, hC₀pos, ?_⟩
  intro K hK Ω _ P _ X μ hX hbdd a hν hm T hT
  subst hν
  subst hm
  have hcore := nb_final_core' P X μ hX a S hS hS01 (bestMean μ) l B Kc hm0 hm1 hl0 hl1 hw hBpos
    hBS hKval.symm hKpos C₀ hC₀ T (T - K) hT (Nat.sub_le T K)
  unfold f₂
  exact hcore

lemma sa_arith (m u : ℝ) (hm0 : 0 < m) (hm1 : m ≤ 1) (hu1 : 1 ≤ u) :
    1 + (1 + 1 / (2 * (m / (4 * u)) ^ 2))
        + Real.exp 1 * (1 + 1 / (m / (4 * u))) * (1 + 1 / (4 * (m / (4 * u)) ^ 2))
      ≤ 1 + 72 / m ^ 4 * u ^ 4 + 40 / m ^ 2 * u ^ 2 := by
  have hu0 : 0 < u := by linarith
  obtain ⟨v, hv⟩ : ∃ v, v = u / m := ⟨_, rfl⟩
  have hv1 : 1 ≤ v := by rw [hv, le_div_iff₀ hm0]; linarith
  have e1 : 1 / (2 * (m / (4 * u)) ^ 2) = 8 * v ^ 2 := by rw [hv]; field_simp <;> ring
  have e2 : 1 / (m / (4 * u)) = 4 * v := by rw [hv]; field_simp
  have e3 : 1 / (4 * (m / (4 * u)) ^ 2) = 4 * v ^ 2 := by rw [hv]; field_simp <;> ring
  have e4 : 72 / m ^ 4 * u ^ 4 = 72 * v ^ 4 := by rw [hv]; field_simp
  have e5 : 40 / m ^ 2 * u ^ 2 = 40 * v ^ 2 := by rw [hv]; field_simp
  rw [e1, e2, e3, e4, e5]
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpos : 0 ≤ (1 + 4 * v) * (1 + 4 * v ^ 2) := by positivity
  have h1 : Real.exp 1 * (1 + 4 * v) * (1 + 4 * v ^ 2) ≤ 2.72 * ((1 + 4 * v) * (1 + 4 * v ^ 2)) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (by linarith) hpos
  have hv2 : v ≤ v ^ 2 := by nlinarith
  have hv3 : v ^ 2 ≤ v ^ 3 := by nlinarith
  have hv4 : v ^ 3 ≤ v ^ 4 := by nlinarith
  nlinarith


lemma empMeasure_atom_pos (x : ℕ → ℝ) {n : ℕ} (i : ℕ) (hi : i < n) :
    0 < empMeasure x n {x i} := by
  unfold empMeasure
  rw [Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n)) ?_
  refine ne_of_gt (lt_of_lt_of_le ?_ (Finset.single_le_sum
    (f := fun k => Measure.dirac (x k) {x i}) (fun _ _ => zero_le) (Finset.mem_range.2 hi)))
  simp

lemma elUpper_bdd (S : Finset ℝ) (hS : ∀ y ∈ S, y ≤ 1) (νh : Measure ℝ) (ε : ℝ) :
    BddAbove {m : ℝ | ∃ ν' : Measure ℝ, IsProbabilityMeasure ν' ∧
      ν' (↑(insert 1 S) : Set ℝ)ᶜ = 0 ∧
      InformationTheory.klDiv νh ν' ≤ ENNReal.ofReal ε ∧ m = mean ν'} := by
  refine ⟨1, ?_⟩
  rintro m ⟨ν', hP, hsupp, -, rfl⟩
  unfold mean
  rw [integral_finsupp ν' _ hsupp]
  have h1 := integral_finsupp ν' _ hsupp (fun _ => (1:ℝ))
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at h1
  calc ∑ x ∈ insert 1 S, (ν' {x}).toReal * x ≤ ∑ x ∈ insert 1 S, (ν' {x}).toReal := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hx1 : x ≤ 1 := by
          rcases Finset.mem_insert.1 hx with rfl | h
          · exact le_rfl
          · exact hS x h
        have := ENNReal.toReal_nonneg (a := ν' {x})
        nlinarith
    _ = 1 := by linarith

/-- Deterministic step: an index below `c` yields a dual point with dual value at least `ε`. -/
lemma sa_dual_of_le_index (x : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    (hx : ∀ k, x k ∈ Set.Icc (0 : ℝ) 1) (c ε : ℝ) (hc1 : c < 1) (hε : 0 < ε)
    (h : elUpper (empSupp x n) (empMeasure x n) ε ≤ c) :
    ∃ l : ℝ, 0 ≤ l ∧ l * (1 - c) ≤ 1 ∧ (∀ i, i < n → 0 < 1 - l * (x i - c)) ∧
      (n : ℝ) * ε ≤ ∑ i ∈ Finset.range n, Real.log (1 - l * (x i - c)) := by
  classical
  haveI := empMeasure_isProb x hn
  have hS : empMeasure x n (↑(empSupp x n) : Set ℝ)ᶜ = 0 :=
    empMeasure_compl x n (empSupp x n) subset_rfl
  have hS01 : ∀ y ∈ empSupp x n, y ∈ Set.Icc (0:ℝ) 1 := by
    intro y hy; obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hy; exact hx k
  have hxS : ∀ i, i < n → x i ∈ empSupp x n := fun i hi =>
    Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩
  have hbdd := elUpper_bdd (empSupp x n) (fun y hy => (hS01 y hy).2) (empMeasure x n) ε
  have hval : ∀ l : ℝ, 0 ≤ l → l * (1 - c) ≤ 1 →
      (∀ y ∈ empSupp x n, 0 < empMeasure x n {y} → 0 < 1 - l * (y - c)) →
      ∑ y ∈ empSupp x n, (empMeasure x n {y}).toReal / (1 - l * (y - c)) ≤ 1 →
      0 ≤ ∑ y ∈ empSupp x n, (empMeasure x n {y}).toReal * (y - c) / (1 - l * (y - c)) +
        (1 - ∑ y ∈ empSupp x n, (empMeasure x n {y}).toReal / (1 - l * (y - c))) * (1 - c) →
      ε ≤ ∫ y, Real.log (1 - l * (y - c)) ∂(empMeasure x n) := by
    intro l hl0 hl1 hwp hZ hΦ
    by_contra hlt
    push Not at hlt
    obtain ⟨ν', hP, hsupp, hmean, hkl⟩ := dual_point_witness (empMeasure x n) (empSupp x n) hS
      hS01 c hc1 l hl0 hl1 hwp hZ hΦ
      (Real.toNNReal (ε - ∫ y, Real.log (1 - l * (y - c)) ∂(empMeasure x n)))
      (Real.toNNReal_pos.2 (by linarith))
    have hHe : (∫ y, Real.log (1 - l * (y - c)) ∂(empMeasure x n)) +
        ((Real.toNNReal (ε - ∫ y, Real.log (1 - l * (y - c)) ∂(empMeasure x n)) : ℝ≥0) : ℝ) = ε := by
      rw [Real.coe_toNNReal _ (by linarith)]; ring
    rw [hHe] at hkl
    have hmem : mean ν' ∈ {m : ℝ | ∃ ν' : Measure ℝ, IsProbabilityMeasure ν' ∧
        ν' (↑(insert 1 (empSupp x n)) : Set ℝ)ᶜ = 0 ∧
        InformationTheory.klDiv (empMeasure x n) ν' ≤ ENNReal.ofReal ε ∧ m = mean ν'} :=
      ⟨ν', hP, hsupp, hkl, rfl⟩
    have h1 := le_csSup hbdd hmem
    have h2 : elUpper (empSupp x n) (empMeasure x n) ε ≤ c := h
    unfold elUpper at h2
    linarith
  have hp1 : ∑ y ∈ empSupp x n, (empMeasure x n {y}).toReal = 1 := by
    have := integral_finsupp (empMeasure x n) (empSupp x n) hS (fun _ => (1:ℝ))
    simpa using this.symm
  by_cases hlt : (∫ y, y ∂(empMeasure x n)) < c
  · obtain ⟨l, hl0, hl1, hwp, hZ, hΦ⟩ :=
      strong_dual_wit (empMeasure x n) (empSupp x n) hS hS01 c hc1 hlt
    have hH := hval l hl0 hl1 hwp hZ hΦ
    refine ⟨l, hl0, hl1, fun i hi => hwp (x i) (hxS i hi) (empMeasure_atom_pos x i hi), ?_⟩
    rw [integral_empMeasure x hn] at hH
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    rw [one_div, le_inv_mul_iff₀ hnpos] at hH
    exact hH
  · exfalso
    push Not at hlt
    have hm := integral_finsupp (empMeasure x n) (empSupp x n) hS (fun y => y)
    have hH := hval 0 le_rfl (by simp) (fun y _ _ => by simp) (by simp [hp1]) (by
      simp only [zero_mul, sub_zero, div_one]
      have : ∑ y ∈ empSupp x n, (empMeasure x n {y}).toReal * (y - c) =
          (∫ y, y ∂(empMeasure x n)) - c := by
        rw [hm]
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1]
        ring
      rw [this, hp1]; linarith)
    simp at hH
    linarith


/-! ## Optimal-arm tail at a shifted level (new route for N_A) -/

lemma sa_factor_nonneg {x c l : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1) (hl0 : 0 ≤ l)
    (hl1 : l * (1 - c) ≤ 1) : 0 ≤ 1 - l * (x - c) := by
  have : l * (x - c) ≤ l * (1 - c) := mul_le_mul_of_nonneg_left (by linarith [hx.2]) hl0
  linarith

lemma sa_one_add_pow_le (n : ℕ) (hn : 1 ≤ n) : (1 + 1 / (n:ℝ)) ^ n ≤ Real.exp 1 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have h1 : 1 + 1 / (n:ℝ) ≤ Real.exp (1 / n) := by
    have := Real.add_one_le_exp (1 / (n:ℝ)); linarith
  calc (1 + 1 / (n:ℝ)) ^ n ≤ Real.exp (1 / n) ^ n := pow_le_pow_left₀ (by positivity) h1 n
    _ = Real.exp 1 := by rw [← Real.exp_nat_mul]; congr 1; field_simp

lemma sa_grid_le (n : ℕ) (hn : 1 ≤ n) (c l0 : ℝ) (hc1 : c < 1) (hl1 : l0 * (1 - c) ≤ 1)
    (j : ℕ) (hj : j ∈ Finset.range (⌊(1 / (1 - c) - l0) * n⌋₊ + 1)) :
    (l0 + j / n) * (1 - c) ≤ 1 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have h1c : 0 < 1 - c := by linarith
  have hgap : 0 ≤ 1 / (1 - c) - l0 := by
    rw [sub_nonneg, le_div_iff₀ h1c]; exact hl1
  have hjJ : (j:ℝ) ≤ (1 / (1 - c) - l0) * n := by
    have : j ≤ ⌊(1 / (1 - c) - l0) * n⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    calc (j:ℝ) ≤ (⌊(1 / (1 - c) - l0) * n⌋₊ : ℝ) := by exact_mod_cast this
      _ ≤ _ := Nat.floor_le (by positivity)
  have h2 : (j:ℝ) / n ≤ 1 / (1 - c) - l0 := by rw [div_le_iff₀ hnpos]; exact hjJ
  have h3 : l0 + j / n ≤ 1 / (1 - c) := by linarith
  calc (l0 + j / n) * (1 - c) ≤ 1 / (1 - c) * (1 - c) := mul_le_mul_of_nonneg_right h3 h1c.le
    _ = 1 := by field_simp

/-- Covering the dual parameter by a grid of mesh `1/n` above `l0`, and a linear bound below. -/
lemma sa_grid_bound (x : ℕ → ℝ) (hx : ∀ k, x k ∈ Set.Icc (0:ℝ) 1) (n : ℕ) (hn : 1 ≤ n)
    (c l0 : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (hl00 : 0 ≤ l0) (hl01 : l0 * (1 - c) ≤ 1)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l * (1 - c) ≤ 1) (t : ℝ) (ht : 1 < t)
    (htl : t ≤ ∏ i ∈ Finset.range n, (1 - l * (x i - c))) :
    t ≤ Real.exp (l0 * ∑ i ∈ Finset.range n, (c - x i)) + Real.exp 1 *
      ∑ j ∈ Finset.range (⌊(1 / (1 - c) - l0) * n⌋₊ + 1),
        ∏ i ∈ Finset.range n, (1 - (l0 + j / n) * (x i - c)) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have h1c : 0 < 1 - c := by linarith
  have hgrid : ∀ j ∈ Finset.range (⌊(1 / (1 - c) - l0) * n⌋₊ + 1),
      0 ≤ ∏ i ∈ Finset.range n, (1 - (l0 + j / n) * (x i - c)) := by
    intro j hj
    exact Finset.prod_nonneg fun i _ =>
      sa_factor_nonneg (hx i) (by positivity) (sa_grid_le n hn c l0 hc1 hl01 j hj)
  have hsum0 := Finset.sum_nonneg hgrid
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hes := mul_nonneg he0.le hsum0
  rcases lt_or_ge l l0 with hlt | hge
  · have hprod : ∏ i ∈ Finset.range n, (1 - l * (x i - c)) ≤
        Real.exp (l * ∑ i ∈ Finset.range n, (c - x i)) := by
      rw [Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_le_prod (fun i _ => sa_factor_nonneg (hx i) hl0 hl1) (fun i _ => ?_)
      have := Real.add_one_le_exp (l * (c - x i)); linarith
    have hs0 : 0 ≤ ∑ i ∈ Finset.range n, (c - x i) := by
      by_contra hneg
      push Not at hneg
      have h1 : l * ∑ i ∈ Finset.range n, (c - x i) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hl0 hneg.le
      have h2 : Real.exp (l * ∑ i ∈ Finset.range n, (c - x i)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; exact h1
      linarith
    have h3 : Real.exp (l * ∑ i ∈ Finset.range n, (c - x i)) ≤
        Real.exp (l0 * ∑ i ∈ Finset.range n, (c - x i)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hlt.le hs0)
    linarith
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, j = ⌊(l - l0) * n⌋₊ := ⟨_, rfl⟩
    have hd0 : 0 ≤ (l - l0) * n := mul_nonneg (by linarith) hnpos.le
    have hjle : (j:ℝ) ≤ (l - l0) * n := by rw [hj]; exact Nat.floor_le hd0
    have hjgt : (l - l0) * n < j + 1 := by rw [hj]; exact Nat.lt_floor_add_one _
    have hlc : l ≤ 1 / (1 - c) := by rw [le_div_iff₀ h1c]; exact hl1
    have hjJ : j ≤ ⌊(1 / (1 - c) - l0) * n⌋₊ := by
      rw [hj]
      apply Nat.floor_le_floor
      exact mul_le_mul_of_nonneg_right (by linarith) hnpos.le
    have hmem : j ∈ Finset.range (⌊(1 / (1 - c) - l0) * n⌋₊ + 1) :=
      Finset.mem_range.2 (Nat.lt_succ_of_le hjJ)
    have hlj_le : l0 + j / n ≤ l := by
      have : (j:ℝ) / n ≤ l - l0 := by rw [div_le_iff₀ hnpos]; exact hjle
      linarith
    have hlj_gt : l - (l0 + j / n) ≤ 1 / n := by
      have h1 : l - l0 ≤ (j + 1) / n := by rw [le_div_iff₀ hnpos]; linarith
      rw [add_div] at h1
      linarith
    have hlj0 : 0 ≤ l0 + j / n := by positivity
    have hlj1 : (l0 + j / n) * (1 - c) ≤ 1 := sa_grid_le n hn c l0 hc1 hl01 j hmem
    have hw : 0 < 1 / (n:ℝ) := by positivity
    have hfac : ∀ i ∈ Finset.range n,
        1 - l * (x i - c) ≤ (1 - (l0 + j / n) * (x i - c)) * (1 + 1 / n) := by
      intro i _
      have hxi := hx i
      have hA := sa_factor_nonneg hxi hlj0 hlj1
      have hy1 : 0 ≤ x i - c + 1 := by linarith [hxi.1]
      rcases le_or_gt 0 (x i - c) with hy | hy
      · nlinarith [mul_nonneg (sub_nonneg.2 hlj_le) hy, mul_nonneg hw.le hA]
      · nlinarith [mul_le_mul_of_nonpos_right hlj_gt hy.le,
          mul_nonneg hw.le (mul_nonneg hlj0 (neg_nonneg.2 hy.le)), mul_nonneg hw.le hy1]
    have hprod : ∏ i ∈ Finset.range n, (1 - l * (x i - c)) ≤
        (∏ i ∈ Finset.range n, (1 - (l0 + j / n) * (x i - c))) * (1 + 1 / n) ^ n := by
      calc _ ≤ ∏ i ∈ Finset.range n, ((1 - (l0 + j / n) * (x i - c)) * (1 + 1 / n)) :=
            Finset.prod_le_prod (fun i _ => sa_factor_nonneg (hx i) hl0 hl1) hfac
        _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    have hP0 : 0 ≤ ∏ i ∈ Finset.range n, (1 - (l0 + j / n) * (x i - c)) :=
      Finset.prod_nonneg fun i _ => sa_factor_nonneg (hx i) hlj0 hlj1
    have hpow := sa_one_add_pow_le n hn
    have hsingle : ∏ i ∈ Finset.range n, (1 - (l0 + j / n) * (x i - c)) ≤
        ∑ j ∈ Finset.range (⌊(1 / (1 - c) - l0) * n⌋₊ + 1),
          ∏ i ∈ Finset.range n, (1 - (l0 + j / n) * (x i - c)) :=
      Finset.single_le_sum (f := fun j : ℕ => ∏ i ∈ Finset.range n,
        (1 - (l0 + (j:ℝ) / n) * (x i - c))) hgrid hmem
    have hexp0 : 0 < Real.exp (l0 * ∑ i ∈ Finset.range n, (c - x i)) := Real.exp_pos _
    nlinarith [mul_le_mul_of_nonneg_left hpow hP0, mul_le_mul_of_nonneg_left hsingle he0.le]

lemma sa_count_le (b : ℝ) (hb : 0 ≤ b) (T : ℕ) :
    ∑ t ∈ Finset.Ico 3 T, (if (t:ℝ) ≤ b then (1:ℝ) else 0) ≤ b := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsub : (Finset.Ico 3 T).filter (fun t : ℕ => (t:ℝ) ≤ b) ⊆ Finset.Icc 1 ⌊b⌋₊ := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_Ico] at ht
    rw [Finset.mem_Icc]
    exact ⟨by omega, Nat.le_floor ht.2⟩
  calc (((Finset.Ico 3 T).filter (fun t : ℕ => (t:ℝ) ≤ b)).card : ℝ)
      ≤ ((Finset.Icc 1 ⌊b⌋₊).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ = (⌊b⌋₊ : ℝ) := by simp
    _ ≤ b := Nat.floor_le hb

lemma sa_sum_prob_le_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : Ω → ℝ) (hBm : Measurable B) (hBi : Integrable B P)
    (hB0 : ∀ ω, 0 ≤ B ω) (T : ℕ) :
    ∑ t ∈ Finset.Ico 3 T, P.real {ω | (t:ℝ) ≤ B ω} ≤ ∫ ω, B ω ∂P := by
  have hms : ∀ t : ℕ, MeasurableSet {ω | (t:ℝ) ≤ B ω} := fun t =>
    measurableSet_le measurable_const hBm
  have hint : ∀ t : ℕ, Integrable ({ω | (t:ℝ) ≤ B ω}.indicator (1 : Ω → ℝ)) P := fun t =>
    (integrable_const (1:ℝ)).indicator (hms t)
  have h1 : ∀ t : ℕ, P.real {ω | (t:ℝ) ≤ B ω} =
      ∫ ω, ({ω | (t:ℝ) ≤ B ω}.indicator (1 : Ω → ℝ)) ω ∂P :=
    fun t => (integral_indicator_one (hms t)).symm
  rw [Finset.sum_congr rfl (fun t _ => h1 t), ← integral_finsetSum _ (fun t _ => hint t)]
  refine integral_mono (integrable_finsetSum _ (fun t _ => hint t)) hBi ?_
  intro ω
  refine le_trans (le_of_eq ?_) (sa_count_le (B ω) (hB0 ω) T)
  dsimp only
  refine Finset.sum_congr rfl (fun t _ => ?_)
  simp [Set.indicator_apply]

lemma sa_indep_arm {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Fin K → ℕ → Ω → ℝ} {μ : Fin K → ℝ} (hX : IsStochasticBandit P X μ) (a : Fin K) :
    iIndepFun (fun k => X a k) P :=
  hX.indep.precomp (g := fun k : ℕ => ((a, k) : Fin K × ℕ)) (fun k k' h => by simpa using h)

lemma sa_mean_arm {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Fin K → ℕ → Ω → ℝ} {μ : Fin K → ℝ} (hX : IsStochasticBandit P X μ) (a : Fin K)
    (k : ℕ) : ∫ ω, X a k ω ∂P = μ a := by
  rw [(hX.identDistrib a k).integral_eq]; exact hX.mean a

lemma sa_int_arm {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Fin K → ℕ → Ω → ℝ} {μ : Fin K → ℝ} (hX : IsStochasticBandit P X μ) (a : Fin K)
    (k : ℕ) : Integrable (X a k) P :=
  (hX.identDistrib a k).integrable_iff.2 (hX.integrable a)

lemma sa_expect_prod {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ) (a : Fin K) (c l : ℝ) (n : ℕ) :
    ∫ ω, ∏ i ∈ Finset.range n, (1 - l * (X a i ω - c)) ∂P = (1 - l * (μ a - c)) ^ n := by
  have hind : iIndepFun (fun (i : Fin n) (ω : Ω) => 1 - l * (X a i ω - c)) P := by
    have h1 : iIndepFun (fun i : Fin n => X a (i : ℕ)) P :=
      (sa_indep_arm hX a).precomp (g := fun i : Fin n => (i : ℕ)) Fin.val_injective
    exact h1.comp (fun _ x => 1 - l * (x - c)) (fun _ => by fun_prop)
  have hm : ∀ i : Fin n, AEStronglyMeasurable (fun ω => 1 - l * (X a i ω - c)) P := fun i =>
    ((by fun_prop : Measurable fun x : ℝ => 1 - l * (x - c)).comp
      (hX.measurable a i)).aestronglyMeasurable
  have hrw : (fun ω => ∏ i ∈ Finset.range n, (1 - l * (X a i ω - c))) =
      fun ω => ∏ i : Fin n, (1 - l * (X a i ω - c)) := by
    funext ω; exact (Fin.prod_univ_eq_prod_range (fun i => 1 - l * (X a i ω - c)) n).symm
  rw [hrw, hind.integral_fun_prod_eq_prod_integral hm]
  have hE : ∀ i : Fin n, ∫ ω, (1 - l * (X a i ω - c)) ∂P = 1 - l * (μ a - c) := by
    intro i
    have hi := sa_int_arm hX a i
    have h2 : (fun ω => 1 - l * (X a i ω - c)) = fun ω => (1 + l * c) - l * X a i ω := by
      funext ω; ring
    rw [h2, integral_sub (integrable_const _) (hi.const_mul l), integral_const_mul,
      sa_mean_arm hX a i]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  rw [Finset.prod_congr rfl (fun i _ => hE i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

lemma sa_expect_exp {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ) (hbdd : ∀ a k ω, X a k ω ∈ Set.Icc (0 : ℝ) 1)
    (a : Fin K) (c s : ℝ) (n : ℕ) :
    ∫ ω, Real.exp (s * ∑ i ∈ Finset.range n, (c - X a i ω)) ∂P ≤
      Real.exp (-(n:ℝ) * s * (μ a - c) + n * s ^ 2 / 8) := by
  set Z : ℕ → Ω → ℝ := fun k ω => μ a - X a k ω with hZ
  have hZind : iIndepFun Z P :=
    (sa_indep_arm hX a).comp (fun _ x => μ a - x) (fun _ => by fun_prop)
  set cB : ℝ≥0 := Real.toNNReal (1 / 4) with hcB
  have hcBr : (cB : ℝ) = 1 / 4 := Real.coe_toNNReal _ (by norm_num)
  have hsub : ∀ k, HasSubgaussianMGF (Z k) cB P := by
    intro k
    have h := hasSubgaussianMGF_of_mem_Icc (μ := P) (X := Z k) (a := μ a - 1) (b := μ a)
      ((hX.measurable a k).const_sub _).aemeasurable
      (ae_of_all _ fun ω => by
        simp only [hZ, Set.mem_Icc]
        constructor <;> linarith [(hbdd a k ω).1, (hbdd a k ω).2])
    have hm : P[Z k] = 0 := by
      simp only [hZ]
      rw [integral_sub (integrable_const _) (sa_int_arm hX a k), sa_mean_arm hX a k]
      simp
    have hpar : ((‖(μ a) - (μ a - 1)‖₊ / 2) ^ 2 : ℝ≥0) = cB := by
      apply NNReal.eq
      rw [hcBr]
      simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat]
      rw [show (μ a) - (μ a - 1) = 1 by ring]
      norm_num
    rw [← hpar]
    simpa [hm] using h
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hZind (s := Finset.range n)
    (c := fun _ => cB) (fun i _ => hsub i)
  have hmgf := hsum.mgf_le s
  have hpar2 : ((∑ i ∈ Finset.range n, cB : ℝ≥0) : ℝ) = n / 4 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    rw [hcBr]; ring
  rw [hpar2] at hmgf
  have hpt : ∀ ω, Real.exp (s * ∑ i ∈ Finset.range n, (c - X a i ω)) =
      Real.exp (-(n:ℝ) * s * (μ a - c)) * Real.exp (s * ∑ i ∈ Finset.range n, Z i ω) := by
    intro ω
    rw [← Real.exp_add]
    congr 1
    simp only [hZ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul]
  unfold mgf at hmgf
  calc Real.exp (-(n:ℝ) * s * (μ a - c)) * ∫ ω, Real.exp (s * ∑ i ∈ Finset.range n, Z i ω) ∂P
      ≤ Real.exp (-(n:ℝ) * s * (μ a - c)) * Real.exp (n / 4 * s ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The dominating variable for the optimal-arm tail. -/
noncomputable def saB {Ω : Type*} {K : ℕ} (X : Fin K → ℕ → Ω → ℝ) (a : Fin K) (c d : ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (4 * d * ∑ i ∈ Finset.range n, (c - X a i ω)) + Real.exp 1 *
    ∑ j ∈ Finset.range (⌊(1 / (1 - c) - 4 * d) * n⌋₊ + 1),
      ∏ i ∈ Finset.range n, (1 - (4 * d + j / n) * (X a i ω - c))

lemma sa_B_facts {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ) (hbdd : ∀ a k ω, X a k ω ∈ Set.Icc (0 : ℝ) 1)
    (a : Fin K) (c d : ℝ) (hd : 0 < d) (hc0 : 0 ≤ c) (hc1 : c < 1) (hcd : μ a = c + d)
    (hd4 : 4 * d * (1 - c) ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    Measurable (saB X a c d n) ∧ Integrable (saB X a c d n) P ∧ (∀ ω, 0 ≤ saB X a c d n ω) ∧
      ∫ ω, saB X a c d n ω ∂P ≤ Real.exp (-(n:ℝ) * (2 * d ^ 2))
        + Real.exp 1 * (1 + 1 / d) * Real.exp (-(n:ℝ) * (4 * d ^ 2)) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  set J := ⌊(1 / (1 - c) - 4 * d) * n⌋₊ with hJ
  have hXm : ∀ i, Measurable (X a i) := fun i => hX.measurable a i
  have hexpM : Measurable (fun ω => Real.exp (4 * d * ∑ i ∈ Finset.range n, (c - X a i ω))) :=
    Real.measurable_exp.comp ((Finset.measurable_sum _ fun i _ =>
      measurable_const.sub (hXm i)).const_mul _)
  have hprodM : ∀ j : ℕ, Measurable (fun ω => ∏ i ∈ Finset.range n,
      (1 - (4 * d + j / n) * (X a i ω - c))) := fun j =>
    Finset.measurable_prod _ fun i _ =>
      measurable_const.sub (((hXm i).sub measurable_const).const_mul _)
  have hexpB : ∀ ω, ‖Real.exp (4 * d * ∑ i ∈ Finset.range n, (c - X a i ω))‖ ≤
      Real.exp (4 * d * n) := by
    intro ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    have : ∑ i ∈ Finset.range n, (c - X a i ω) ≤ ∑ i ∈ Finset.range n, (1:ℝ) :=
      Finset.sum_le_sum fun i _ => by linarith [(hbdd a i ω).1]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
    nlinarith
  have hexpI : Integrable (fun ω => Real.exp (4 * d * ∑ i ∈ Finset.range n, (c - X a i ω))) P :=
    Integrable.of_bound hexpM.aestronglyMeasurable _ (ae_of_all _ hexpB)
  have hgl : ∀ j ∈ Finset.range (J + 1), (4 * d + j / n) * (1 - c) ≤ 1 := fun j hj =>
    sa_grid_le n hn c (4 * d) hc1 hd4 j hj
  have hprodI : ∀ j ∈ Finset.range (J + 1), Integrable (fun ω => ∏ i ∈ Finset.range n,
      (1 - (4 * d + j / n) * (X a i ω - c))) P := by
    intro j hj
    refine Integrable.of_bound (hprodM j).aestronglyMeasurable ((1 + (4 * d + j / n)) ^ n)
      (ae_of_all _ fun ω => ?_)
    have hl0 : 0 ≤ 4 * d + j / n := by positivity
    have h0 : ∀ i ∈ Finset.range n, 0 ≤ 1 - (4 * d + j / n) * (X a i ω - c) := fun i _ =>
      sa_factor_nonneg (hbdd a i ω) hl0 (hgl j hj)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg h0)]
    calc ∏ i ∈ Finset.range n, (1 - (4 * d + j / n) * (X a i ω - c))
        ≤ ∏ i ∈ Finset.range n, (1 + (4 * d + j / n)) := by
          refine Finset.prod_le_prod h0 fun i _ => ?_
          have hx := hbdd a i ω
          have : (4 * d + j / n) * (c - X a i ω) ≤ (4 * d + j / n) * 1 :=
            mul_le_mul_of_nonneg_left (by linarith [hx.1]) hl0
          linarith
      _ = _ := by rw [Finset.prod_const, Finset.card_range]
  have hsumI := integrable_finsetSum _ hprodI
  refine ⟨hexpM.add (measurable_const.mul (Finset.measurable_sum _ fun j _ => hprodM j)),
    hexpI.add (hsumI.const_mul _), fun ω => ?_, ?_⟩
  · unfold saB
    have hs : 0 ≤ ∑ j ∈ Finset.range (⌊(1 / (1 - c) - 4 * d) * n⌋₊ + 1),
        ∏ i ∈ Finset.range n, (1 - (4 * d + j / n) * (X a i ω - c)) :=
      Finset.sum_nonneg fun (j : ℕ) hj => Finset.prod_nonneg fun i _ =>
        sa_factor_nonneg (hbdd a i ω) (by positivity) (hgl j hj)
    have := mul_nonneg (Real.exp_pos 1).le hs
    have := Real.exp_pos (4 * d * ∑ i ∈ Finset.range n, (c - X a i ω))
    linarith
  · unfold saB
    rw [integral_add hexpI (hsumI.const_mul _), integral_const_mul, integral_finsetSum _ hprodI]
    have h1 := sa_expect_exp P X μ hX hbdd a c (4 * d) n
    have h1' : ∫ ω, Real.exp (4 * d * ∑ i ∈ Finset.range n, (c - X a i ω)) ∂P ≤
        Real.exp (-(n:ℝ) * (2 * d ^ 2)) := by
      refine h1.trans (le_of_eq ?_)
      congr 1; rw [hcd]; ring
    have h2 : ∀ j ∈ Finset.range (J + 1), ∫ ω, ∏ i ∈ Finset.range n,
        (1 - (4 * d + j / n) * (X a i ω - c)) ∂P ≤
        Real.exp (-(n:ℝ) * (4 * d ^ 2)) * Real.exp (-(j:ℝ) * d) := by
      intro j hj
      rw [sa_expect_prod P X μ hX a c (4 * d + j / n) n]
      have hl0 : 0 ≤ 4 * d + j / n := by positivity
      have hdc : d ≤ 1 - c := by
        have : μ a ≤ 1 := by
          rw [← hX.mean a]
          calc ∫ ω, X a 0 ω ∂P ≤ ∫ _ω, (1:ℝ) ∂P :=
                integral_mono (hX.integrable a) (integrable_const _) fun ω => (hbdd a 0 ω).2
            _ = 1 := by simp
        linarith
      have hx0 : 0 ≤ 1 - (4 * d + j / n) * (μ a - c) := by
        rw [show μ a - c = d by linarith]
        have := hgl j hj
        have : (4 * d + j / n) * d ≤ (4 * d + j / n) * (1 - c) :=
          mul_le_mul_of_nonneg_left hdc hl0
        linarith
      calc (1 - (4 * d + j / n) * (μ a - c)) ^ n
          ≤ Real.exp (-((4 * d + j / n) * (μ a - c))) ^ n := by
            refine pow_le_pow_left₀ hx0 ?_ n
            have := Real.add_one_le_exp (-((4 * d + j / n) * (μ a - c))); linarith
        _ = Real.exp (-(n:ℝ) * (4 * d ^ 2)) * Real.exp (-(j:ℝ) * d) := by
            rw [← Real.exp_nat_mul, ← Real.exp_add]
            congr 1
            rw [show μ a - c = d by linarith]
            field_simp
            ring
    have h3 : ∑ j ∈ Finset.range (J + 1), ∫ ω, ∏ i ∈ Finset.range n,
        (1 - (4 * d + j / n) * (X a i ω - c)) ∂P ≤
        Real.exp (-(n:ℝ) * (4 * d ^ 2)) * (1 + 1 / d) := by
      calc _ ≤ ∑ j ∈ Finset.range (J + 1),
              Real.exp (-(n:ℝ) * (4 * d ^ 2)) * Real.exp (-(j:ℝ) * d) := Finset.sum_le_sum h2
        _ = Real.exp (-(n:ℝ) * (4 * d ^ 2)) * ∑ j ∈ Finset.range (J + 1),
              Real.exp (-(j:ℝ) * d) := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (geom_exp_sum_bound d hd _) (Real.exp_pos _).le
    have h4 := mul_le_mul_of_nonneg_left h3 (Real.exp_pos 1).le
    nlinarith

/-- The optimal-arm tail at the shifted level `c = μ⋆ - d`. -/
theorem sa_tail {K : ℕ} (hK : 2 ≤ K) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ) (hbdd : ∀ a k ω, X a k ω ∈ Set.Icc (0 : ℝ) 1)
    (I : ℕ → Ω → Fin K) (hrun : IsEmpKLUCBRun f₂ X I) (astar : Fin K) (c d : ℝ)
    (hd : 0 < d) (hc0 : 0 ≤ c) (hc1 : c < 1) (hcd : μ astar = c + d) (hd4 : 4 * d ≤ 1)
    (T : ℕ) :
    ∑ t ∈ Finset.Ico K T, P.real {ω | c ≥ index f₂ X I astar t ω} ≤
      1 + (1 + 1 / (2 * d ^ 2)) + Real.exp 1 * (1 + 1 / d) * (1 + 1 / (4 * d ^ 2)) := by
  have hd4' : 4 * d * (1 - c) ≤ 1 := by nlinarith
  have hincl : ∀ t ∈ Finset.Ico K T, 3 ≤ t → {ω | c ≥ index f₂ X I astar t ω} ⊆
      ⋃ n ∈ Finset.Icc 1 T, {ω | (t:ℝ) ≤ saB X astar c d n ω} := by
    intro t ht ht3 ω hω
    have hKt := (Finset.mem_Ico.1 ht).1
    have htT := (Finset.mem_Ico.1 ht).2
    obtain ⟨hn1, hnt⟩ := pullCount_bounds hrun astar t hKt ω
    have hf : 0 < f₂ t := f₂_pos ht3
    have hnpos : (0:ℝ) < pullCount I astar t ω := by exact_mod_cast hn1
    obtain ⟨l, hl0, hl1, hpos, hsum⟩ := sa_dual_of_le_index (fun k => X astar k ω) hn1
      (fun k => hbdd astar k ω) c (f₂ t / pullCount I astar t ω) hc1 (div_pos hf hnpos) hω
    have hnf : (pullCount I astar t ω : ℝ) * (f₂ t / pullCount I astar t ω) = f₂ t := by
      field_simp
    rw [hnf] at hsum
    have ht0 : (0:ℝ) < t := by have : (3:ℝ) ≤ t := by exact_mod_cast ht3
                               linarith
    have ht_le : (t:ℝ) ≤ Real.exp (f₂ t) := by
      have h1 : 1 < Real.log t := one_lt_log_of_three_le ht3
      have h2 : 0 < Real.log (Real.log t) := Real.log_pos h1
      calc (t:ℝ) = Real.exp (Real.log t) := (Real.exp_log ht0).symm
        _ ≤ Real.exp (f₂ t) := Real.exp_le_exp.2 (by unfold f₂; linarith)
    have hprod : Real.exp (∑ i ∈ Finset.range (pullCount I astar t ω),
        Real.log (1 - l * (X astar i ω - c))) =
        ∏ i ∈ Finset.range (pullCount I astar t ω), (1 - l * (X astar i ω - c)) := by
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl (fun i hi => Real.exp_log (hpos i (Finset.mem_range.1 hi)))
    have htl : (t:ℝ) ≤ ∏ i ∈ Finset.range (pullCount I astar t ω), (1 - l * (X astar i ω - c)) := by
      rw [← hprod]
      exact ht_le.trans (Real.exp_le_exp.2 hsum)
    have ht1 : (1:ℝ) < t := by have : (3:ℝ) ≤ t := by exact_mod_cast ht3
                               linarith
    have hB := sa_grid_bound (fun k => X astar k ω) (fun k => hbdd astar k ω)
      (pullCount I astar t ω) hn1 c (4 * d) hc0 hc1 (by positivity) hd4' l hl0 hl1 t ht1 htl
    simp only [Set.mem_iUnion]
    exact ⟨pullCount I astar t ω, Finset.mem_Icc.2 ⟨hn1, by omega⟩, hB⟩
  have hfacts := fun n (hn : n ∈ Finset.Icc 1 T) =>
    sa_B_facts P X μ hX hbdd astar c d hd hc0 hc1 hcd hd4' n (Finset.mem_Icc.1 hn).1
  set q : ℕ → ℝ := fun t => if 3 ≤ t then
    ∑ n ∈ Finset.Icc 1 T, P.real {ω | (t:ℝ) ≤ saB X astar c d n ω} else 1 with hq
  have hstep : ∀ t ∈ Finset.Ico K T, P.real {ω | c ≥ index f₂ X I astar t ω} ≤ q t := by
    intro t ht
    by_cases h3 : 3 ≤ t
    · simp only [hq, if_pos h3]
      exact (measureReal_mono (hincl t ht h3) (measure_ne_top _ _)).trans
        (measureReal_biUnion_finset_le _ _)
    · simp only [hq, if_neg h3]; exact measureReal_le_one
  have hq0 : ∀ t, 0 ≤ q t := by
    intro t; simp only [hq]; split_ifs
    · exact Finset.sum_nonneg fun _ _ => measureReal_nonneg
    · exact zero_le_one
  have hsplit : ∑ t ∈ Finset.Ico 2 T, q t ≤
      1 + ∑ t ∈ Finset.Ico 3 T, ∑ n ∈ Finset.Icc 1 T, P.real {ω | (t:ℝ) ≤ saB X astar c d n ω} := by
    rcases lt_or_ge 2 T with h2T | h2T
    · rw [Finset.sum_eq_sum_Ico_succ_bot h2T]
      have hq2 : q 2 = 1 := by simp [hq]
      rw [hq2]
      gcongr with t ht
      have h3 : 3 ≤ t := (Finset.mem_Ico.1 ht).1
      simp only [hq, if_pos h3]; exact le_rfl
    · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
      have := Finset.sum_nonneg fun t (_ : t ∈ Finset.Ico 3 T) =>
        Finset.sum_nonneg fun n (_ : n ∈ Finset.Icc 1 T) =>
          (measureReal_nonneg : (0:ℝ) ≤ P.real {ω | (t:ℝ) ≤ saB X astar c d n ω})
      linarith
  have hgeo1 := geom_exp_sum_bound (2 * d ^ 2) (by positivity) (Finset.Icc 1 T)
  have hgeo2 := geom_exp_sum_bound (4 * d ^ 2) (by positivity) (Finset.Icc 1 T)
  calc ∑ t ∈ Finset.Ico K T, P.real {ω | c ≥ index f₂ X I astar t ω}
      ≤ ∑ t ∈ Finset.Ico K T, q t := Finset.sum_le_sum hstep
    _ ≤ ∑ t ∈ Finset.Ico 2 T, q t :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left hK)
          (fun _ _ _ => hq0 _)
    _ ≤ 1 + ∑ t ∈ Finset.Ico 3 T, ∑ n ∈ Finset.Icc 1 T,
          P.real {ω | (t:ℝ) ≤ saB X astar c d n ω} := hsplit
    _ = 1 + ∑ n ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Ico 3 T,
          P.real {ω | (t:ℝ) ≤ saB X astar c d n ω} := by rw [Finset.sum_comm]
    _ ≤ 1 + ∑ n ∈ Finset.Icc 1 T, ∫ ω, saB X astar c d n ω ∂P := by
        gcongr with n hn
        obtain ⟨hm, hi, h0, -⟩ := hfacts n hn
        exact sa_sum_prob_le_integral P _ hm hi h0 T
    _ ≤ 1 + ∑ n ∈ Finset.Icc 1 T, (Real.exp (-(n:ℝ) * (2 * d ^ 2))
          + Real.exp 1 * (1 + 1 / d) * Real.exp (-(n:ℝ) * (4 * d ^ 2))) := by
        gcongr with n hn
        exact (hfacts n hn).2.2.2
    _ = 1 + (∑ n ∈ Finset.Icc 1 T, Real.exp (-(n:ℝ) * (2 * d ^ 2)))
          + Real.exp 1 * (1 + 1 / d) * ∑ n ∈ Finset.Icc 1 T, Real.exp (-(n:ℝ) * (4 * d ^ 2)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]; ring
    _ ≤ 1 + (1 + 1 / (2 * d ^ 2)) + Real.exp 1 * (1 + 1 / d) * (1 + 1 / (4 * d ^ 2)) := by
        have he : 0 ≤ Real.exp 1 * (1 + 1 / d) := by positivity
        have := mul_le_mul_of_nonneg_left hgeo2 he
        linarith


end CappeKLUCB.Empirical

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic CappeKLUCB.Empirical in
theorem solution :
    ∃ M : Measure ℝ → ℝ → ℝ, (∀ ν m, 0 < M ν m) ∧
      ∀ {K : ℕ} (_hK : 2 ≤ K)
        {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (_hX : IsStochasticBandit P X μ)
        (_hF : ∀ a, IsFinSupp01 (P.map (X a 0))) (_hbdd : ∀ a k ω, X a k ω ∈ Set.Icc (0 : ℝ) 1)
        (I : ℕ → Ω → Fin K) (_hI : ∀ t, Measurable (I t)) (_hadapt : CappeKLUCB.ExpFam.IsNonanticipating X I)
        (_hrun : IsEmpKLUCBRun f₂ X I)
        (_hpos : ∀ a, 0 < μ a) (_hlt1 : bestMean μ < 1)
        (a : Fin K) (_ha : μ a < bestMean μ) (T : ℕ) (_hT : 3 ≤ T),
        ∫ ω, (pullCount I a T ω : ℝ) ∂P ≤
          Real.log T / (Kinf (P.map (X a 0)) (bestMean μ)).toReal
          + 36 / bestMean μ ^ 4 * Real.log T ^ ((4 : ℝ) / 5) * Real.log (Real.log T)
          + (72 / bestMean μ ^ 4
              + 2 * bestMean μ
                / ((1 - bestMean μ) * (Kinf (P.map (X a 0)) (bestMean μ)).toReal ^ 2))
            * Real.log T ^ ((4 : ℝ) / 5)
          + (1 - bestMean μ) ^ 2 * M (P.map (X a 0)) (bestMean μ) / (2 * bestMean μ ^ 2)
            * Real.log T ^ ((2 : ℝ) / 5)
          + Real.log (Real.log T) / (Kinf (P.map (X a 0)) (bestMean μ)).toReal
          + 2 * bestMean μ
              / ((1 - bestMean μ) * (Kinf (P.map (X a 0)) (bestMean μ)).toReal ^ 2)
          + 4 := by
  classical
  have H : ∀ (ν : Measure ℝ) (m : ℝ), ∃ M₀ : ℝ, 0 < M₀ ∧
      ((IsFinSupp01 ν ∧ 0 < m ∧ m < 1 ∧ mean ν < m) → NBBound' ν m M₀) := by
    intro ν m
    by_cases h : IsFinSupp01 ν ∧ 0 < m ∧ m < 1 ∧ mean ν < m
    · obtain ⟨M₀, hM₀, hB⟩ := nb_exists' ν m h.1 h.2.1 h.2.2.1 h.2.2.2
      exact ⟨M₀, hM₀, fun _ => hB⟩
    · exact ⟨1, one_pos, fun h' => absurd h' h⟩
  choose C hCpos hC using H
  refine ⟨fun ν m => (C ν m + 40 / m ^ 2) * (2 * m ^ 2 / (1 - m) ^ 2) + 1,
    fun ν m => by have := hCpos ν m; positivity, ?_⟩
  intro K hK Ω _ P _ X μ hX hF hbdd I hI hadapt hrun hpos hlt1 a ha T hT
  have : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  obtain ⟨astar, hastar⟩ := exists_eq_ciSup_of_finite (f := μ)
  have hastar' : μ astar = bestMean μ := by rw [hastar]; rfl
  have hm0 : 0 < bestMean μ := hastar' ▸ hpos astar
  have hL1 : 1 < Real.log T := one_lt_log_of_three_le hT
  have hL0 : 0 < Real.log T := by linarith
  have hu1 : 1 ≤ Real.log T ^ ((1:ℝ) / 5) := Real.one_le_rpow hL1.le (by norm_num)
  have hu0 : 0 < Real.log T ^ ((1:ℝ) / 5) := by linarith
  have hd0 : 0 < bestMean μ / (4 * Real.log T ^ ((1:ℝ) / 5)) := by positivity
  have hdle : bestMean μ / (4 * Real.log T ^ ((1:ℝ) / 5)) ≤ bestMean μ / 4 := by
    apply div_le_div_of_nonneg_left hm0.le (by norm_num)
    linarith
  have hd4 : 4 * (bestMean μ / (4 * Real.log T ^ ((1:ℝ) / 5))) ≤ 1 := by linarith
  have hc0 : 0 ≤ bestMean μ - bestMean μ / (4 * Real.log T ^ ((1:ℝ) / 5)) := by linarith
  have hc1 : bestMean μ - bestMean μ / (4 * Real.log T ^ ((1:ℝ) / 5)) < 1 := by linarith
  have h10 := gb10_aux hK P X μ hX hF hbdd I hI hrun a astar hastar' ha
    (bestMean μ - bestMean μ / (4 * Real.log T ^ ((1:ℝ) / 5))) T hT
  have hA := sa_tail hK P X μ hX hbdd I hrun astar
    (bestMean μ - bestMean μ / (4 * Real.log T ^ ((1:ℝ) / 5)))
    (bestMean μ / (4 * Real.log T ^ ((1:ℝ) / 5))) hd0 hc0 hc1 (by rw [hastar']; ring) hd4 T
  have hA2 := sa_arith (bestMean μ) (Real.log T ^ ((1:ℝ) / 5)) hm0 hlt1.le hu1
  have hu4 : (Real.log T ^ ((1:ℝ) / 5)) ^ 4 = Real.log T ^ ((4:ℝ) / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hu2 : (Real.log T ^ ((1:ℝ) / 5)) ^ 2 = Real.log T ^ ((2:ℝ) / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  rw [hu4, hu2] at hA2
  have hmean : mean (P.map (X a 0)) = μ a := by
    unfold mean
    have h := integral_map (μ := P) (φ := X a 0) (f := fun x : ℝ => x)
      (hX.measurable a 0).aemeasurable aestronglyMeasurable_id
    rw [h]
    exact hX.mean a
  have hcond : IsFinSupp01 (P.map (X a 0)) ∧ 0 < bestMean μ ∧ bestMean μ < 1 ∧
      mean (P.map (X a 0)) < bestMean μ :=
    ⟨hF a, hm0, hlt1, by rw [hmean]; exact ha⟩
  have hB := hC _ _ hcond hK P X μ hX hbdd a rfl rfl T hT
  have hdiv : f₂ T / (Kinf (P.map (X a 0)) (bestMean μ)).toReal =
      Real.log T / (Kinf (P.map (X a 0)) (bestMean μ)).toReal
        + Real.log (Real.log T) / (Kinf (P.map (X a 0)) (bestMean μ)).toReal := by
    unfold f₂; rw [add_div]
  have h1m : 0 < 1 - bestMean μ := by linarith
  have hMeq : (1 - bestMean μ) ^ 2 * ((C (P.map (X a 0)) (bestMean μ) + 40 / bestMean μ ^ 2)
      * (2 * bestMean μ ^ 2 / (1 - bestMean μ) ^ 2) + 1) / (2 * bestMean μ ^ 2) =
      (C (P.map (X a 0)) (bestMean μ) + 40 / bestMean μ ^ 2)
        + (1 - bestMean μ) ^ 2 / (2 * bestMean μ ^ 2) := by
    field_simp
  have hMge : C (P.map (X a 0)) (bestMean μ) + 40 / bestMean μ ^ 2 ≤
      (1 - bestMean μ) ^ 2 * ((C (P.map (X a 0)) (bestMean μ) + 40 / bestMean μ ^ 2)
        * (2 * bestMean μ ^ 2 / (1 - bestMean μ) ^ 2) + 1) / (2 * bestMean μ ^ 2) := by
    rw [hMeq]
    have : 0 ≤ (1 - bestMean μ) ^ 2 / (2 * bestMean μ ^ 2) := by positivity
    linarith
  have hL25 : 0 ≤ Real.log T ^ ((2:ℝ) / 5) := by positivity
  have hMterm := mul_le_mul_of_nonneg_right hMge hL25
  have h36 : 0 ≤ 36 / bestMean μ ^ 4 * Real.log T ^ ((4 : ℝ) / 5) * Real.log (Real.log T) := by
    have := Real.log_pos hL1
    positivity
  beta_reduce
  linarith [h10, hA, hA2, hB, hdiv, hMterm, h36]
