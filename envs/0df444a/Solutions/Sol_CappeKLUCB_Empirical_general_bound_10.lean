-- Prove2me | solution 1 for CappeKLUCB.Empirical.general_bound_10
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:38:41.618532+00:00
-- url     : https://prove2.me/submissions/7744786b-060f-44f6-bacb-2686977520a6

import Mathlib
import Definitions.Def_CappeKLUCB_Empirical_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
open scoped ENNReal

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

end CappeKLUCB.Empirical

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic CappeKLUCB.Empirical in
theorem solution {K : ℕ} (hK : 2 ≤ K)
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
  exact CappeKLUCB.Empirical.gb10_aux hK P X μ hX hF hbdd I hI hrun a astar hastar ha μdag T hT
