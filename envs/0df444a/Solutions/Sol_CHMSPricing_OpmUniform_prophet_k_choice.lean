-- Prove2me | solution 1 for CHMSPricing.OpmUniform.prophet_k_choice
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:43:27.7843+00:00
-- url     : https://prove2.me/submissions/79a1f75f-b1b6-45af-91e9-fadde166a6d6

import Mathlib
import Definitions.Def_CHMSPricing_OpmUniform_Prophet



namespace CHMSPricing.OpmUniform

open MeasureTheory ProbabilityTheory Finset

namespace PhAux

variable {n k : ℕ}

noncomputable def tI (hk : k ≤ n) (s : Finset (Fin n)) (i : Fin k) : Fin n :=
  if h : (i : ℕ) < s.card then min ⟨n - k + i, by omega⟩ (s.orderEmbOfFin rfl ⟨i, h⟩)
  else ⟨n - k + i, by omega⟩

lemma sort_get (s : Finset (Fin n)) (i : ℕ) :
    (s.sort (· ≤ ·))[i]? = if h : i < s.card then some (s.orderEmbOfFin rfl ⟨i, h⟩) else none := by
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h), orderEmbOfFin_apply]; rfl
  · rw [List.getElem?_eq_none (by simpa using h)]

lemma threshIdx_eq (hk : k ≤ n) (x : Fin n → ℝ) (c : ℝ) (i : Fin k) :
    threshIdx hk x c i = tI hk (univ.filter (fun j => c ≤ x j)) i := by
  unfold threshIdx tI
  simp only
  rw [sort_get]
  split_ifs <;> rfl

lemma e_le (s : Finset (Fin n)) (q : Fin s.card) :
    ((s.orderEmbOfFin rfl q : Fin n) : ℕ) ≤ n - s.card + q := by
  have hsub : (Finset.Ioi q).map (s.orderEmbOfFin rfl).toEmbedding ⊆
      Finset.Ioi (s.orderEmbOfFin rfl q) := by
    intro y hy
    simp only [mem_map, mem_Ioi] at hy ⊢
    obtain ⟨a, ha, rfl⟩ := hy
    exact (s.orderEmbOfFin rfl).strictMono ha
  have := card_le_card hsub
  rw [card_map, Fin.card_Ioi, Fin.card_Ioi] at this
  have h1 := q.2
  have h2 := (s.orderEmbOfFin rfl q).2
  omega

lemma rank_ge (s : Finset (Fin n)) (q : Fin s.card) :
    (q : ℕ) ≤ (s.filter (· < s.orderEmbOfFin rfl q)).card := by
  have hsub : (Finset.Iio q).map (s.orderEmbOfFin rfl).toEmbedding ⊆
      s.filter (· < s.orderEmbOfFin rfl q) := by
    intro y hy
    simp only [mem_map, mem_Iio, mem_filter] at hy ⊢
    obtain ⟨a, ha, rfl⟩ := hy
    exact ⟨orderEmbOfFin_mem _ _ _, (s.orderEmbOfFin rfl).strictMono ha⟩
  have := card_le_card hsub
  rwa [card_map, Fin.card_Iio] at this

lemma tI_le (hk : k ≤ n) (s : Finset (Fin n)) (i : Fin k) : ((tI hk s i : Fin n) : ℕ) ≤ n - k + i := by
  unfold tI
  split_ifs
  · exact (Fin.le_iff_val_le_val.1 (min_le_left _ _))
  · exact le_rfl

lemma tI_strictMono (hk : k ≤ n) (s : Finset (Fin n)) : StrictMono (tI hk s) := by
  intro i i' hii
  have hii' : (i : ℕ) < i' := hii
  have h1 := tI_le hk s i
  rw [Fin.lt_iff_val_lt_val]
  unfold tI
  by_cases h' : (i' : ℕ) < s.card
  · rw [dif_pos h']
    have h2 : (i : ℕ) < s.card := lt_trans hii' h'
    have h3 : (tI hk s i) ≤ s.orderEmbOfFin rfl ⟨i, h2⟩ := by
      unfold tI; rw [dif_pos h2]; exact min_le_right _ _
    have h4 : s.orderEmbOfFin rfl ⟨i, h2⟩ < s.orderEmbOfFin rfl ⟨i', h'⟩ :=
      (s.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.2 hii')
    rcases min_choice (⟨n - k + i', by omega⟩ : Fin n) (s.orderEmbOfFin rfl ⟨i', h'⟩) with h | h
    · rw [h]; simp only; unfold tI at h1; omega
    · rw [h]; exact Fin.lt_iff_val_lt_val.1 (lt_of_le_of_lt h3 h4)
  · rw [dif_neg h']; simp only; unfold tI at h1; omega

lemma pw (hk : k ≤ n) (x : Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c) (hx : ∀ j, 0 ≤ x j) :
    (if k ≤ (univ.filter (fun j => c ≤ x j)).card then (k : ℝ) * c else 0) +
      ∑ j, (if (univ.filter (fun l => l < j ∧ c ≤ x l)).card < k then max 0 (x j - c) else 0) ≤
    ∑ i : Fin k, x (threshIdx hk x c i) := by
  simp_rw [threshIdx_eq]
  set s := univ.filter (fun j => c ≤ x j) with hs
  have hmem : ∀ j, j ∈ s ↔ c ≤ x j := by intro j; simp [hs]
  set e := s.orderEmbOfFin rfl with he
  have hrank : ∀ q, s.filter (· < e q) = univ.filter (fun l => l < e q ∧ c ≤ x l) := by
    intro q; ext l; simp [hs, and_comm]
  have hrange : ∀ j ∈ s, ∃ q, e q = j := by
    intro j hj
    have : j ∈ Set.range e := by rw [he, range_orderEmbOfFin]; exact hj
    exact this
  have inj : Function.Injective (tI hk s) := (tI_strictMono hk s).injective
  rw [← sum_image (fun a _ b _ h => inj h)]
  by_cases hT : k ≤ s.card
  · rw [if_pos hT]
    have ht : ∀ i : Fin k, tI hk s i = e ⟨i, lt_of_lt_of_le i.2 hT⟩ := by
      intro i
      unfold tI
      rw [dif_pos (lt_of_lt_of_le i.2 hT)]
      apply min_eq_right
      rw [Fin.le_iff_val_le_val]
      have := e_le s ⟨i, lt_of_lt_of_le i.2 hT⟩
      simp only at this ⊢
      omega
    set W := univ.image (tI hk s) with hW
    have hWs : W ⊆ s := by
      intro j hj
      simp only [hW, mem_image, mem_univ, true_and] at hj
      obtain ⟨i, rfl⟩ := hj
      rw [ht]; exact orderEmbOfFin_mem _ _ _
    have hcardW : (W.card : ℝ) = k := by
      rw [hW, card_image_of_injective _ inj]; simp
    have hle : ∀ j, (if (univ.filter (fun l => l < j ∧ c ≤ x l)).card < k
        then max 0 (x j - c) else 0) ≤ if j ∈ W then x j - c else 0 := by
      intro j
      have hR : 0 ≤ if j ∈ W then x j - c else 0 := by
        split_ifs with h
        · linarith [(hmem j).1 (hWs h)]
        · exact le_rfl
      split_ifs with hA hjW
      · exact (max_eq_right (by linarith [(hmem j).1 (hWs hjW)])).le
      · by_cases hjs : j ∈ s
        · exfalso
          obtain ⟨q, rfl⟩ := hrange j hjs
          have h1 := rank_ge s q
          rw [hrank] at h1
          have hq : (q : ℕ) < k := lt_of_le_of_lt h1 hA
          apply hjW
          simp only [hW, mem_image, mem_univ, true_and]
          exact ⟨⟨q, hq⟩, by rw [ht]⟩
        · have : x j < c := by rw [hmem] at hjs; exact lt_of_not_ge hjs
          exact (max_eq_left (by linarith)).le
      · rename_i h; linarith [(hmem j).1 (hWs h)]
      · exact le_rfl
    calc (k : ℝ) * c + ∑ j, (if (univ.filter (fun l => l < j ∧ c ≤ x l)).card < k
          then max 0 (x j - c) else 0)
        ≤ (k : ℝ) * c + ∑ j, (if j ∈ W then x j - c else 0) := by
          gcongr with j; exact hle j
      _ = ∑ j ∈ W, x j := by
          rw [sum_ite_mem, univ_inter, sum_sub_distrib, sum_const, nsmul_eq_mul, hcardW]; ring
  · rw [if_neg hT, zero_add]
    push_neg at hT
    have hsub : s ⊆ univ.image (tI hk s) := by
      intro j hj
      obtain ⟨q, rfl⟩ := hrange j hj
      simp only [mem_image, mem_univ, true_and]
      have hqk : (q : ℕ) < k := lt_trans q.2 hT
      by_cases hle : ((e q : Fin n) : ℕ) ≤ n - k + q
      · refine ⟨⟨q, hqk⟩, ?_⟩
        unfold tI
        rw [dif_pos q.2]
        apply min_eq_right
        rw [Fin.le_iff_val_le_val]; exact hle
      · push_neg at hle
        have hjn := (e q).2
        refine ⟨⟨(e q : ℕ) - (n - k), by omega⟩, ?_⟩
        unfold tI
        split_ifs with hp
        · have hgt : e q < e ⟨(e q : ℕ) - (n - k), hp⟩ :=
            e.strictMono (Fin.lt_iff_val_lt_val.2 (by show (q:ℕ) < (e q : ℕ) - (n-k); omega))
          rw [min_eq_left]
          · apply Fin.ext; show n - k + ((e q : ℕ) - (n - k)) = (e q : ℕ); omega
          · rw [Fin.le_iff_val_le_val]
            rw [Fin.lt_iff_val_lt_val] at hgt
            show n - k + ((e q : ℕ) - (n - k)) ≤ ((e ⟨(e q : ℕ) - (n - k), hp⟩ : Fin n) : ℕ)
            omega
        · apply Fin.ext; show n - k + ((e q : ℕ) - (n - k)) = (e q : ℕ); omega
    calc ∑ j, (if (univ.filter (fun l => l < j ∧ c ≤ x l)).card < k
          then max 0 (x j - c) else 0)
        ≤ ∑ j, (if j ∈ s then x j else 0) := by
          gcongr with j
          split_ifs with h1 h2 h2
          · exact max_le (hx j) (by linarith)
          · rw [hmem] at h2; exact (max_eq_left (by linarith [not_le.1 h2])).le
          · exact hx j
          · exact le_rfl
      _ = ∑ j ∈ s, x j := by rw [sum_ite_mem, univ_inter]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hx j)

lemma meas_filter {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (p : Fin m → Ω → Prop)
    [∀ l ω, Decidable (p l ω)] (hp : ∀ l, MeasurableSet {ω | p l ω})
    (Q : Finset (Fin m) → Prop) : MeasurableSet {ω | Q (univ.filter (fun l => p l ω))} := by
  classical
  have : {ω | Q (univ.filter (fun l => p l ω))} =
      ⋃ s ∈ (univ.filter Q : Finset (Finset (Fin m))), ⋂ l, {ω | p l ω ↔ l ∈ s} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, mem_filter, mem_univ,
      true_and, exists_prop]
    constructor
    · intro h; exact ⟨_, h, fun l => by simp⟩
    · rintro ⟨s, hs, h⟩
      convert hs
      ext l; simp [h l]
  rw [this]
  refine Finset.measurableSet_biUnion _ (fun s _ => MeasurableSet.iInter (fun l => ?_))
  by_cases hl : l ∈ s
  · simpa [hl] using hp l
  · have : {ω | p l ω ↔ l ∈ s} = {ω | p l ω}ᶜ := by ext ω; simp [hl]
    rw [this]; exact (hp l).compl

end PhAux
end CHMSPricing.OpmUniform

namespace CHMSPricing.OpmUniform
open MeasureTheory ProbabilityTheory Finset

theorem prophet_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X P)
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω) (hXint : ∀ i, Integrable (X i) P) (a b c : ℝ)
    (ha : a = ∑ i : Fin k, ∫ ω, max 0 (orderStat (fun j => X j ω) i - a / k) ∂P)
    (hb : b = ∑ i, ∫ ω, max 0 (X i ω - b / k) ∂P)
    (hac : a ≤ k * c) (hcb : k * c ≤ b) :
    ∑ i : Fin k, ∫ ω, orderStat (fun j => X j ω) i ∂P ≤
      2 * ∑ i : Fin k, ∫ ω, X (threshIdx hkn (fun j => X j ω) c i) ω ∂P := by
  have hkpos : (0:ℝ) < k := Nat.cast_pos.2 hk
  have ha0 : 0 ≤ a := by
    rw [ha]; exact sum_nonneg (fun i _ => integral_nonneg (fun ω => le_max_left _ _))
  have hc0 : 0 ≤ c := by
    by_contra h; push_neg at h; nlinarith
  -- upper bound for the prophet
  have hL : ∑ i : Fin k, ∫ ω, orderStat (fun j => X j ω) i ∂P ≤ 2 * a := by
    have h1 : ∀ i : Fin k, ∫ ω, orderStat (fun j => X j ω) i ∂P ≤
        a / k + ∫ ω, max 0 (orderStat (fun j => X j ω) i - a / k) ∂P := by
      intro i
      by_cases hi : Integrable (fun ω => orderStat (fun j => X j ω) i) P
      · have h2 : Integrable (fun ω => max 0 (orderStat (fun j => X j ω) i - a / k)) P := by
          have := (hi.sub (integrable_const (a / k))).pos_part
          refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
          simp [max_comm]
        calc ∫ ω, orderStat (fun j => X j ω) i ∂P
            ≤ ∫ ω, (a / k + max 0 (orderStat (fun j => X j ω) i - a / k)) ∂P :=
              integral_mono hi ((integrable_const _).add h2) (fun ω => by
                simp only; linarith [le_max_right 0 (orderStat (fun j => X j ω) i - a / k)])
          _ = _ := by rw [integral_add (integrable_const _) h2]; simp
      · rw [integral_undef hi]
        have := integral_nonneg (μ := P)
          (f := fun ω => max 0 (orderStat (fun j => X j ω) i - a / k))
          (fun ω => le_max_left 0 (orderStat (fun j => X j ω) i - a / k))
        linarith [div_nonneg ha0 hkpos.le]
    calc _ ≤ ∑ i : Fin k, (a / k + ∫ ω, max 0 (orderStat (fun j => X j ω) i - a / k) ∂P) :=
          sum_le_sum (fun i _ => h1 i)
      _ = 2 * a := by
          rw [sum_add_distrib, ← ha]; simp; field_simp; ring
  -- lower bound for the threshold rule
  have hYm : ∀ i : Fin k, Measurable (fun ω => X (threshIdx hkn (fun j => X j ω) c i) ω) := by
    intro i
    have : (fun ω => X (threshIdx hkn (fun j => X j ω) c i) ω) =
        fun ω => ∑ j, if threshIdx hkn (fun j => X j ω) c i = j then X j ω else 0 := by
      funext ω; rw [sum_ite_eq]; simp
    rw [this]
    refine Finset.measurable_sum _ (fun j _ => Measurable.ite ?_ (hXm j) measurable_const)
    simp_rw [PhAux.threshIdx_eq]
    exact PhAux.meas_filter (fun l ω => c ≤ X l ω)
      (fun l => measurableSet_le measurable_const (hXm l)) (fun s => PhAux.tI hkn s i = j)
  have hYi : ∀ i : Fin k, Integrable (fun ω => X (threshIdx hkn (fun j => X j ω) c i) ω) P := by
    intro i
    refine Integrable.mono' (integrable_finset_sum univ (fun j _ => (hXint j).abs))
      (hYm i).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact single_le_sum (f := fun j => |X j ω|) (fun j _ => abs_nonneg _) (mem_univ _)
  have hAm : ∀ j : Fin n, MeasurableSet
      {ω | (univ.filter (fun l => l < j ∧ c ≤ X l ω)).card < k} := by
    intro j
    refine PhAux.meas_filter (fun l ω => l < j ∧ c ≤ X l ω) (fun l => ?_) (fun s => s.card < k)
    by_cases h : l < j
    · simpa [h] using measurableSet_le measurable_const (hXm l)
    · simp [h]
  have hTm : MeasurableSet {ω | k ≤ (univ.filter (fun l => c ≤ X l ω)).card} :=
    PhAux.meas_filter (fun l ω => c ≤ X l ω)
      (fun l => measurableSet_le measurable_const (hXm l)) (fun s => k ≤ s.card)
  set pT := (P {ω | k ≤ (univ.filter (fun l => c ≤ X l ω)).card}).toReal with hpT
  set qT := (P {ω | k ≤ (univ.filter (fun l => c ≤ X l ω)).card}ᶜ).toReal with hqT
  have hpq : pT + qT = 1 := by
    rw [hpT, hqT, prob_compl_eq_one_sub hTm, ENNReal.toReal_sub_of_le prob_le_one
      ENNReal.one_ne_top]
    simp
  have hI1 : ∫ ω, (if k ≤ (univ.filter (fun l => c ≤ X l ω)).card then (k : ℝ) * c else 0) ∂P
      = k * c * pT := by
    have : (fun ω => if k ≤ (univ.filter (fun l => c ≤ X l ω)).card then (k : ℝ) * c else 0) =
        {ω | k ≤ (univ.filter (fun l => c ≤ X l ω)).card}.indicator (fun _ => (k : ℝ) * c) := by
      funext ω; simp [Set.indicator]
    rw [this, integral_indicator_const _ hTm, measureReal_def, smul_eq_mul, mul_comm]
  have i1 : Integrable
      (fun ω => if k ≤ (univ.filter (fun l => c ≤ X l ω)).card then (k : ℝ) * c else 0) P := by
    have : (fun ω => if k ≤ (univ.filter (fun l => c ≤ X l ω)).card then (k : ℝ) * c else 0) =
        {ω | k ≤ (univ.filter (fun l => c ≤ X l ω)).card}.indicator (fun _ => (k : ℝ) * c) := by
      funext ω; simp [Set.indicator]
    rw [this]; exact (integrable_const _).indicator hTm
  have i2 : ∀ j : Fin n, Integrable (fun ω => if (univ.filter (fun l => l < j ∧ c ≤ X l ω)).card < k
      then max 0 (X j ω - c) else 0) P := by
    intro j
    have h0 : Integrable (fun ω => max 0 (X j ω - c)) P := by
      have := ((hXint j).sub (integrable_const c)).pos_part
      refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp [max_comm]
    have := h0.indicator (hAm j)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp [Set.indicator]
  have hI2 : ∀ j : Fin n, ∫ ω, (if (univ.filter (fun l => l < j ∧ c ≤ X l ω)).card < k
      then max 0 (X j ω - c) else 0) ∂P =
      (P {ω | (univ.filter (fun l => l < j ∧ c ≤ X l ω)).card < k}).toReal *
        ∫ ω, max 0 (X j ω - c) ∂P := by
    intro j
    let S : Finset (Fin n) := univ.filter (· < j)
    let T' : Finset (Fin n) := {j}
    have hST : Disjoint S T' := by
      rw [Finset.disjoint_singleton_right]; simp [S]
    have hind := hXind.indepFun_finset S T' hST hXm
    let φ : (S → ℝ) → ℝ := fun y =>
      if (univ.filter (fun l : Fin n => ∃ h : l ∈ S, c ≤ y ⟨l, h⟩)).card < k then 1 else 0
    let ψ : (T' → ℝ) → ℝ := fun y => max 0 (y ⟨j, mem_singleton_self j⟩ - c)
    have hφm : Measurable φ := by
      refine Measurable.ite ?_ measurable_const measurable_const
      refine PhAux.meas_filter (fun l (y : S → ℝ) => ∃ h : l ∈ S, c ≤ y ⟨l, h⟩) (fun l => ?_)
        (fun s => s.card < k)
      by_cases hl : l ∈ S
      · have : {y : S → ℝ | ∃ h : l ∈ S, c ≤ y ⟨l, h⟩} = {y | c ≤ y ⟨l, hl⟩} := by
          ext y; simp [hl]
        rw [this]; exact measurableSet_le measurable_const (measurable_pi_apply _)
      · simp [hl]
    have hψm : Measurable ψ := measurable_const.max ((measurable_pi_apply _).sub measurable_const)
    have hind2 := hind.comp hφm hψm
    have hfe : ∀ ω, (univ.filter (fun l : Fin n => ∃ h : l ∈ S, c ≤ X l ω)) =
        univ.filter (fun l => l < j ∧ c ≤ X l ω) := by
      intro ω; ext l; simp [S]
    have heq : (fun ω => if (univ.filter (fun l => l < j ∧ c ≤ X l ω)).card < k
        then max 0 (X j ω - c) else 0) =
        (φ ∘ fun ω (l : S) => X l ω) * (ψ ∘ fun ω (l : T') => X l ω) := by
      funext ω
      simp only [Pi.mul_apply, Function.comp, φ, ψ, hfe]
      split_ifs <;> simp
    have hmS : Measurable fun ω (l : S) => X l ω := measurable_pi_lambda _ (fun l => hXm l)
    have hmT : Measurable fun ω (l : T') => X l ω := measurable_pi_lambda _ (fun l => hXm l)
    rw [heq, hind2.integral_mul_eq_mul_integral (hφm.comp hmS).aestronglyMeasurable
      (hψm.comp hmT).aestronglyMeasurable]
    congr 1
    have : (φ ∘ fun ω (l : S) => X l ω) =
        {ω | (univ.filter (fun l => l < j ∧ c ≤ X l ω)).card < k}.indicator 1 := by
      funext ω
      simp only [Function.comp, φ, hfe, Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    rw [this, integral_indicator_one (hAm j), measureReal_def]
  have hR : (k : ℝ) * c ≤ ∑ i : Fin k, ∫ ω, X (threshIdx hkn (fun j => X j ω) c i) ω ∂P := by
    rw [← integral_finset_sum _ (fun i _ => hYi i)]
    have hpw : ∀ᵐ ω ∂P,
        ((if k ≤ (univ.filter (fun l => c ≤ X l ω)).card then (k : ℝ) * c else 0) +
          ∑ j, (if (univ.filter (fun l => l < j ∧ c ≤ X l ω)).card < k
            then max 0 (X j ω - c) else 0)) ≤
        ∑ i : Fin k, X (threshIdx hkn (fun j => X j ω) c i) ω := by
      filter_upwards [ae_all_iff.2 hXnn] with ω hω
      exact PhAux.pw hkn (fun j => X j ω) c hc0 hω
    have hmono : ∫ ω, ((if k ≤ (univ.filter (fun l => c ≤ X l ω)).card then (k : ℝ) * c else 0) +
          ∑ j, (if (univ.filter (fun l => l < j ∧ c ≤ X l ω)).card < k
            then max 0 (X j ω - c) else 0)) ∂P ≤
        ∫ ω, ∑ i : Fin k, X (threshIdx hkn (fun j => X j ω) c i) ω ∂P := integral_mono_ae (i1.add (integrable_finset_sum univ (fun j _ => i2 j)))
      (integrable_finset_sum univ (fun i _ => hYi i)) hpw
    rw [integral_add i1 (integrable_finset_sum univ (fun j _ => i2 j)),
      integral_finset_sum _ (fun j _ => i2 j), hI1] at hmono
    simp_rw [hI2] at hmono
    refine le_trans ?_ hmono
    -- k c ≤ k c pT + Σ_j P(A_j) E_j
    have hE : ∀ j : Fin n, qT * ∫ ω, max 0 (X j ω - b / k) ∂P ≤
        (P {ω | (univ.filter (fun l => l < j ∧ c ≤ X l ω)).card < k}).toReal *
          ∫ ω, max 0 (X j ω - c) ∂P := by
      intro j
      have hcb' : c ≤ b / k := by rw [le_div_iff₀ hkpos]; linarith
      have hE1 : ∫ ω, max 0 (X j ω - b / k) ∂P ≤ ∫ ω, max 0 (X j ω - c) ∂P := by
        refine integral_mono ?_ ?_ (fun ω => ?_)
        · have := ((hXint j).sub (integrable_const (b / k))).pos_part
          refine this.congr (Filter.Eventually.of_forall fun ω => ?_); simp [max_comm]
        · have := ((hXint j).sub (integrable_const c)).pos_part
          refine this.congr (Filter.Eventually.of_forall fun ω => ?_); simp [max_comm]
        · exact max_le_max le_rfl (by linarith)
      have hE0 : 0 ≤ ∫ ω, max 0 (X j ω - b / k) ∂P :=
        integral_nonneg (fun ω => le_max_left _ _)
      have hP : qT ≤ (P {ω | (univ.filter (fun l => l < j ∧ c ≤ X l ω)).card < k}).toReal := by
        rw [hqT]
        refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun ω hω => ?_))
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω ⊢
        refine lt_of_le_of_lt (card_le_card (fun l hl => ?_)) hω
        simp only [mem_filter, mem_univ, true_and] at hl ⊢
        exact hl.2
      have hq0 : 0 ≤ qT := ENNReal.toReal_nonneg
      calc qT * ∫ ω, max 0 (X j ω - b / k) ∂P ≤ qT * ∫ ω, max 0 (X j ω - c) ∂P :=
            mul_le_mul_of_nonneg_left hE1 hq0
        _ ≤ _ := mul_le_mul_of_nonneg_right hP (hE1.trans' hE0 |> fun h => le_trans hE0 hE1)
    have hsum := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin n))) => hE j)
    rw [← mul_sum, ← hb] at hsum
    have hq0 : 0 ≤ qT := ENNReal.toReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_left hcb hq0]
  linarith

end CHMSPricing.OpmUniform

open CHMSPricing.OpmUniform
open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (X : Fin n → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hXind : iIndepFun X P)
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω) (hXint : ∀ i, Integrable (X i) P) (a b c : ℝ)
    (ha : a = ∑ i : Fin k, ∫ ω, max 0 (orderStat (fun j => X j ω) i - a / k) ∂P)
    (hb : b = ∑ i, ∫ ω, max 0 (X i ω - b / k) ∂P)
    (hac : a ≤ k * c) (hcb : k * c ≤ b) :
    ∑ i : Fin k, ∫ ω, orderStat (fun j => X j ω) i ∂P ≤
      2 * ∑ i : Fin k, ∫ ω, X (threshIdx hkn (fun j => X j ω) c i) ω ∂P := by
  exact prophet_core P hk hkn X hXm hXind hXnn hXint a b c ha hb hac hcb
