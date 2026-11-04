-- Prove2me | solution 1 for BlindProphetSec.Blind.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:25:30.499772+00:00
-- url     : https://prove2.me/submissions/481dd398-26f8-4664-bb16-3179dffabe8d

import Mathlib
import Definitions.Def_BlindProphetSec_Blind_Setting

open MeasureTheory

namespace BPSLem31

open BlindProphetSec.Blind

/-- Independence: `P(V_{σ j} ∈ S j ∀ j) = ∏_j μ_{σ j}(S j)`. -/
lemma box_prob' {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (σ : Equiv.Perm (Fin n)) (S : Fin n → Set ℝ) :
    ((Measure.pi μ) {v | ∀ j, v (σ j) ∈ S j}).toReal = ∏ j, (μ (σ j) (S j)).toReal := by
  have hset : {v : Fin n → ℝ | ∀ j, v (σ j) ∈ S j} = Set.univ.pi (fun p => S (σ.symm p)) := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h p
      have := h (σ.symm p)
      simpa using this
    · intro h j
      have := h (σ j)
      simpa using this
  rw [hset, Measure.pi_pi, ENNReal.toReal_prod]
  conv_lhs => rw [← Equiv.prod_comp σ]
  simp

lemma measurable_box {n : ℕ} (σ : Equiv.Perm (Fin n)) (J : Finset (Fin n)) (τ : Fin n → ℝ) :
    MeasurableSet {v : Fin n → ℝ | ∀ j ∈ J, v (σ j) ≤ τ j} := by
  have : {v : Fin n → ℝ | ∀ j ∈ J, v (σ j) ≤ τ j} = ⋂ j ∈ J, (fun v : Fin n → ℝ => v (σ j)) ⁻¹' Set.Iic (τ j) := by
    ext v; simp
  rw [this]
  exact Finset.measurableSet_biInter J fun j _ => measurableSet_Iic.preimage (measurable_pi_apply _)

lemma firstStop_some {n : ℕ} (acc : Fin n → Prop) (h : ∃ j, acc j) :
    ∃ m, firstStop acc = some m ∧ acc m ∧ ∀ m', acc m' → m ≤ m' := by
  classical
  refine ⟨(Finset.univ.filter acc).min' ⟨h.choose, by simp [h.choose_spec]⟩, ?_, ?_, ?_⟩
  · unfold firstStop
    rw [dif_pos h]
  · have := Finset.min'_mem (Finset.univ.filter acc) ⟨h.choose, by simp [h.choose_spec]⟩
    simpa using this
  · intro m' hm'
    exact Finset.min'_le _ _ (by simp [hm'])

lemma firstStop_none {n : ℕ} (acc : Fin n → Prop) (h : ¬ ∃ j, acc j) : firstStop acc = none := by
  classical
  unfold firstStop
  rw [dif_neg h]

/-- Per-order decomposition of `P(V_{σ_T} > t)` according to the stopping time. -/
lemma per_sigma {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (τ : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (J : ℕ) (t : ℝ) (ht0 : 0 ≤ t)
    (hlo : ∀ k : Fin n, J ≤ k.val → τ k ≤ t) (hhi : ∀ k : Fin n, k.val < J → t < τ k) :
    ((Measure.pi μ) {v | t < ttaReward τ v σ}).toReal =
      ((Measure.pi μ) {v | stopLE (ttaAcc τ v σ) J}).toReal +
        ∑ k ∈ Finset.univ.filter (fun k : Fin n => J ≤ k.val),
          ((Measure.pi μ) {v | ∀ m ∈ Finset.univ.filter (fun m : Fin n => m.val < k.val),
              v (σ m) ≤ τ m}).toReal * (μ (σ k) (Set.Ioi t)).toReal := by
  classical
  set U : Set (Fin n → ℝ) := {v | stopLE (ttaAcc τ v σ) J} with hU
  let Pk : Fin n → Finset (Fin n) := fun k => Finset.univ.filter (fun m : Fin n => m.val < k.val)
  let D : Fin n → Set (Fin n → ℝ) := fun k =>
    {v | (∀ m ∈ Pk k, v (σ m) ≤ τ m) ∧ t < v (σ k)}
  set Kset : Finset (Fin n) := Finset.univ.filter (fun k : Fin n => J ≤ k.val) with hKset
  -- set decomposition
  have hdecomp : {v : Fin n → ℝ | t < ttaReward τ v σ} = U ∪ ⋃ k ∈ Kset, D k := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, hU, hKset, Finset.mem_filter,
      Finset.mem_univ, true_and, exists_prop]
    constructor
    · intro hv
      by_cases hex : ∃ j, ttaAcc τ v σ j
      · obtain ⟨m, hm, hacc, hmin⟩ := firstStop_some _ hex
        have hr : ttaReward τ v σ = v (σ m) := by
          unfold ttaReward stopReward; rw [hm]
        rw [hr] at hv
        by_cases hmJ : m.val < J
        · exact Or.inl ⟨m, hmJ, hacc⟩
        · right
          refine ⟨m, by omega, ?_, hv⟩
          intro m' hm'
          have hm'' : m'.val < m.val := by simpa [Pk] using hm'
          by_contra hc
          have := hmin m' (by simp only [ttaAcc]; exact lt_of_not_ge hc)
          exact absurd (Fin.le_def.mp this) (by omega)
      · have hr : ttaReward τ v σ = 0 := by
          unfold ttaReward stopReward; rw [firstStop_none _ hex]
        rw [hr] at hv; linarith
    · rintro (⟨m0, hm0J, hacc0⟩ | ⟨k, hkJ, hbox, htk⟩)
      · obtain ⟨m, hm, hacc, hmin⟩ := firstStop_some (ttaAcc τ v σ) ⟨m0, hacc0⟩
        have hr : ttaReward τ v σ = v (σ m) := by
          unfold ttaReward stopReward; rw [hm]
        rw [hr]
        have hmm0 := Fin.le_def.mp (hmin m0 hacc0)
        exact lt_trans (hhi m (by omega)) hacc
      · have hacck : ttaAcc τ v σ k := lt_of_le_of_lt (hlo k hkJ) htk
        obtain ⟨m, hm, hacc, hmin⟩ := firstStop_some (ttaAcc τ v σ) ⟨k, hacck⟩
        have hmk : m = k := by
          apply le_antisymm (hmin k hacck)
          by_contra hc
          have hlt : m < k := lt_of_not_ge hc
          have := hbox m (by simpa [Pk] using hlt)
          exact absurd hacc (not_lt.mpr this)
        have hr : ttaReward τ v σ = v (σ k) := by
          unfold ttaReward stopReward; rw [hm, hmk]
        rw [hr]; exact htk
  -- measurability
  have hUm : MeasurableSet U := by
    have : U = ⋃ m ∈ Finset.univ.filter (fun m : Fin n => m.val < J),
        (fun v : Fin n → ℝ => v (σ m)) ⁻¹' Set.Ioi (τ m) := by
      ext v; simp [hU, stopLE, ttaAcc]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun m _ =>
      measurableSet_Ioi.preimage (measurable_pi_apply _)
  have hDm : ∀ k, MeasurableSet (D k) := by
    intro k
    have : D k = {v : Fin n → ℝ | ∀ m ∈ Pk k, v (σ m) ≤ τ m} ∩
        (fun v : Fin n → ℝ => v (σ k)) ⁻¹' Set.Ioi t := by
      ext v; simp [D]
    rw [this]
    exact (measurable_box σ (Pk k) τ).inter (measurableSet_Ioi.preimage (measurable_pi_apply _))
  -- disjointness
  have hdisjU : Disjoint U (⋃ k ∈ Kset, D k) := by
    rw [Set.disjoint_iUnion₂_right]
    intro k hk
    rw [Set.disjoint_left]
    rintro v ⟨m, hmJ, hacc⟩ ⟨hbox, _⟩
    have hkJ : J ≤ k.val := by simpa [hKset] using hk
    have := hbox m (by simp [Pk]; omega)
    exact absurd hacc (not_lt.mpr this)
  have hdisjD : (Kset : Set (Fin n)).PairwiseDisjoint D := by
    intro k hk k' hk' hne
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hKset] at hk hk'
    rw [Function.onFun, Set.disjoint_left]
    rintro v ⟨hbox, htk⟩ ⟨hbox', htk'⟩
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · have := hbox' k (by simpa [Pk] using h)
      linarith [hlo k hk]
    · have := hbox k' (by simpa [Pk] using h)
      linarith [hlo k' hk']
  -- measure computation
  rw [hdecomp, measure_union hdisjU (Finset.measurableSet_biUnion _ fun k _ => hDm k),
    measure_biUnion_finset hdisjD (fun k _ => hDm k),
    ENNReal.toReal_add (measure_ne_top _ _)
      (ENNReal.sum_ne_top.mpr fun k _ => measure_ne_top _ _),
    ENNReal.toReal_sum (fun k _ => measure_ne_top _ _)]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  -- factorization of `P(D k)`
  have hD : D k = {v : Fin n → ℝ | ∀ j, v (σ j) ∈
      (if j.val < k.val then Set.Iic (τ j) else if j = k then Set.Ioi t else Set.univ)} := by
    ext v
    simp only [D, Pk, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hbox, htk⟩ j
      split_ifs with h1 h2
      · exact hbox j h1
      · rw [h2]; exact htk
      · trivial
    · intro h
      refine ⟨fun m hm => ?_, ?_⟩
      · have := h m; rw [if_pos hm] at this; exact this
      · have := h k; rw [if_neg (lt_irrefl _), if_pos rfl] at this; exact this
  have hB : {v : Fin n → ℝ | ∀ m ∈ Pk k, v (σ m) ≤ τ m} = {v : Fin n → ℝ | ∀ j, v (σ j) ∈
      (if j.val < k.val then Set.Iic (τ j) else Set.univ)} := by
    ext v
    simp only [Pk, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hbox j
      split_ifs with h1
      · exact hbox j h1
      · trivial
    · intro h m hm
      have := h m; rw [if_pos hm] at this; exact this
  show ((Measure.pi μ) (D k)).toReal = ((Measure.pi μ) {v | ∀ m ∈ Pk k, v (σ m) ≤ τ m}).toReal *
    (μ (σ k) (Set.Ioi t)).toReal
  rw [hD, hB, box_prob', box_prob']
  have e1 : ∀ j, (μ (σ j) (if j.val < k.val then Set.Iic (τ j)
      else if j = k then Set.Ioi t else Set.univ)).toReal =
      (if j.val < k.val then (μ (σ j) (Set.Iic (τ j))).toReal else 1) *
        (if j = k then (μ (σ k) (Set.Ioi t)).toReal else 1) := by
    intro j
    by_cases h1 : j.val < k.val
    · have hjk : j ≠ k := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      simp [h1, hjk]
    · by_cases h2 : j = k
      · subst h2; simp
      · simp [h1, h2]
  have e2 : ∀ j, (μ (σ j) (if j.val < k.val then Set.Iic (τ j) else Set.univ)).toReal =
      (if j.val < k.val then (μ (σ j) (Set.Iic (τ j))).toReal else 1) := by
    intro j
    split_ifs <;> simp
  simp_rw [e1, e2]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite_eq']
  simp

end BPSLem31

open BlindProphetSec.Blind BPSLem31 in
theorem solution {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hnn : ∀ i, μ i (Set.Iio 0) = 0) (τ : Fin n → ℝ) (hτ : Antitone τ)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n + 1) (t : ℝ) (ht0 : 0 ≤ t)
    (ht_lo : ∀ h : j ≤ n, τ ⟨j - 1, by omega⟩ ≤ t)
    (ht_hi : ∀ h : 2 ≤ j, t < τ ⟨j - 2, by omega⟩) :
    probVS μ (fun v σ => t < ttaReward τ v σ) =
      probVS μ (fun v σ => stopLE (ttaAcc τ v σ) (j - 1)) +
        ∑ i : Fin n, (μ i (Set.Ioi t)).toReal *
          ∑ k ∈ Finset.univ.filter (fun k : Fin n => j ≤ k.val + 1),
            ((n : ℝ) * probVS μ (fun v σ => stopGE (ttaAcc τ v σ) (k.val + 1) ∧ σ k = i)) / n := by
  classical
  have hlo : ∀ k : Fin n, j - 1 ≤ k.val → τ k ≤ t := by
    intro k hk
    have hjn' : j ≤ n := by have := k.isLt; omega
    exact le_trans (hτ (Fin.le_def.mpr (by simp; omega))) (ht_lo hjn')
  have hhi : ∀ k : Fin n, k.val < j - 1 → t < τ k := by
    intro k hk
    have hj2 : 2 ≤ j := by omega
    exact lt_of_lt_of_le (ht_hi hj2) (hτ (Fin.le_def.mpr (by simp; omega)))
  -- the event `stopGE ∧ σ k = i` as an indicator times the box
  have hRHS : ∀ (σ : Equiv.Perm (Fin n)) (k i : Fin n),
      ((Measure.pi μ) {v | stopGE (ttaAcc τ v σ) (k.val + 1) ∧ σ k = i}).toReal =
        if σ k = i then ((Measure.pi μ) {v | ∀ m ∈ Finset.univ.filter
          (fun m : Fin n => m.val < k.val), v (σ m) ≤ τ m}).toReal else 0 := by
    intro σ k i
    split_ifs with hσ
    · congr 2
      ext v
      simp only [stopGE, ttaAcc, Set.mem_ofPred_eq, not_lt, hσ, and_true, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro h m hm; exact h m (by omega)
      · intro h m hm; exact h m (by omega)
    · have : {v : Fin n → ℝ | stopGE (ttaAcc τ v σ) (k.val + 1) ∧ σ k = i} = ∅ := by
        ext v; simp [hσ]
      rw [this]; simp
  by_cases hn0 : n = 0
  · subst hn0
    simp [probVS]
    have : {v : Fin 0 → ℝ | t < ttaReward τ v 1} = ∅ := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have : ttaReward τ v 1 = 0 := by
        unfold ttaReward stopReward
        rw [firstStop_none]
        rintro ⟨j, _⟩; exact j.elim0
      rw [this]; exact ht0
    have h2 : {v : Fin 0 → ℝ | stopLE (ttaAcc τ v 1) (j - 1)} = ∅ := by
      ext v; simp only [stopLE, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨j, _⟩; exact j.elim0
    rw [this, h2]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  -- rewrite the right-hand side
  have hsimp : ∀ (k i : Fin n),
      ((n : ℝ) * probVS μ (fun v σ => stopGE (ttaAcc τ v σ) (k.val + 1) ∧ σ k = i)) / n =
        probVS μ (fun v σ => stopGE (ttaAcc τ v σ) (k.val + 1) ∧ σ k = i) := by
    intro k i; field_simp
  simp_rw [hsimp]
  have hfilt : Finset.univ.filter (fun k : Fin n => j ≤ k.val + 1) =
      Finset.univ.filter (fun k : Fin n => j - 1 ≤ k.val) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  rw [hfilt]
  unfold probVS
  simp_rw [hRHS]
  simp_rw [per_sigma μ τ _ (j - 1) t ht0 hlo hhi]
  rw [Finset.sum_add_distrib, mul_add]
  congr 1
  -- regroup the second sum by `i = σ k`
  set c : ℝ := 1 / (n.factorial : ℝ)
  set Kf := Finset.univ.filter (fun k : Fin n => j - 1 ≤ k.val)
  let box : Equiv.Perm (Fin n) → Fin n → ℝ := fun σ k => ((Measure.pi μ) {v | ∀ m ∈
    Finset.univ.filter (fun m : Fin n => m.val < k.val), v (σ m) ≤ τ m}).toReal
  let G : Fin n → ℝ := fun i => (μ i (Set.Ioi t)).toReal
  have hinner : ∀ (σ : Equiv.Perm (Fin n)) (k : Fin n),
      ∑ i : Fin n, G i * (c * (if σ k = i then box σ k else 0)) = c * (box σ k * G (σ k)) := by
    intro σ k
    rw [Finset.sum_eq_single (σ k)]
    · simp only [if_true]; ring
    · intro i _ hi
      rw [if_neg (Ne.symm hi)]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  calc c * ∑ σ : Equiv.Perm (Fin n), ∑ k ∈ Kf, box σ k * G (σ k)
      = ∑ σ : Equiv.Perm (Fin n), ∑ k ∈ Kf, ∑ i : Fin n,
          G i * (c * (if σ k = i then box σ k else 0)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro σ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _
        rw [hinner]
    _ = ∑ k ∈ Kf, ∑ σ : Equiv.Perm (Fin n), ∑ i : Fin n,
          G i * (c * (if σ k = i then box σ k else 0)) := Finset.sum_comm
    _ = ∑ k ∈ Kf, ∑ i : Fin n, ∑ σ : Equiv.Perm (Fin n),
          G i * (c * (if σ k = i then box σ k else 0)) := by
        apply Finset.sum_congr rfl; intro k _
        exact Finset.sum_comm
    _ = ∑ i : Fin n, ∑ k ∈ Kf, ∑ σ : Equiv.Perm (Fin n),
          G i * (c * (if σ k = i then box σ k else 0)) := Finset.sum_comm
    _ = ∑ i : Fin n, G i * ∑ k ∈ Kf, c * ∑ σ : Equiv.Perm (Fin n),
          (if σ k = i then box σ k else 0) := by
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro k _
        rw [Finset.mul_sum, Finset.mul_sum]
