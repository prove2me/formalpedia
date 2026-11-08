-- Prove2me | solution 1 for BidPriceControl.Asymptotic.kuhn_tucker_conditions
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T10:11:48.193008+00:00
-- url     : https://prove2.me/submissions/f08b1408-0969-476c-ba96-795afa1c4026

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace Aux_BPC_kt
open BidPriceControl.Asymptotic

/-- Perturbation of the `i`-th bid price by `d`. -/
def pert {m : ℕ} (μ : Fin m → ℝ) (i : Fin m) (d : ℝ) : Fin m → ℝ :=
  fun l => μ l + if l = i then d else 0

lemma bidSum_pert {m n : ℕ} (A : Fin m → Fin n → ℕ) (μ : Fin m → ℝ) (i : Fin m) (d : ℝ)
    (j : Fin n) : bidSum A (pert μ i d) j = bidSum A μ j + d * (A i j : ℝ) := by
  simp [bidSum, pert, add_mul, Finset.sum_add_distrib, ite_mul]

lemma relaxed_pert {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (μ : Fin m → ℝ) (i : Fin m) (d : ℝ) :
    relaxedValue A F k x (pert μ i d) =
      (∑ t ∈ Finset.Icc 1 k, ∑ j, ∫ r, max (r j - (bidSum A μ j + d * (A i j : ℝ))) 0 ∂(F t))
        + ((∑ l, μ l * (x l : ℝ)) + d * (x i : ℝ)) := by
  unfold relaxedValue
  simp only [bidSum_pert]
  congr 1
  simp [pert, add_mul, Finset.sum_add_distrib, ite_mul]

lemma ite_meas {n : ℕ} (j : Fin n) (b c : ℝ) :
    Measurable (fun r : Fin n → ℝ => if b < r j then c else 0) :=
  Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply j))
    measurable_const measurable_const

lemma integral_ite1 {n : ℕ} (j : Fin n) (b c : ℝ) (G : Measure (Fin n → ℝ))
    [IsProbabilityMeasure G] :
    ∫ r, (if b < r j then c else 0) ∂G = (G {r | b < r j}).toReal * c := by
  have : (fun r : Fin n → ℝ => if b < r j then c else 0)
      = Set.indicator {r | b < r j} (fun _ => c) := by
    funext r; simp [Set.indicator]
  rw [this, integral_indicator_const _
    (measurableSet_lt measurable_const (measurable_pi_apply j))]
  simp [Measure.real]

/-- The basic one-sided bound for an upward perturbation `c ≥ 0` of the threshold. -/
lemma int_up {n : ℕ} (j : Fin n) (b c : ℝ) (hc : 0 ≤ c) (G : Measure (Fin n → ℝ))
    (hG : IsRequestLaw G) :
    ∫ r, max (r j - (b + c)) 0 ∂G ≤
      ∫ r, max (r j - b) 0 ∂G - c * (G {r | b + c < r j}).toReal := by
  haveI := hG.isProbabilityMeasure
  have i1 : Integrable (fun r : Fin n → ℝ => max (r j - (b + c)) 0) G :=
    ((hG.integrable_coord j).sub (integrable_const _)).pos_part
  have i2 : Integrable (fun r : Fin n → ℝ => max (r j - b) 0) G :=
    ((hG.integrable_coord j).sub (integrable_const _)).pos_part
  have i3 : Integrable (fun r : Fin n → ℝ => if b + c < r j then c else 0) G :=
    Integrable.of_bound (ite_meas j _ _).aestronglyMeasurable |c|
      (Eventually.of_forall fun r => by split_ifs <;> simp)
  have hpt : ∀ r : Fin n → ℝ, max (r j - (b + c)) 0 ≤
      max (r j - b) 0 - (if b + c < r j then c else 0) := by
    intro r
    split_ifs with h
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · rw [max_eq_right (by linarith)]; linarith [le_max_right (r j - b) 0]
  calc ∫ r, max (r j - (b + c)) 0 ∂G
      ≤ ∫ r, (max (r j - b) 0 - (if b + c < r j then c else 0)) ∂G :=
        integral_mono i1 (i2.sub i3) hpt
    _ = _ := by
        rw [integral_sub i2 i3, integral_ite1]; ring

lemma int_down {n : ℕ} (j : Fin n) (b c : ℝ) (hc : 0 ≤ c) (G : Measure (Fin n → ℝ))
    (hG : IsRequestLaw G) :
    ∫ r, max (r j - (b + -c)) 0 ∂G ≤
      ∫ r, max (r j - b) 0 ∂G + c * (G {r | b + -c < r j}).toReal := by
  haveI := hG.isProbabilityMeasure
  have i1 : Integrable (fun r : Fin n → ℝ => max (r j - (b + -c)) 0) G :=
    ((hG.integrable_coord j).sub (integrable_const _)).pos_part
  have i2 : Integrable (fun r : Fin n → ℝ => max (r j - b) 0) G :=
    ((hG.integrable_coord j).sub (integrable_const _)).pos_part
  have i3 : Integrable (fun r : Fin n → ℝ => if b + -c < r j then c else 0) G :=
    Integrable.of_bound (ite_meas j _ _).aestronglyMeasurable |c|
      (Eventually.of_forall fun r => by split_ifs <;> simp)
  have hpt : ∀ r : Fin n → ℝ, max (r j - (b + -c)) 0 ≤
      max (r j - b) 0 + (if b + -c < r j then c else 0) := by
    intro r
    split_ifs with h
    · rw [max_eq_left (by linarith)]; linarith [le_max_left (r j - b) 0]
    · rw [max_eq_right (by linarith)]; linarith [le_max_right (r j - b) 0]
  calc ∫ r, max (r j - (b + -c)) 0 ∂G
      ≤ ∫ r, (max (r j - b) 0 + (if b + -c < r j then c else 0)) ∂G :=
        integral_mono i1 (i2.add i3) hpt
    _ = _ := by
        rw [integral_add i2 i3, integral_ite1]; ring

lemma pert_nonneg {m : ℕ} (μ : Fin m → ℝ) (hμ : 0 ≤ μ) (i : Fin m) (d : ℝ)
    (hd : 0 ≤ μ i + d) : 0 ≤ pert μ i d := by
  intro l
  simp only [pert, Pi.zero_apply]
  split_ifs with h
  · subst h; exact hd
  · simpa using hμ l

/-- Increasing-threshold limit: `P(R^j > b + a ε/(n+1)) → P(R^j > b)`. -/
lemma tendsto_up {n : ℕ} (j : Fin n) (b a ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε)
    (G : Measure (Fin n → ℝ)) [IsProbabilityMeasure G] :
    Tendsto (fun N : ℕ => (G {r | b + ε / ((N : ℝ) + 1) * a < r j}).toReal * a) atTop
      (𝓝 ((G {r | b < r j}).toReal * a)) := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0; simp
  apply Tendsto.mul_const
  set s : ℕ → Set (Fin n → ℝ) := fun N => {r | b + ε / ((N : ℝ) + 1) * a < r j}
  have hmono : Monotone s := by
    intro N M hNM r hr
    simp only [s, Set.mem_setOf_eq] at hr ⊢
    have : ε / ((M : ℝ) + 1) ≤ ε / ((N : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left hε.le (by positivity)
      have : (N : ℝ) ≤ M := by exact_mod_cast hNM
      linarith
    nlinarith
  have hU : (⋃ N, s N) = {r | b < r j} := by
    ext r
    simp only [s, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨N, hN⟩
      have : 0 ≤ ε / ((N : ℝ) + 1) * a := by positivity
      linarith
    · intro hr
      obtain ⟨N, hN⟩ := exists_nat_gt (ε * a / (r j - b))
      refine ⟨N, ?_⟩
      have hd : 0 < r j - b := by linarith
      have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have : ε * a < (r j - b) * ((N : ℝ) + 1) := by
        rw [div_lt_iff₀ hd] at hN; nlinarith
      have : ε / ((N : ℝ) + 1) * a < r j - b := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hN1]; linarith
      linarith
  have := tendsto_measure_iUnion_atTop (μ := G) hmono
  rw [hU] at this
  exact (ENNReal.tendsto_toReal (measure_ne_top G _)).comp this

/-- Decreasing-threshold limit: if `b > 0` and there is no atom at `b`,
`P(R^j > b − a ε/(n+1)) → P(R^j > b)`. -/
lemma tendsto_down {n : ℕ} (j : Fin n) (b a ε : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (G : Measure (Fin n → ℝ)) [IsProbabilityMeasure G] (hatom : G {r | r j = b} = 0) :
    Tendsto (fun N : ℕ => (G {r | b + -(ε / ((N : ℝ) + 1) * a) < r j}).toReal) atTop
      (𝓝 ((G {r | b < r j}).toReal)) := by
  set s : ℕ → Set (Fin n → ℝ) := fun N => {r | b + -(ε / ((N : ℝ) + 1) * a) < r j}
  have hanti : Antitone s := by
    intro N M hNM r hr
    simp only [s, Set.mem_setOf_eq] at hr ⊢
    have : ε / ((M : ℝ) + 1) ≤ ε / ((N : ℝ) + 1) := by
      apply div_le_div_of_nonneg_left hε.le (by positivity)
      have : (N : ℝ) ≤ M := by exact_mod_cast hNM
      linarith
    nlinarith
  have hI : (⋂ N, s N) = {r | b ≤ r j} := by
    ext r
    simp only [s, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h
      by_contra hlt
      push Not at hlt
      obtain ⟨N, hN⟩ := exists_nat_gt (ε * a / (b - r j))
      have hd : 0 < b - r j := by linarith
      have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have : ε * a < (b - r j) * ((N : ℝ) + 1) := by
        rw [div_lt_iff₀ hd] at hN; nlinarith
      have : ε / ((N : ℝ) + 1) * a < b - r j := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hN1]; linarith
      have := h N
      linarith
    · intro hr N
      have : 0 < ε / ((N : ℝ) + 1) * a := by positivity
      linarith
  have hmeas : ∀ N, NullMeasurableSet (s N) G := fun N =>
    (measurableSet_lt measurable_const (measurable_pi_apply j)).nullMeasurableSet
  have := tendsto_measure_iInter_atTop (μ := G) hmeas hanti ⟨0, measure_ne_top G _⟩
  rw [hI] at this
  have heq : G {r | b ≤ r j} = G {r | b < r j} := by
    apply le_antisymm
    · have hsub : {r : Fin n → ℝ | b ≤ r j} ⊆ {r | b < r j} ∪ {r | r j = b} := by
        intro r hr
        simp only [Set.mem_setOf_eq] at hr
        rcases hr.lt_or_eq with h | h
        · exact Or.inl h
        · exact Or.inr h.symm
      calc G {r | b ≤ r j} ≤ G ({r | b < r j} ∪ {r | r j = b}) := measure_mono hsub
        _ ≤ G {r | b < r j} + G {r | r j = b} := measure_union_le _ _
        _ = G {r | b < r j} := by rw [hatom, add_zero]
    · exact measure_mono fun r (hr : b < r j) => le_of_lt hr
  rw [heq] at this
  exact (ENNReal.tendsto_toReal (measure_ne_top G _)).comp this

end Aux_BPC_kt

open BidPriceControl.Asymptotic in
theorem solution {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (μstar : Fin m → ℝ) (hmin : IsRelaxedMinimizer A F k x μstar) (i : Fin m) :
    ∑ t ∈ Finset.Icc 1 k, ∑ j, exceedProb A F μstar t j * (A i j : ℝ) ≤ (x i : ℝ) ∧
      μstar i * ((x i : ℝ) - ∑ t ∈ Finset.Icc 1 k, ∑ j, exceedProb A F μstar t j * (A i j : ℝ))
        = 0 := by
  set b := bidSum A μstar with hb
  have hμi : 0 ≤ μstar i := hmin.1 i
  set a : Fin n → ℝ := fun j => (A i j : ℝ) with ha
  have ha0 : ∀ j, 0 ≤ a j := fun j => Nat.cast_nonneg _
  set I : ℕ → Fin n → ℝ := fun t j => ∫ r, max (r j - b j) 0 ∂(F t) with hI
  -- `D h` : the perturbed demand on leg `i`
  -- Step 1: for every h > 0, Σ Σ P(R > b + h a) a ≤ x_i
  have hup : ∀ h : ℝ, 0 < h →
      ∑ t ∈ Finset.Icc 1 k, ∑ j, (F t {r | b j + h * a j < r j}).toReal * a j ≤ (x i : ℝ) := by
    intro h hh
    have hle := hmin.2 (Aux_BPC_kt.pert μstar i h)
      (Aux_BPC_kt.pert_nonneg μstar hmin.1 i h (by linarith))
    rw [Aux_BPC_kt.relaxed_pert] at hle
    unfold relaxedValue at hle
    have hsum : ∑ t ∈ Finset.Icc 1 k, ∑ j, ∫ r, max (r j - (b j + h * a j)) 0 ∂(F t)
        ≤ ∑ t ∈ Finset.Icc 1 k, ∑ j, (I t j - h * ((F t {r | b j + h * a j < r j}).toReal * a j)) := by
      apply Finset.sum_le_sum; intro t ht
      apply Finset.sum_le_sum; intro j _
      have := Aux_BPC_kt.int_up j (b j) (h * a j) (mul_nonneg hh.le (ha0 j)) (F t) (hF t ht)
      simp only [hI]
      nlinarith
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    have : h * ∑ t ∈ Finset.Icc 1 k, ∑ j, (F t {r | b j + h * a j < r j}).toReal * a j
        ≤ h * (x i : ℝ) := by
      simp only [hI] at hsum
      linarith
    exact le_of_mul_le_mul_left this hh
  -- the limit h → 0+
  have hD1 : ∑ t ∈ Finset.Icc 1 k, ∑ j, exceedProb A F μstar t j * (A i j : ℝ) ≤ (x i : ℝ) := by
    have hT : Tendsto (fun N : ℕ => ∑ t ∈ Finset.Icc 1 k, ∑ j,
        (F t {r | b j + 1 / ((N : ℝ) + 1) * a j < r j}).toReal * a j) atTop
        (𝓝 (∑ t ∈ Finset.Icc 1 k, ∑ j, exceedProb A F μstar t j * (A i j : ℝ))) := by
      apply tendsto_finset_sum; intro t ht
      apply tendsto_finset_sum; intro j _
      haveI := (hF t ht).isProbabilityMeasure
      exact Aux_BPC_kt.tendsto_up j (b j) (a j) 1 (ha0 j) one_pos (F t)
    exact le_of_tendsto' hT fun N => hup _ (by positivity)
  refine ⟨hD1, ?_⟩
  rcases hμi.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
  -- Step 2: μ_i > 0, so downward perturbations are feasible
  have hdown : ∀ h : ℝ, 0 < h → h ≤ μstar i →
      (x i : ℝ) ≤ ∑ t ∈ Finset.Icc 1 k, ∑ j,
        (F t {r | b j + -(h * a j) < r j}).toReal * a j := by
    intro h hh hhμ
    have hle := hmin.2 (Aux_BPC_kt.pert μstar i (-h))
      (Aux_BPC_kt.pert_nonneg μstar hmin.1 i (-h) (by linarith))
    rw [Aux_BPC_kt.relaxed_pert] at hle
    unfold relaxedValue at hle
    have hsum : ∑ t ∈ Finset.Icc 1 k, ∑ j, ∫ r, max (r j - (b j + -h * a j)) 0 ∂(F t)
        ≤ ∑ t ∈ Finset.Icc 1 k, ∑ j,
            (I t j + h * ((F t {r | b j + -(h * a j) < r j}).toReal * a j)) := by
      apply Finset.sum_le_sum; intro t ht
      apply Finset.sum_le_sum; intro j _
      have := Aux_BPC_kt.int_down j (b j) (h * a j) (mul_nonneg hh.le (ha0 j)) (F t) (hF t ht)
      simp only [hI, neg_mul]
      nlinarith
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have : h * (x i : ℝ) ≤
        h * ∑ t ∈ Finset.Icc 1 k, ∑ j, (F t {r | b j + -(h * a j) < r j}).toReal * a j := by
      simp only [hI] at hsum
      linarith
    exact le_of_mul_le_mul_left this hh
  have hD2 : (x i : ℝ) ≤ ∑ t ∈ Finset.Icc 1 k, ∑ j, exceedProb A F μstar t j * (A i j : ℝ) := by
    have hT : Tendsto (fun N : ℕ => ∑ t ∈ Finset.Icc 1 k, ∑ j,
        (F t {r | b j + -(μstar i / ((N : ℝ) + 1) * a j) < r j}).toReal * a j) atTop
        (𝓝 (∑ t ∈ Finset.Icc 1 k, ∑ j, exceedProb A F μstar t j * (A i j : ℝ))) := by
      apply tendsto_finset_sum; intro t ht
      apply tendsto_finset_sum; intro j _
      haveI := (hF t ht).isProbabilityMeasure
      rcases (ha0 j).eq_or_lt with hz | hapos
      · have hA : (A i j : ℝ) = 0 := hz.symm
        simp only [ha, hA, mul_zero]
        exact tendsto_const_nhds
      · apply Tendsto.mul_const
        have hbpos : 0 < b j := by
          have h1 : μstar i * a j ≤ b j := by
            simp only [hb, bidSum, ha]
            exact Finset.single_le_sum (f := fun l => μstar l * (A l j : ℝ))
              (fun l _ => mul_nonneg (hmin.1 l) (Nat.cast_nonneg _)) (Finset.mem_univ i)
          nlinarith
        exact Aux_BPC_kt.tendsto_down j (b j) (a j) (μstar i) hapos hpos (F t)
          ((hF t ht).noAtom_pos j (b j) hbpos)
    refine ge_of_tendsto' hT fun N => hdown _ (by positivity) ?_
    rw [div_le_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have : (x i : ℝ) - ∑ t ∈ Finset.Icc 1 k, ∑ j, exceedProb A F μstar t j * (A i j : ℝ) = 0 := by
    linarith
  rw [this, mul_zero]
