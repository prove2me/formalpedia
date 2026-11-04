-- Prove2me | solution 1 for CasinoCPT.Embedding.root_coins_exist
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T07:33:46.323117+00:00
-- url     : https://prove2.me/submissions/e1809f94-0b3b-429a-b48f-4e2714b800be

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

open MeasureTheory ProbabilityTheory CasinoCPT.Embedding

namespace Casino31Coins

attribute [local instance] Classical.propDecidable

/-- rescaling step of the nested-interval construction -/
noncomputable def stepU (p u : ℝ) : ℝ :=
  if p = 0 ∨ p = 1 then u else if u ≤ p then u / p else (u - p) / (1 - p)

/-- coin read off the current uniform: `false` iff `u ≤ p` -/
noncomputable def coinOf (p u : ℝ) : Bool :=
  if p = 0 then true else if p = 1 then false else decide (p < u)

/-- probability of a set of outcomes of a `p`-coin (`p` = probability of `false`) -/
noncomputable def piB (p : ℝ) (A : Set Bool) : ℝ :=
  (if false ∈ A then p else 0) + (if true ∈ A then 1 - p else 0)

lemma measurable_stepU (p : ℝ) : Measurable (stepU p) := by
  unfold stepU
  split_ifs
  · exact measurable_id
  · exact Measurable.ite measurableSet_Iic (measurable_id.div_const p)
      ((measurable_id.sub_const p).div_const (1 - p))

lemma measurable_coinOf (p : ℝ) : Measurable (coinOf p) := by
  unfold coinOf
  split_ifs
  · exact measurable_const
  · exact measurable_const
  · have : (fun u : ℝ => decide (p < u)) = fun u => decide (u ∈ Set.Ioi p) := rfl
    rw [this]
    exact measurable_to_countable' fun b => by
      cases b
      · have : (fun u : ℝ => decide (u ∈ Set.Ioi p)) ⁻¹' {false} = (Set.Ioi p)ᶜ := by
          ext u; simp
        rw [this]; exact measurableSet_Ioi.compl
      · have : (fun u : ℝ => decide (u ∈ Set.Ioi p)) ⁻¹' {true} = Set.Ioi p := by
          ext u; simp
        rw [this]; exact measurableSet_Ioi

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

noncomputable def uSeq (p : ℕ → ℝ) (ξ : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => ξ
  | j + 1 => fun ω => stepU (p j) (uSeq p ξ j ω)

noncomputable def cSeq (p : ℕ → ℝ) (ξ : Ω → ℝ) (j : ℕ) (ω : Ω) : Bool :=
  coinOf (p j) (uSeq p ξ j ω)

lemma meas_uSeq {m : MeasurableSpace Ω} (p : ℕ → ℝ) (ξ : Ω → ℝ) (hξ : Measurable[m] ξ) :
    ∀ j, Measurable[m] (uSeq p ξ j) := by
  intro j
  induction j with
  | zero => exact hξ
  | succ j ih => exact (measurable_stepU (p j)).comp ih

lemma meas_cSeq {m : MeasurableSpace Ω} (p : ℕ → ℝ) (ξ : Ω → ℝ) (hξ : Measurable[m] ξ) (j : ℕ) :
    Measurable[m] (cSeq p ξ j) :=
  (measurable_coinOf (p j)).comp (meas_uSeq p ξ hξ j)

lemma base_cdf (P : Measure Ω) (ξ : Ω → ℝ) (hξ : Measurable ξ)
    (hlaw : P.map ξ = volume.restrict (Set.Icc (0 : ℝ) 1)) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    P.real {ω | ξ ω ≤ y} = y := by
  have : P {ω | ξ ω ≤ y} = ENNReal.ofReal y := by
    have h := congrArg (fun m : Measure ℝ => m (Set.Iic y)) hlaw
    have hI : Set.Iic y ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 y := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hy1⟩
    rw [Measure.map_apply hξ measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
      hI, Real.volume_Icc, sub_zero] at h
    exact h
  rw [measureReal_def, this, ENNReal.toReal_ofReal hy0]

/-- the main CDF identity -/
lemma cdf_formula (P : Measure Ω) [IsFiniteMeasure P] (ξ : Ω → ℝ) (hξ : Measurable ξ)
    (hlaw : P.map ξ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) :
    ∀ (n : ℕ) (A : ℕ → Set Bool) (y : ℝ), 0 ≤ y → y ≤ 1 →
      P.real ({ω | ∀ j < n, cSeq p ξ j ω ∈ A j} ∩ {ω | uSeq p ξ n ω ≤ y}) =
        (∏ j ∈ Finset.range n, piB (p j) (A j)) * y := by
  intro n
  induction n with
  | zero =>
    intro A y hy0 hy1
    simp only [not_lt_zero', IsEmpty.forall_iff, implies_true, Set.setOf_true, Set.univ_inter,
      Finset.range_zero, Finset.prod_empty, one_mul]
    exact base_cdf P ξ hξ hlaw y hy0 hy1
  | succ n ih =>
    intro A y hy0 hy1
    have hum : Measurable (uSeq p ξ n) := meas_uSeq p ξ hξ n
    have hcm : ∀ j, Measurable (cSeq p ξ j) := meas_cSeq p ξ hξ
    set X := {ω | ∀ j < n, cSeq p ξ j ω ∈ A j} with hX
    have hXm : MeasurableSet X := by
      have : X = ⋂ j ∈ Finset.range n, cSeq p ξ j ⁻¹' A j := by
        ext ω; simp [hX]
      rw [this]
      exact Finset.measurableSet_biInter _ fun j _ => hcm j (Set.Finite.measurableSet (Set.toFinite _))
    set K := ∏ j ∈ Finset.range n, piB (p j) (A j) with hK
    have hG : ∀ z, 0 ≤ z → z ≤ 1 → P.real (X ∩ {ω | uSeq p ξ n ω ≤ z}) = K * z :=
      fun z h0 h1 => ih A z h0 h1
    have hsplit : {ω | ∀ j < n + 1, cSeq p ξ j ω ∈ A j} = X ∩ {ω | cSeq p ξ n ω ∈ A n} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hX]
      constructor
      · intro h; exact ⟨fun j hj => h j (by omega), h n (by omega)⟩
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact h1 j h
        · subst h; exact h2
    rw [hsplit, Finset.prod_range_succ, ← hK]
    set q := p n with hq
    have hu1 : ∀ ω, uSeq p ξ (n + 1) ω = stepU q (uSeq p ξ n ω) := fun ω => rfl
    have hc : ∀ ω, cSeq p ξ n ω = coinOf q (uSeq p ξ n ω) := fun ω => rfl
    by_cases hdeg : q = 0 ∨ q = 1
    · -- degenerate coin: constant, u unchanged
      have hu1' : ∀ ω, uSeq p ξ (n + 1) ω = uSeq p ξ n ω := by
        intro ω; rw [hu1]; unfold stepU; rw [if_pos hdeg]
      have hconst : ∀ ω, cSeq p ξ n ω = (if q = 0 then true else false) := by
        intro ω; rw [hc]; unfold coinOf
        rcases hdeg with h | h
        · simp [h]
        · have : q ≠ 0 := by rw [h]; norm_num
          simp [this, h]
      have hpi : piB q (A n) = if (if q = 0 then true else false) ∈ A n then 1 else 0 := by
        unfold piB
        rcases hdeg with h | h <;> rw [h] <;>
          by_cases h1 : false ∈ A n <;> by_cases h2 : true ∈ A n <;> simp [h1, h2]
      rw [hpi]
      by_cases hm : (if q = 0 then true else false) ∈ A n
      · have e : X ∩ {ω | cSeq p ξ n ω ∈ A n} ∩ {ω | uSeq p ξ (n + 1) ω ≤ y} =
            X ∩ {ω | uSeq p ξ n ω ≤ y} := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hconst, hu1']
          tauto
        rw [e, hG y hy0 hy1, if_pos hm]; ring
      · have e : X ∩ {ω | cSeq p ξ n ω ∈ A n} ∩ {ω | uSeq p ξ (n + 1) ω ≤ y} = ∅ := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hconst, Set.mem_empty_iff_false,
            iff_false]
          tauto
        rw [e, if_neg hm]; simp
    · -- genuine coin
      push_neg at hdeg
      have hq0 : 0 < q := lt_of_le_of_ne (hp n).1 (Ne.symm hdeg.1)
      have hq1 : q < 1 := lt_of_le_of_ne (hp n).2 hdeg.2
      have hstep : ∀ u, stepU q u = if u ≤ q then u / q else (u - q) / (1 - q) := by
        intro u; unfold stepU; rw [if_neg (by tauto)]
      have hcoin : ∀ u, coinOf q u = decide (q < u) := by
        intro u; unfold coinOf; rw [if_neg hdeg.1, if_neg hdeg.2]
      -- false part
      have hF : {ω | cSeq p ξ n ω = false} ∩ {ω | uSeq p ξ (n + 1) ω ≤ y} =
          {ω | uSeq p ξ n ω ≤ q * y} := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hc, hu1, hcoin, hstep,
          decide_eq_false_iff_not, not_lt]
        constructor
        · rintro ⟨h1, h2⟩
          rw [if_pos h1, div_le_iff₀ hq0] at h2; linarith
        · intro h
          have h1 : uSeq p ξ n ω ≤ q := le_trans h (by nlinarith)
          refine ⟨h1, ?_⟩
          rw [if_pos h1, div_le_iff₀ hq0]; linarith
      have hT : {ω | cSeq p ξ n ω = true} ∩ {ω | uSeq p ξ (n + 1) ω ≤ y} =
          {ω | uSeq p ξ n ω ≤ q + (1 - q) * y} \ {ω | uSeq p ξ n ω ≤ q} := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_diff, hc, hu1, hcoin, hstep,
          decide_eq_true_eq, not_le]
        constructor
        · rintro ⟨h1, h2⟩
          rw [if_neg (not_le.mpr h1), div_le_iff₀ (by linarith)] at h2
          exact ⟨by linarith, h1⟩
        · rintro ⟨h2, h1⟩
          refine ⟨h1, ?_⟩
          rw [if_neg (not_le.mpr h1), div_le_iff₀ (by linarith)]; linarith
      have hmF : MeasurableSet {ω | uSeq p ξ n ω ≤ q * y} := hum measurableSet_Iic
      have hmT1 : MeasurableSet {ω | uSeq p ξ n ω ≤ q + (1 - q) * y} := hum measurableSet_Iic
      have hmT2 : MeasurableSet {ω | uSeq p ξ n ω ≤ q} := hum measurableSet_Iic
      have PF : P.real (X ∩ {ω | uSeq p ξ n ω ≤ q * y}) = K * (q * y) :=
        hG _ (by positivity) (by nlinarith)
      have PT : P.real (X ∩ ({ω | uSeq p ξ n ω ≤ q + (1 - q) * y} \ {ω | uSeq p ξ n ω ≤ q})) =
          K * ((1 - q) * y) := by
        have hsub : X ∩ {ω | uSeq p ξ n ω ≤ q} ⊆ X ∩ {ω | uSeq p ξ n ω ≤ q + (1 - q) * y} := by
          intro ω ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          simp only [Set.mem_setOf_eq] at h2 ⊢
          nlinarith
        rw [Set.inter_diff_distrib_left, measureReal_diff hsub (hXm.inter hmT2),
          hG _ (by nlinarith) (by nlinarith), hG _ hq0.le hq1.le]
        ring
      have hdisj : Disjoint (X ∩ {ω | uSeq p ξ n ω ≤ q * y})
          (X ∩ ({ω | uSeq p ξ n ω ≤ q + (1 - q) * y} \ {ω | uSeq p ξ n ω ≤ q})) := by
        rw [Set.disjoint_left]
        rintro ω ⟨_, h1⟩ ⟨_, _, h3⟩
        simp only [Set.mem_setOf_eq] at h1 h3
        exact h3 (le_trans h1 (by nlinarith))
      have PFT : P.real ((X ∩ {ω | uSeq p ξ n ω ≤ q * y}) ∪
          (X ∩ ({ω | uSeq p ξ n ω ≤ q + (1 - q) * y} \ {ω | uSeq p ξ n ω ≤ q}))) =
          K * (q * y) + K * ((1 - q) * y) := by
        rw [measureReal_union hdisj ((hXm.inter hmT1).diff (hXm.inter hmT2) |> fun h => by
          rw [Set.inter_diff_distrib_left]; exact h), PF, PT]
      have eF : X ∩ {ω | cSeq p ξ n ω = false} ∩ {ω | uSeq p ξ (n + 1) ω ≤ y} =
          X ∩ {ω | uSeq p ξ n ω ≤ q * y} := by
        rw [Set.inter_assoc, hF]
      have eT : X ∩ {ω | cSeq p ξ n ω = true} ∩ {ω | uSeq p ξ (n + 1) ω ≤ y} =
          X ∩ ({ω | uSeq p ξ n ω ≤ q + (1 - q) * y} \ {ω | uSeq p ξ n ω ≤ q}) := by
        rw [Set.inter_assoc, hT]
      unfold piB
      by_cases hf : false ∈ A n <;> by_cases ht : true ∈ A n
      · have hA : {ω | cSeq p ξ n ω ∈ A n} =
            {ω | cSeq p ξ n ω = false} ∪ {ω | cSeq p ξ n ω = true} := by
          ext ω; simp only [Set.mem_setOf_eq, Set.mem_union]
          cases cSeq p ξ n ω <;> simp_all
        rw [hA, Set.inter_union_distrib_left, Set.union_inter_distrib_right, eF, eT, PFT,
          if_pos hf, if_pos ht]
        ring
      · have hA : {ω | cSeq p ξ n ω ∈ A n} = {ω | cSeq p ξ n ω = false} := by
          ext ω; simp only [Set.mem_setOf_eq]
          cases cSeq p ξ n ω <;> simp_all
        rw [hA, eF, PF, if_pos hf, if_neg ht]; ring
      · have hA : {ω | cSeq p ξ n ω ∈ A n} = {ω | cSeq p ξ n ω = true} := by
          ext ω; simp only [Set.mem_setOf_eq]
          cases cSeq p ξ n ω <;> simp_all
        rw [hA, eT, PT, if_neg hf, if_pos ht]; ring
      · have hA : {ω | cSeq p ξ n ω ∈ A n} = ∅ := by
          ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          cases cSeq p ξ n ω <;> simp_all
        rw [hA, if_neg hf, if_neg ht]; simp

lemma piB_univ (q : ℝ) : piB q Set.univ = 1 := by unfold piB; simp

lemma piB_nonneg (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) (A : Set Bool) : 0 ≤ piB q A := by
  unfold piB; split_ifs <;> linarith [hq.1, hq.2]

lemma joint_formula (P : Measure Ω) [IsProbabilityMeasure P] (ξ : Ω → ℝ) (hξ : Measurable ξ)
    (hlaw : P.map ξ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (n : ℕ) (A : ℕ → Set Bool) :
    P.real {ω | ∀ j < n, cSeq p ξ j ω ∈ A j} = ∏ j ∈ Finset.range n, piB (p j) (A j) := by
  have hB := cdf_formula P ξ hξ hlaw p hp n (fun _ => Set.univ) 1 zero_le_one le_rfl
  simp only [Set.mem_univ, implies_true, Set.setOf_true, Set.univ_inter, piB_univ,
    Finset.prod_const_one, mul_one] at hB
  have hum : Measurable (uSeq p ξ n) := meas_uSeq p ξ hξ n
  have hBm : MeasurableSet {ω | uSeq p ξ n ω ≤ 1} := hum measurableSet_Iic
  have hnull : P {ω | uSeq p ξ n ω ≤ 1}ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff hBm]
    rw [measureReal_def] at hB
    have := (ENNReal.toReal_eq_one_iff _).mp hB
    exact this
  have h := cdf_formula P ξ hξ hlaw p hp n A 1 zero_le_one le_rfl
  rw [mul_one] at h
  rw [← h, measureReal_def, measureReal_def, measure_inter_conull hnull]

lemma marginal (P : Measure Ω) [IsProbabilityMeasure P] (ξ : Ω → ℝ) (hξ : Measurable ξ)
    (hlaw : P.map ξ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (i : ℕ) (B : Set Bool) :
    P.real {ω | cSeq p ξ i ω ∈ B} = piB (p i) B := by
  have h := joint_formula P ξ hξ hlaw p hp (i + 1) (fun j => if j = i then B else Set.univ)
  have e : {ω | ∀ j < i + 1, cSeq p ξ j ω ∈ (if j = i then B else Set.univ)} =
      {ω | cSeq p ξ i ω ∈ B} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h; have := h i (by omega); simpa using this
    · intro h j _; split_ifs with hj
      · subst hj; exact h
      · exact Set.mem_univ _
  rw [e] at h
  rw [h, Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp only [hj, if_false]; exact piB_univ _
  · intro hi; simp at hi

lemma indep_coins (P : Measure Ω) [IsProbabilityMeasure P] (ξ : Ω → ℝ) (hξ : Measurable ξ)
    (hlaw : P.map ξ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) :
    iIndepFun (fun j => cSeq p ξ j) P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  set n := S.sup id + 1
  have hSn : ∀ i ∈ S, i < n := by
    intro i hi
    have : i ≤ S.sup id := Finset.le_sup (f := id) hi
    omega
  let A : ℕ → Set Bool := fun j => if j ∈ S then sets j else Set.univ
  have e : (⋂ i ∈ S, cSeq p ξ i ⁻¹' sets i) = {ω | ∀ j < n, cSeq p ξ j ω ∈ A j} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq, A]
    constructor
    · intro h j _; split_ifs with hj
      · exact h j hj
      · exact Set.mem_univ _
    · intro h i hi; have := h i (hSn i hi); simpa [hi] using this
  rw [e, ← ofReal_measureReal, joint_formula P ξ hξ hlaw p hp n A]
  have hprod : ∏ j ∈ Finset.range n, piB (p j) (A j) = ∏ j ∈ S, piB (p j) (sets j) := by
    rw [← Finset.prod_subset (s₁ := S) (fun i hi => Finset.mem_range.mpr (hSn i hi))]
    · apply Finset.prod_congr rfl; intro j hj; simp [A, hj]
    · intro j _ hj; simp only [A, hj, if_false]; exact piB_univ _
  rw [hprod, ENNReal.ofReal_prod_of_nonneg (fun j _ => piB_nonneg _ (hp j) _)]
  apply Finset.prod_congr rfl
  intro j _
  rw [← marginal P ξ hξ hlaw p hp j (sets j), ofReal_measureReal]
  rfl

end Casino31Coins

open Casino31Coins

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ) (hS : IsCasinoSpace P F S ξ)
    (b : ℤ → ℕ) (r : ℤ → ℝ) (hr : ∀ x, 0 ≤ r x ∧ r x ≤ 1) :
    ∃ coin : ℕ → ℤ → Ω → Bool, IsRootCoins P F b r coin ∧
      (∀ t x ω, t < b x → coin t x ω = true) ∧
      (∀ t x ω, b x < t → coin t x ω = false) ∧
      (∀ x ω, r x = 1 → coin (b x) x ω = false) := by
  have hP := hS.isProb
  let e : ℕ × ℤ ≃ ℕ := Denumerable.eqv (ℕ × ℤ)
  let law : ℕ × ℤ → ℝ := fun q => if q.1 < b q.2 then 0 else if q.1 = b q.2 then r q.2 else 1
  let pp : ℕ → ℝ := fun k => law (e.symm k)
  have hpp : ∀ k, 0 ≤ pp k ∧ pp k ≤ 1 := by
    intro k; simp only [pp, law]
    split_ifs
    · norm_num
    · exact hr _
    · norm_num
  have hpp' : ∀ t x, pp (e (t, x)) = law (t, x) := by
    intro t x; simp only [pp, Equiv.symm_apply_apply]
  have hξ0 : Measurable[F 0] ξ := hS.unif_meas
  have hξ : Measurable ξ := hξ0.mono (F.le 0) le_rfl
  refine ⟨fun t x => cSeq pp ξ (e (t, x)), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro t x; exact meas_cSeq pp ξ hξ0 _
  · have := indep_coins P ξ hξ hS.unif_law pp hpp
    exact this.precomp (g := fun q : ℕ × ℤ => e (q.1, q.2)) (fun q1 q2 h => by
      have := e.injective h; exact Prod.ext (congrArg Prod.fst this) (congrArg Prod.snd this))
  · intro t x
    have h := marginal P ξ hξ hS.unif_law pp hpp (e (t, x)) {false}
    rw [measureReal_def] at h
    simp only [Set.mem_singleton_iff] at h
    rw [h, hpp']
    unfold piB; simp [law]
  · intro t x ω h
    show coinOf _ _ = true
    rw [hpp']; unfold coinOf; simp [law, h]
  · intro t x ω h
    show coinOf _ _ = false
    rw [hpp']; unfold coinOf
    have h1 : ¬ t < b x := by omega
    have h2 : t ≠ b x := by omega
    simp [law, h1, h2]
  · intro x ω h
    show coinOf _ _ = false
    rw [hpp']; unfold coinOf; simp [law, h]
