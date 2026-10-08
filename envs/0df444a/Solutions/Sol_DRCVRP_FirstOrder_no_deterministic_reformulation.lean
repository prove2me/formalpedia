-- Prove2me | solution 1 for DRCVRP.FirstOrder.no_deterministic_reformulation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T15:22:06.667571+00:00
-- url     : https://prove2.me/submissions/a575195b-6bc3-4025-92ec-b8b46b9091de

import Mathlib
import Definitions.Def_DRCVRP_FirstOrder_AmbiguitySet
import Definitions.Def_DRCVRP_FirstOrder_RouteSet

open MeasureTheory


namespace DRCVRP.FirstOrder

noncomputable section

def foLo : Fin 4 → ℝ := ![0, 0, 1, 1]
def foHi : Fin 4 → ℝ := ![2, 2, 3/2, 3/2]
def foMu : Fin 4 → ℝ := ![1, 1, 5/4, 5/4]
def foS : Fin 1 → Finset (Fin 4) := fun _ => {0, 1}
def foNu : Fin 1 → ℝ := fun _ => 2/3

abbrev foAmb : Set (Measure (Fin 4 → ℝ)) := firstOrderAmbiguitySet foLo foHi foMu foS foNu

def foTwo (a b : Fin 4 → ℝ) : Measure (Fin 4 → ℝ) :=
  (2⁻¹ : ENNReal) • (Measure.dirac a + Measure.dirac b)

lemma fo_int (a b : Fin 4 → ℝ) (f : (Fin 4 → ℝ) → ℝ) :
    ∫ q, f q ∂(foTwo a b) = 2⁻¹ * (f a + f b) := by
  unfold foTwo
  rw [integral_smul_measure, integral_add_measure, integral_dirac, integral_dirac]
  · simp
  · exact integrable_dirac (by simp)
  · exact integrable_dirac (by simp)

lemma fo_integrable (a b : Fin 4 → ℝ) (f : (Fin 4 → ℝ) → ℝ) : Integrable f (foTwo a b) := by
  unfold foTwo
  refine Integrable.smul_measure ?_ (by simp)
  exact (integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))

lemma fo_meas (a b : Fin 4 → ℝ) (s : Set (Fin 4 → ℝ)) :
    foTwo a b s = 2⁻¹ * (s.indicator 1 a + s.indicator 1 b) := by
  unfold foTwo
  simp [Measure.dirac_apply, mul_add]

lemma fo_half : (2⁻¹ : ENNReal) * (1 + 1) = 1 := by
  rw [one_add_one_eq_two]; exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

lemma fo_mem (a b : Fin 4 → ℝ) (ha : a ∈ Set.Icc foLo foHi) (hb : b ∈ Set.Icc foLo foHi)
    (hm : ∀ j, 2⁻¹ * (a j + b j) = foMu j)
    (hn : 2⁻¹ * ((|a 0 - 1| + |a 1 - 1|) + (|b 0 - 1| + |b 1 - 1|)) ≤ 2/3) :
    foTwo a b ∈ foAmb := by
  refine ⟨⟨?_⟩, ?_, ?_, ?_⟩
  · rw [fo_meas]; simp
    exact fo_half
  · rw [fo_meas]
    simp [Set.indicator_of_mem ha, Set.indicator_of_mem hb]
    exact fo_half
  · intro j; exact ⟨fo_integrable _ _ _, by rw [fo_int]; exact hm j⟩
  · intro l
    refine ⟨fo_integrable _ _ _, ?_⟩
    rw [fo_int]
    simpa [foS, foNu, foMu] using hn

def foX0 : Fin 4 → ℝ := ![8/5, 1, 3/2, 3/2]
def foY0 : Fin 4 → ℝ := ![2/5, 1, 1, 1]
def foX1 : Fin 4 → ℝ := ![1, 8/5, 3/2, 3/2]
def foY1 : Fin 4 → ℝ := ![1, 2/5, 1, 1]

lemma fo_box (v : Fin 4 → ℝ) (h : ∀ j, foLo j ≤ v j ∧ v j ≤ foHi j) : v ∈ Set.Icc foLo foHi :=
  ⟨fun j => (h j).1, fun j => (h j).2⟩

lemma fo_mem0 : foTwo foX0 foY0 ∈ foAmb := by
  apply fo_mem
  · apply fo_box; intro j; fin_cases j <;> simp [foX0, foLo, foHi] <;> norm_num
  · apply fo_box; intro j; fin_cases j <;> simp [foY0, foLo, foHi] <;> norm_num
  · intro j; fin_cases j <;> simp [foX0, foY0, foMu] <;> norm_num
  · simp [foX0, foY0]; rw [abs_of_pos (by norm_num), abs_of_neg (by norm_num)]; norm_num

lemma fo_mem1 : foTwo foX1 foY1 ∈ foAmb := by
  apply fo_mem
  · apply fo_box; intro j; fin_cases j <;> simp [foX1, foLo, foHi] <;> norm_num
  · apply fo_box; intro j; fin_cases j <;> simp [foY1, foLo, foHi] <;> norm_num
  · intro j; fin_cases j <;> simp [foX1, foY1, foMu] <;> norm_num
  · simp [foX1, foY1]; rw [abs_of_pos (by norm_num), abs_of_neg (by norm_num)]; norm_num

lemma fo_bad (a b : Fin 4 → ℝ) (i j : Fin 4) (h1 : 3 < a i + a j) (h2 : b i + b j ≤ 3) :
    foTwo a b {q | q i + q j ≤ 3} < ENNReal.ofReal (1 - 1/3) := by
  rw [fo_meas]
  have hn : a ∉ {q : Fin 4 → ℝ | q i + q j ≤ 3} := by simpa using h1
  have hm : b ∈ {q : Fin 4 → ℝ | q i + q j ≤ 3} := h2
  rw [Set.indicator_of_notMem hn, Set.indicator_of_mem hm]
  simp only [Pi.one_apply, zero_add, mul_one]
  rw [show (1:ℝ) - 1/3 = 2/3 by norm_num, ENNReal.lt_ofReal_iff_toReal_lt (by simp)]
  simp; norm_num

lemma fo_ae (P : Measure (Fin 4 → ℝ)) (hP : P ∈ foAmb) :
    ∀ᵐ q ∂P, q ∈ Set.Icc foLo foHi := by
  obtain ⟨hprob, hbox, -, -⟩ := hP
  rw [ae_iff]
  have := (prob_compl_eq_zero_iff (μ := P) measurableSet_Icc).2 hbox
  simpa [Set.compl_def] using this

lemma fo_box_le (P : Measure (Fin 4 → ℝ)) (hP : P ∈ foAmb) (s : Set (Fin 4 → ℝ))
    (hs : Set.Icc foLo foHi ⊆ s) : ENNReal.ofReal (1 - 1/3) ≤ P s := by
  have hbox := hP.2.1
  calc ENNReal.ofReal (1 - 1/3) ≤ 1 := by rw [ENNReal.ofReal_le_one]; norm_num
    _ = P (Set.Icc foLo foHi) := hbox.symm
    _ ≤ _ := measure_mono hs

lemma fo_markov (P : Measure (Fin 4 → ℝ)) (hP : P ∈ foAmb) :
    ENNReal.ofReal (1 - 1/3) ≤ P {q | q 0 + q 1 ≤ 3} := by
  obtain ⟨hprob, -, hmean, hnu⟩ := hP
  obtain ⟨hi0, he0⟩ := hmean 0
  obtain ⟨hi1, he1⟩ := hmean 1
  obtain ⟨hig, heg⟩ := hnu 0
  have hY : Integrable (fun q : Fin 4 → ℝ => q 0 + q 1 - 2) P :=
    (hi0.add hi1).sub (integrable_const _)
  have hYp : Integrable (fun q : Fin 4 → ℝ => max (q 0 + q 1 - 2) 0) P := hY.pos_part
  have hYint : ∫ q, (q 0 + q 1 - 2) ∂P = 0 := by
    rw [integral_sub (f := fun q : Fin 4 → ℝ => q 0 + q 1) (hi0.add hi1) (integrable_const _),
      integral_add hi0 hi1, he0, he1]
    simp [foMu]; norm_num
  have hpt : ∀ q : Fin 4 → ℝ, 2 * max (q 0 + q 1 - 2) 0 ≤
      (q 0 + q 1 - 2) + ∑ j ∈ foS 0, |q j - foMu j| := by
    intro q
    simp only [foS, foMu]
    rw [Finset.sum_pair (by decide)]
    simp
    have := abs_le.1 (le_refl |q 0 - 1|)
    have := abs_le.1 (le_refl |q 1 - 1|)
    rcases le_total (q 0 + q 1 - 2) 0 with h | h
    · rw [max_eq_right h]; linarith [abs_nonneg (q 0 - 1), abs_nonneg (q 1 - 1),
        neg_abs_le (q 0 - 1), neg_abs_le (q 1 - 1), le_abs_self (q 0 - 1), le_abs_self (q 1 - 1)]
    · rw [max_eq_left h]; linarith [le_abs_self (q 0 - 1), le_abs_self (q 1 - 1)]
  have hmono := integral_mono (hYp.const_mul 2) (hY.add hig) hpt
  rw [integral_const_mul] at hmono
  have hadd : ∫ x, ((fun q : Fin 4 → ℝ => q 0 + q 1 - 2) + fun q : Fin 4 → ℝ => ∑ j ∈ foS 0, |q j - foMu j|) x ∂P
      = ∫ q : Fin 4 → ℝ, (q 0 + q 1 - 2) ∂P + ∫ q : Fin 4 → ℝ, ∑ j ∈ foS 0, |q j - foMu j| ∂P := integral_add hY hig
  rw [hadd, hYint] at hmono
  have hnu0 : foNu 0 = 2/3 := rfl
  have hE : ∫ q, max (q 0 + q 1 - 2) 0 ∂P ≤ 1/3 := by linarith
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (f := fun q : Fin 4 → ℝ => max (q 0 + q 1 - 2) 0)
    (Filter.Eventually.of_forall fun q => le_max_right _ _) hYp 1
  rw [one_mul] at hmk
  have hsub : {q : Fin 4 → ℝ | q 0 + q 1 ≤ 3}ᶜ ⊆ {q | 1 ≤ max (q 0 + q 1 - 2) 0} := by
    intro q hq
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hq ⊢
    exact le_max_of_le_left (by linarith)
  have hc : (P {q : Fin 4 → ℝ | q 0 + q 1 ≤ 3}ᶜ).toReal ≤ 1/3 := by
    refine le_trans ?_ (hmk.trans hE)
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hms : MeasurableSet {q : Fin 4 → ℝ | q 0 + q 1 ≤ 3} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hsum := prob_add_prob_compl (μ := P) hms
  rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  have : (P {q : Fin 4 → ℝ | q 0 + q 1 ≤ 3}).toReal +
      (P {q : Fin 4 → ℝ | q 0 + q 1 ≤ 3}ᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hsum]; simp
  linarith

def foR1 : Fin 3 → List (Fin 4) := ![[0, 1], [2], [3]]
def foR2 : Fin 3 → List (Fin 4) := ![[2, 3], [0], [1]]
def foR3 : Fin 3 → List (Fin 4) := ![[0, 2], [1], [3]]
def foR4 : Fin 3 → List (Fin 4) := ![[1, 3], [0], [2]]

lemma foR1_rs : IsRouteSet foR1 := by unfold IsRouteSet foR1; decide
lemma foR2_rs : IsRouteSet foR2 := by unfold IsRouteSet foR2; decide
lemma foR3_rs : IsRouteSet foR3 := by unfold IsRouteSet foR3; decide
lemma foR4_rs : IsRouteSet foR4 := by unfold IsRouteSet foR4; decide

lemma fo_single (P : Measure (Fin 4 → ℝ)) (hP : P ∈ foAmb) (i : Fin 4) :
    ENNReal.ofReal (1 - 1/3) ≤ P {q | q i ≤ 3} := by
  apply fo_box_le P hP
  intro q hq; have := hq.2 i
  simp only [Set.mem_setOf_eq]
  fin_cases i <;> simp [foHi] at this ⊢ <;> linarith

lemma fo_23 (P : Measure (Fin 4 → ℝ)) (hP : P ∈ foAmb) :
    ENNReal.ofReal (1 - 1/3) ≤ P {q | q 2 + q 3 ≤ 3} := by
  apply fo_box_le P hP
  intro q hq; have h2 := hq.2 2; have h3 := hq.2 3
  simp [foHi] at h2 h3
  simp only [Set.mem_setOf_eq]; linarith

lemma foR1_feas : IsRVRPFeasible foAmb (1/3) 3 foR1 := by
  refine ⟨foR1_rs, fun P hP k => ?_⟩
  fin_cases k
  · simpa [foR1] using fo_markov P hP
  · simpa [foR1] using fo_single P hP 2
  · simpa [foR1] using fo_single P hP 3

lemma foR2_feas : IsRVRPFeasible foAmb (1/3) 3 foR2 := by
  refine ⟨foR2_rs, fun P hP k => ?_⟩
  fin_cases k
  · simpa [foR2] using fo_23 P hP
  · simpa [foR2] using fo_single P hP 0
  · simpa [foR2] using fo_single P hP 1

lemma foR3_infeas : ¬ IsRVRPFeasible foAmb (1/3) 3 foR3 := by
  rintro ⟨-, h⟩
  have h1 := h _ fo_mem0 0
  have h2 := fo_bad foX0 foY0 0 2 (by simp [foX0]; norm_num) (by simp [foY0]; norm_num)
  simp [foR3] at h1
  exact absurd h1 (not_le.2 (by simpa using h2))

lemma foR4_infeas : ¬ IsRVRPFeasible foAmb (1/3) 3 foR4 := by
  rintro ⟨-, h⟩
  have h1 := h _ fo_mem1 0
  have h2 := fo_bad foX1 foY1 1 3 (by simp [foX1]; norm_num) (by simp [foY1]; norm_num)
  simp [foR4] at h1
  exact absurd h1 (not_le.2 (by simpa using h2))

end

theorem ndr_core :
    ∃ (n m : ℕ) (Q ε : ℝ) (qlo qhi μ : Fin n → ℝ) (p : ℕ) (Sfam : Fin p → Finset (Fin n))
      (ν : Fin p → ℝ),
      0 < Q ∧ 0 < ε ∧ ε < 1 ∧ (∀ j, 0 ≤ qlo j) ∧ (∀ j, qlo j < μ j ∧ μ j < qhi j) ∧
      (∀ l, 0 < ν l) ∧
      ∀ (Q' : ℝ) (q' : Fin n → ℝ), 0 ≤ Q' → (∀ i, 0 ≤ q' i) →
        {R : Fin m → List (Fin n) |
            IsRVRPFeasible (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε Q R} ≠
          {R : Fin m → List (Fin n) | IsDeterministicFeasible Q' q' R} := by
  refine ⟨4, 3, 3, 1/3, foLo, foHi, foMu, 1, foS, foNu, by norm_num, by norm_num, by norm_num,
    fun j => by fin_cases j <;> simp [foLo], fun j => by
      fin_cases j <;> simp [foLo, foHi, foMu] <;> norm_num, fun l => by simp [foNu], ?_⟩
  intro Q' q hQ' hq hEq
  have d1 : IsDeterministicFeasible Q' q foR1 := by
    have : foR1 ∈ {R : Fin 3 → List (Fin 4) | IsRVRPFeasible foAmb (1/3) 3 R} := foR1_feas
    rw [hEq] at this; exact this
  have d2 : IsDeterministicFeasible Q' q foR2 := by
    have : foR2 ∈ {R : Fin 3 → List (Fin 4) | IsRVRPFeasible foAmb (1/3) 3 R} := foR2_feas
    rw [hEq] at this; exact this
  have n3 : ¬ IsDeterministicFeasible Q' q foR3 := by
    intro h
    have : foR3 ∈ {R : Fin 3 → List (Fin 4) | IsDeterministicFeasible Q' q R} := h
    rw [← hEq] at this; exact foR3_infeas this
  have n4 : ¬ IsDeterministicFeasible Q' q foR4 := by
    intro h
    have : foR4 ∈ {R : Fin 3 → List (Fin 4) | IsDeterministicFeasible Q' q R} := h
    rw [← hEq] at this; exact foR4_infeas this
  have a1 := d1.2 0; have a2 := d2.2 0
  simp [foR1, foR2] at a1 a2
  have h0 := hq 0; have h1 := hq 1; have h2 := hq 2; have h3 := hq 3
  have c3 : Q' < q 0 + q 2 := by
    by_contra hc; push_neg at hc
    exact n3 ⟨foR3_rs, fun k => by fin_cases k <;> simp [foR3] <;> linarith⟩
  have c4 : Q' < q 1 + q 3 := by
    by_contra hc; push_neg at hc
    exact n4 ⟨foR4_rs, fun k => by fin_cases k <;> simp [foR4] <;> linarith⟩
  linarith


end DRCVRP.FirstOrder

open DRCVRP.FirstOrder


theorem solution :
    ∃ (n m : ℕ) (Q ε : ℝ) (qlo qhi μ : Fin n → ℝ) (p : ℕ) (Sfam : Fin p → Finset (Fin n))
      (ν : Fin p → ℝ),
      0 < Q ∧ 0 < ε ∧ ε < 1 ∧ (∀ j, 0 ≤ qlo j) ∧ (∀ j, qlo j < μ j ∧ μ j < qhi j) ∧
      (∀ l, 0 < ν l) ∧
      ∀ (Q' : ℝ) (q' : Fin n → ℝ), 0 ≤ Q' → (∀ i, 0 ≤ q' i) →
        {R : Fin m → List (Fin n) |
            IsRVRPFeasible (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε Q R} ≠
          {R : Fin m → List (Fin n) | IsDeterministicFeasible Q' q' R} := by
  exact ndr_core
