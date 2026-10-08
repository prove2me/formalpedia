-- Prove2me | solution 1 for DRCVRP.Covariance.no_deterministic_reformulation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T14:58:52.218191+00:00
-- url     : https://prove2.me/submissions/77a5073a-daa2-4f8c-ae43-bcf23458771e

import Mathlib
import Definitions.Def_DRCVRP_Covariance_AmbiguitySet
import Definitions.Def_DRCVRP_Covariance_Routing

open MeasureTheory


namespace DRCVRP.Covariance

open Matrix

noncomputable section

def ndrV : Fin 4 → ℝ := ![1, -1, 1, -1]
def ndrSg : Matrix (Fin 4) (Fin 4) ℝ := vecMulVec ndrV ndrV + (1/16 : ℝ) • 1
def ndrLo : Fin 4 → ℝ := fun _ => 0
def ndrHi : Fin 4 → ℝ := fun _ => 2
def ndrMu : Fin 4 → ℝ := fun _ => 1

lemma ndrSg_posDef : ndrSg.PosDef := by
  have h1 : (vecMulVec ndrV ndrV).PosSemidef := by
    have := posSemidef_vecMulVec_self_star ndrV
    rwa [star_trivial] at this
  exact PosDef.posSemidef_add h1 (PosDef.one.smul (by norm_num))

def ndrP1 : Fin 4 → ℝ := ![2, 0, 2, 0]
def ndrP2 : Fin 4 → ℝ := ![0, 2, 0, 2]
def ndrP0 : Measure (Fin 4 → ℝ) := (2⁻¹ : ENNReal) • (Measure.dirac ndrP1 + Measure.dirac ndrP2)

lemma ndr_int (f : (Fin 4 → ℝ) → ℝ) : ∫ q, f q ∂ndrP0 = 2⁻¹ * (f ndrP1 + f ndrP2) := by
  unfold ndrP0
  rw [integral_smul_measure, integral_add_measure, integral_dirac, integral_dirac]
  · simp
  · exact integrable_dirac (by simp)
  · exact integrable_dirac (by simp)

lemma ndr_meas (s : Set (Fin 4 → ℝ)) :
    ndrP0 s = 2⁻¹ * (s.indicator 1 ndrP1 + s.indicator 1 ndrP2) := by
  unfold ndrP0
  simp [Measure.dirac_apply, mul_add]

lemma ndr_half : (2⁻¹ : ENNReal) * (1 + 1) = 1 := by
  rw [one_add_one_eq_two]; exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

lemma ndrP0_mem : ndrP0 ∈ covarianceSet ndrLo ndrHi ndrMu ndrSg := by
  refine ⟨⟨?_⟩, ?_, ?_, ?_⟩
  · rw [ndr_meas]; simp
    exact ndr_half
  · rw [ndr_meas]
    have h1 : ndrP1 ∈ Set.Icc ndrLo ndrHi := by
      constructor <;> intro k <;> fin_cases k <;> simp [ndrP1, ndrLo, ndrHi]
    have h2 : ndrP2 ∈ Set.Icc ndrLo ndrHi := by
      constructor <;> intro k <;> fin_cases k <;> simp [ndrP2, ndrLo, ndrHi]
    simp [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
    exact ndr_half
  · intro j; rw [ndr_int]; fin_cases j <;> simp [ndrP1, ndrP2, ndrMu]
  · have hM : centredSecondMoment ndrMu ndrP0 = vecMulVec ndrV ndrV := by
      funext i j
      unfold centredSecondMoment
      rw [ndr_int]
      fin_cases i <;> fin_cases j <;> simp [ndrP1, ndrP2, ndrMu, ndrV, vecMulVec] <;> norm_num
    rw [hM, ndrSg, add_sub_cancel_left]
    exact PosSemidef.one.smul (by norm_num)

lemma ndr_bad (i j : Fin 4) (h1 : 3 < ndrP1 i + ndrP1 j) (h2 : ndrP2 i + ndrP2 j ≤ 3) :
    ndrP0 {q | q i + q j ≤ 3} < ENNReal.ofReal (1 - 1/4) := by
  rw [ndr_meas]
  have hn : ndrP1 ∉ {q : Fin 4 → ℝ | q i + q j ≤ 3} := by simpa using h1
  have hm : ndrP2 ∈ {q : Fin 4 → ℝ | q i + q j ≤ 3} := h2
  rw [Set.indicator_of_notMem hn, Set.indicator_of_mem hm]
  simp only [Pi.one_apply, zero_add, mul_one]
  rw [show (1:ℝ) - 1/4 = 3/4 by norm_num, ENNReal.lt_ofReal_iff_toReal_lt (by simp)]
  simp; norm_num

lemma ndr_bad2 (i j : Fin 4) (h1 : 3 < ndrP2 i + ndrP2 j) (h2 : ndrP1 i + ndrP1 j ≤ 3) :
    ndrP0 {q | q i + q j ≤ 3} < ENNReal.ofReal (1 - 1/4) := by
  rw [ndr_meas]
  have hn : ndrP2 ∉ {q : Fin 4 → ℝ | q i + q j ≤ 3} := by simpa using h1
  have hm : ndrP1 ∈ {q : Fin 4 → ℝ | q i + q j ≤ 3} := h2
  rw [Set.indicator_of_notMem hn, Set.indicator_of_mem hm]
  simp only [Pi.one_apply, add_zero, mul_one]
  rw [show (1:ℝ) - 1/4 = 3/4 by norm_num, ENNReal.lt_ofReal_iff_toReal_lt (by simp)]
  simp; norm_num

lemma ndr_ae (P : Measure (Fin 4 → ℝ)) (hP : P ∈ covarianceSet ndrLo ndrHi ndrMu ndrSg) :
    ∀ᵐ q ∂P, q ∈ Set.Icc ndrLo ndrHi := by
  obtain ⟨hprob, hbox, -, -⟩ := hP
  rw [ae_iff]
  have := (prob_compl_eq_zero_iff (μ := P) measurableSet_Icc).2 hbox
  simpa [Set.compl_def] using this

lemma ndr_integrable (P : Measure (Fin 4 → ℝ)) (hP : P ∈ covarianceSet ndrLo ndrHi ndrMu ndrSg)
    (i j : Fin 4) : Integrable (fun q : Fin 4 → ℝ => (q i - 1) * (q j - 1)) P := by
  have hprob := hP.1
  refine Integrable.of_bound (C := 1) (by fun_prop) ?_
  filter_upwards [ndr_ae P hP] with q hq
  have hi0 := hq.1 i; have hi2 := hq.2 i; have hj0 := hq.1 j; have hj2 := hq.2 j
  simp only [ndrLo, ndrHi] at hi0 hi2 hj0 hj2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

lemma ndr_markov (P : Measure (Fin 4 → ℝ)) (hP : P ∈ covarianceSet ndrLo ndrHi ndrMu ndrSg)
    (i j : Fin 4)
    (hb : centredSecondMoment ndrMu P i i + centredSecondMoment ndrMu P j j +
      2 * centredSecondMoment ndrMu P i j ≤ 1/8) :
    ENNReal.ofReal (1 - 1/4) ≤ P {q | q i + q j ≤ 3} := by
  have hprob := hP.1
  have hint : ∫ q, (q i + q j - 2) ^ 2 ∂P = centredSecondMoment ndrMu P i i +
      centredSecondMoment ndrMu P j j + 2 * centredSecondMoment ndrMu P i j := by
    have : (fun q : Fin 4 → ℝ => (q i + q j - 2) ^ 2) = fun q =>
        ((q i - 1) * (q i - 1) + (q j - 1) * (q j - 1)) + 2 * ((q i - 1) * (q j - 1)) := by
      funext q; ring
    rw [this, integral_add, integral_add, integral_const_mul]
    · simp [centredSecondMoment, ndrMu]
    all_goals first
      | exact ndr_integrable P hP _ _
      | exact (ndr_integrable P hP _ _).const_mul _
      | exact (ndr_integrable P hP _ _).add (ndr_integrable P hP _ _)
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (f := fun q : Fin 4 → ℝ => (q i + q j - 2) ^ 2) (Filter.Eventually.of_forall fun q => sq_nonneg _)
    (by
      have : (fun q : Fin 4 → ℝ => (q i + q j - 2) ^ 2) = fun q =>
        ((q i - 1) * (q i - 1) + (q j - 1) * (q j - 1)) + 2 * ((q i - 1) * (q j - 1)) := by
        funext q; ring
      rw [this]
      exact ((ndr_integrable P hP _ _).add (ndr_integrable P hP _ _)).add
        ((ndr_integrable P hP _ _).const_mul _)) 1
  rw [hint, one_mul] at hmk
  have hsub : {q : Fin 4 → ℝ | q i + q j ≤ 3}ᶜ ⊆ {q | 1 ≤ (q i + q j - 2) ^ 2} := by
    intro q hq
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hq ⊢
    nlinarith
  have hc : (P {q : Fin 4 → ℝ | q i + q j ≤ 3}ᶜ).toReal ≤ 1/8 := by
    refine le_trans ?_ (hmk.trans hb)
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hms : MeasurableSet {q : Fin 4 → ℝ | q i + q j ≤ 3} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hsum := prob_add_prob_compl (μ := P) hms
  rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  have : (P {q : Fin 4 → ℝ | q i + q j ≤ 3}).toReal +
      (P {q : Fin 4 → ℝ | q i + q j ≤ 3}ᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hsum]; simp
  linarith

lemma ndr_symm (P : Measure (Fin 4 → ℝ)) (i j : Fin 4) :
    centredSecondMoment ndrMu P j i = centredSecondMoment ndrMu P i j := by
  unfold centredSecondMoment; congr 1; funext q; ring

lemma ndr_psd (P : Measure (Fin 4 → ℝ)) (hP : P ∈ covarianceSet ndrLo ndrHi ndrMu ndrSg)
    (x : Fin 4 → ℝ) : 0 ≤ x ⬝ᵥ ((ndrSg - centredSecondMoment ndrMu P) *ᵥ x) := by
  have := hP.2.2.2.dotProduct_mulVec_nonneg x
  simpa using this

lemma ndr_b01 (P : Measure (Fin 4 → ℝ)) (hP : P ∈ covarianceSet ndrLo ndrHi ndrMu ndrSg) :
    centredSecondMoment ndrMu P 0 0 + centredSecondMoment ndrMu P 1 1 +
      2 * centredSecondMoment ndrMu P 0 1 ≤ 1/8 := by
  have h := ndr_psd P hP ![1, 1, 0, 0]
  have hs := ndr_symm P 0 1
  simp [dotProduct, mulVec, Fin.sum_univ_four, ndrSg, ndrV, vecMulVec] at h
  norm_num at h
  linarith

lemma ndr_b23 (P : Measure (Fin 4 → ℝ)) (hP : P ∈ covarianceSet ndrLo ndrHi ndrMu ndrSg) :
    centredSecondMoment ndrMu P 2 2 + centredSecondMoment ndrMu P 3 3 +
      2 * centredSecondMoment ndrMu P 2 3 ≤ 1/8 := by
  have h := ndr_psd P hP ![0, 0, 1, 1]
  have hs := ndr_symm P 2 3
  simp [dotProduct, mulVec, Fin.sum_univ_four, ndrSg, ndrV, vecMulVec] at h
  norm_num at h
  linarith

lemma ndr_single (P : Measure (Fin 4 → ℝ)) (hP : P ∈ covarianceSet ndrLo ndrHi ndrMu ndrSg)
    (i : Fin 4) : ENNReal.ofReal (1 - 1/4) ≤ P {q | q i ≤ 3} := by
  have hbox := hP.2.1
  have : Set.Icc ndrLo ndrHi ⊆ {q : Fin 4 → ℝ | q i ≤ 3} := by
    intro q hq; have := hq.2 i; simp only [ndrHi] at this; simp only [Set.mem_setOf_eq]; linarith
  calc ENNReal.ofReal (1 - 1/4) ≤ 1 := by rw [ENNReal.ofReal_le_one]; norm_num
    _ = P (Set.Icc ndrLo ndrHi) := hbox.symm
    _ ≤ _ := measure_mono this

end


def ndrR1 : Fin 3 → List (Fin 4) := ![[0, 1], [2], [3]]
def ndrR2 : Fin 3 → List (Fin 4) := ![[2, 3], [0], [1]]
def ndrR3 : Fin 3 → List (Fin 4) := ![[0, 2], [1], [3]]
def ndrR4 : Fin 3 → List (Fin 4) := ![[1, 3], [0], [2]]

lemma ndrR1_rs : IsRouteSet ndrR1 := by unfold IsRouteSet ndrR1; decide
lemma ndrR2_rs : IsRouteSet ndrR2 := by unfold IsRouteSet ndrR2; decide
lemma ndrR3_rs : IsRouteSet ndrR3 := by unfold IsRouteSet ndrR3; decide
lemma ndrR4_rs : IsRouteSet ndrR4 := by unfold IsRouteSet ndrR4; decide

lemma ndrR1_feas : RVRPFeasible (covarianceSet ndrLo ndrHi ndrMu ndrSg) (1/4) 3 ndrR1 := by
  refine ⟨ndrR1_rs, fun k P hP => ?_⟩
  fin_cases k
  · simpa [ndrR1] using ndr_markov P hP 0 1 (ndr_b01 P hP)
  · simpa [ndrR1] using ndr_single P hP 2
  · simpa [ndrR1] using ndr_single P hP 3

lemma ndrR2_feas : RVRPFeasible (covarianceSet ndrLo ndrHi ndrMu ndrSg) (1/4) 3 ndrR2 := by
  refine ⟨ndrR2_rs, fun k P hP => ?_⟩
  fin_cases k
  · simpa [ndrR2] using ndr_markov P hP 2 3 (ndr_b23 P hP)
  · simpa [ndrR2] using ndr_single P hP 0
  · simpa [ndrR2] using ndr_single P hP 1

lemma ndrR3_infeas : ¬ RVRPFeasible (covarianceSet ndrLo ndrHi ndrMu ndrSg) (1/4) 3 ndrR3 := by
  rintro ⟨-, h⟩
  have h1 := h 0 ndrP0 ndrP0_mem
  have h2 := ndr_bad 0 2 (by simp [ndrP1]; norm_num) (by simp [ndrP2])
  simp [ndrR3] at h1
  exact absurd h1 (not_le.2 (by simpa using h2))

lemma ndrR4_infeas : ¬ RVRPFeasible (covarianceSet ndrLo ndrHi ndrMu ndrSg) (1/4) 3 ndrR4 := by
  rintro ⟨-, h⟩
  have h1 := h 0 ndrP0 ndrP0_mem
  have h2 := ndr_bad2 1 3 (by simp [ndrP2]; norm_num) (by simp [ndrP1])
  simp [ndrR4] at h1
  exact absurd h1 (not_le.2 (by simpa using h2))

theorem ndr_core :
    ∃ (n m : ℕ) (Q ε : ℝ) (qlo qhi μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ),
      0 ≤ Q ∧ 0 < ε ∧ ε < 1 ∧ (∀ j, 0 ≤ qlo j) ∧ (∀ j, qlo j < μ j ∧ μ j < qhi j) ∧
      Sig.PosDef ∧
      ∀ (Q' : ℝ) (q : Fin n → ℝ), 0 ≤ Q' → (∀ j, 0 ≤ q j) →
        {R : Fin m → List (Fin n) | RVRPFeasible (covarianceSet qlo qhi μ Sig) ε Q R} ≠
          {R | DetFeasible Q' q R} := by
  refine ⟨4, 3, 3, 1/4, ndrLo, ndrHi, ndrMu, ndrSg, by norm_num, by norm_num, by norm_num,
    fun j => by simp [ndrLo], fun j => by simp [ndrLo, ndrHi, ndrMu], ndrSg_posDef, ?_⟩
  intro Q' q hQ' hq hEq
  have d1 : DetFeasible Q' q ndrR1 := by
    have : ndrR1 ∈ {R : Fin 3 → List (Fin 4) | RVRPFeasible (covarianceSet ndrLo ndrHi ndrMu ndrSg) (1/4) 3 R} := ndrR1_feas
    rw [hEq] at this; exact this
  have d2 : DetFeasible Q' q ndrR2 := by
    have : ndrR2 ∈ {R : Fin 3 → List (Fin 4) | RVRPFeasible (covarianceSet ndrLo ndrHi ndrMu ndrSg) (1/4) 3 R} := ndrR2_feas
    rw [hEq] at this; exact this
  have n3 : ¬ DetFeasible Q' q ndrR3 := by
    intro h
    have : ndrR3 ∈ {R : Fin 3 → List (Fin 4) | DetFeasible Q' q R} := h
    rw [← hEq] at this; exact ndrR3_infeas this
  have n4 : ¬ DetFeasible Q' q ndrR4 := by
    intro h
    have : ndrR4 ∈ {R : Fin 3 → List (Fin 4) | DetFeasible Q' q R} := h
    rw [← hEq] at this; exact ndrR4_infeas this
  have a1 := d1.2 0; have a2 := d2.2 0
  simp [ndrR1, ndrR2] at a1 a2
  have h0 := hq 0; have h1 := hq 1; have h2 := hq 2; have h3 := hq 3
  have c3 : Q' < q 0 + q 2 := by
    by_contra hc; push_neg at hc
    exact n3 ⟨ndrR3_rs, fun k => by fin_cases k <;> simp [ndrR3] <;> linarith⟩
  have c4 : Q' < q 1 + q 3 := by
    by_contra hc; push_neg at hc
    exact n4 ⟨ndrR4_rs, fun k => by fin_cases k <;> simp [ndrR4] <;> linarith⟩
  linarith

end DRCVRP.Covariance

open DRCVRP.Covariance


theorem solution :
    ∃ (n m : ℕ) (Q ε : ℝ) (qlo qhi μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ),
      0 ≤ Q ∧ 0 < ε ∧ ε < 1 ∧ (∀ j, 0 ≤ qlo j) ∧ (∀ j, qlo j < μ j ∧ μ j < qhi j) ∧
      Sig.PosDef ∧
      ∀ (Q' : ℝ) (q : Fin n → ℝ), 0 ≤ Q' → (∀ j, 0 ≤ q j) →
        {R : Fin m → List (Fin n) | RVRPFeasible (covarianceSet qlo qhi μ Sig) ε Q R} ≠
          {R | DetFeasible Q' q R} := by
  exact ndr_core
