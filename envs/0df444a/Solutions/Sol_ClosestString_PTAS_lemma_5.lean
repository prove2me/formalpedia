-- Prove2me | solution 1 for ClosestString.PTAS.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:53:28.708863+00:00
-- url     : https://prove2.me/submissions/df54bdd9-f1fd-4af0-af10-b9d27638f796

import Mathlib

namespace ClosestString.PTAS.A3L5

open MeasureTheory ProbabilityTheory

theorem ae_mem_Icc_of_ber {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (Y : Ω → ℝ) (hY : Measurable Y) (q : ℝ)
    (h : Pr.real {ω | Y ω = 1} = q ∧ Pr.real {ω | Y ω = 0} = 1 - q) :
    ∀ᵐ ω ∂Pr, Y ω ∈ Set.Icc (0 : ℝ) 1 := by
  have hA : MeasurableSet {ω | Y ω = 1} := hY (measurableSet_singleton 1)
  have hB : MeasurableSet {ω | Y ω = 0} := hY (measurableSet_singleton 0)
  have hdisj : Disjoint {ω | Y ω = 1} {ω | Y ω = 0} := by
    rw [Set.disjoint_left]; intro ω h1 h0
    simp only [Set.mem_setOf_eq] at h1 h0; rw [h1] at h0; norm_num at h0
  have hU : Pr.real ({ω | Y ω = 1} ∪ {ω | Y ω = 0}) = 1 := by
    rw [measureReal_union hdisj hB, h.1, h.2]; ring
  have hC : Pr.real ({ω | Y ω = 1} ∪ {ω | Y ω = 0})ᶜ = 0 := by
    rw [measureReal_compl (hA.union hB), hU]; simp
  have hC' : Pr ({ω | Y ω = 1} ∪ {ω | Y ω = 0})ᶜ = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hC
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hC'
  simp only [Set.mem_setOf_eq, Set.mem_Icc, not_and_or, not_le] at hω
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or]
  constructor <;> intro h' <;> rw [h'] at hω <;> norm_num at hω

/-- Hoeffding for `[0,1]`-valued independent variables, both tails. -/
theorem hoeff {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) (hm : ∀ i, Measurable (X i))
    (hind : iIndepFun X Pr) (hb : ∀ i, ∀ᵐ ω ∂Pr, X i ω ∈ Set.Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 ≤ t) :
    Pr.real {ω | (∫ ω', ∑ i, X i ω' ∂Pr) + t ≤ ∑ i, X i ω} ≤
        Real.exp (-t ^ 2 / (2 * ∑ _i : ι, (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) : ℝ))) ∧
      Pr.real {ω | ∑ i, X i ω ≤ (∫ ω', ∑ i, X i ω' ∂Pr) - t} ≤
        Real.exp (-t ^ 2 / (2 * ∑ _i : ι, (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) : ℝ))) := by
  have hint : ∀ i, Integrable (X i) Pr := fun i =>
    Integrable.of_mem_Icc 0 1 (hm i).aemeasurable (hb i)
  have hsum : (∫ ω', ∑ i, X i ω' ∂Pr) = ∑ i, ∫ ω', X i ω' ∂Pr :=
    integral_finset_sum _ fun i _ => hint i
  set Y : ι → Ω → ℝ := fun i ω => X i ω - ∫ ω', X i ω' ∂Pr with hYdef
  have hYind : iIndepFun Y Pr :=
    hind.comp (fun i x => x - ∫ ω', X i ω' ∂Pr) fun i => measurable_id.sub_const _
  have hYsub : ∀ i, HasSubgaussianMGF (Y i) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) Pr := fun i =>
    hasSubgaussianMGF_of_mem_Icc (hm i).aemeasurable (hb i)
  have hYsum : ∀ ω, ∑ i ∈ Finset.univ, Y i ω = ∑ i, X i ω - ∫ ω', ∑ i, X i ω' ∂Pr := by
    intro ω; rw [hsum]; simp [hYdef, Finset.sum_sub_distrib]
  have h1 := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hYind (s := Finset.univ)
    (fun i _ => hYsub i) ht
  have hnind : iIndepFun (fun i ω => -Y i ω) Pr :=
    hYind.comp (fun _ x => -x) fun _ => measurable_neg
  have h2 := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hnind (s := Finset.univ)
    (fun i _ => (hYsub i).neg) ht
  push_cast at h1 h2 ⊢
  constructor
  · refine le_trans (le_of_eq ?_) h1
    congr 1; ext ω; simp only [Set.mem_setOf_eq, hYsum]; constructor <;> intro h <;> linarith
  · refine le_trans (le_of_eq ?_) h2
    congr 1; ext ω
    simp only [Set.mem_setOf_eq, Finset.sum_neg_distrib, hYsum]
    constructor <;> intro h <;> linarith

theorem main {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    {N : ℕ} (X : Fin N → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X Pr)
    (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hX_ber : ∀ i, Pr.real {ω | X i ω = 1} = p i ∧ Pr.real {ω | X i ω = 0} = 1 - p i)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Pr.real {ω | (∫ ω', ∑ i, X i ω' ∂Pr) + ε * N < ∑ i, X i ω} <
        Real.exp (-(1 / 3) * N * ε ^ 2) ∧
      Pr.real {ω | (∫ ω', ∑ i, X i ω' ∂Pr) + ε * N ≤ ∑ i, X i ω} ≤
        Real.exp (-(1 / 3) * N * ε ^ 2) ∧
      Pr.real {ω | ∑ i, X i ω ≤ (∫ ω', ∑ i, X i ω' ∂Pr) - ε * N} ≤
        Real.exp (-(1 / 2) * N * ε ^ 2) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hb := fun i => ae_mem_Icc_of_ber Pr (X i) (hX_meas i) (p i) (hX_ber i)
  obtain ⟨h1, h2⟩ := hoeff Pr X hX_meas hX_indep hb (t := ε * N) (by positivity)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : ∑ _i : Fin N, (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) : ℝ) = N / 4 := by
    simp; norm_num; ring
  rw [hc] at h1 h2
  have hval : -(ε * N) ^ 2 / (2 * (N / 4 : ℝ)) = -2 * N * ε ^ 2 := by
    field_simp; ring
  rw [hval] at h1 h2
  have hlt : Real.exp (-2 * N * ε ^ 2) < Real.exp (-(1 / 3) * N * ε ^ 2) := by
    rw [Real.exp_lt_exp]; nlinarith [sq_pos_of_pos hε]
  have hle2 : Real.exp (-2 * N * ε ^ 2) ≤ Real.exp (-(1 / 2) * N * ε ^ 2) := by
    rw [Real.exp_le_exp]; nlinarith [sq_pos_of_pos hε]
  refine ⟨lt_of_le_of_lt (le_trans ?_ h1) hlt, le_trans h1 hlt.le, le_trans h2 hle2⟩
  exact measureReal_mono (fun ω h => le_of_lt (Set.mem_setOf_eq ▸ h :))

end ClosestString.PTAS.A3L5

open MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    {N : ℕ} (X : Fin N → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X Pr)
    (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hX_ber : ∀ i, Pr.real {ω | X i ω = 1} = p i ∧ Pr.real {ω | X i ω = 0} = 1 - p i)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Pr.real {ω | (∫ ω', ∑ i, X i ω' ∂Pr) + ε * N < ∑ i, X i ω} <
        Real.exp (-(1 / 3) * N * ε ^ 2) ∧
      Pr.real {ω | (∫ ω', ∑ i, X i ω' ∂Pr) + ε * N ≤ ∑ i, X i ω} ≤
        Real.exp (-(1 / 3) * N * ε ^ 2) ∧
      Pr.real {ω | ∑ i, X i ω ≤ (∫ ω', ∑ i, X i ω' ∂Pr) - ε * N} ≤
        Real.exp (-(1 / 2) * N * ε ^ 2) :=
  ClosestString.PTAS.A3L5.main Pr X hX_meas hX_indep p hp hX_ber ε hε hε1

#print axioms solution
