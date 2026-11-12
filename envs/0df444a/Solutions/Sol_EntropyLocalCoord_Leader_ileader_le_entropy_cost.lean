-- Prove2me | solution 1 for EntropyLocalCoord.Leader.ileader_le_entropy_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:56:35.8961+00:00
-- url     : https://prove2.me/submissions/ff8cd3d5-eb12-4441-9ce8-4fd896651a05

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Model
import Definitions.Def_EntropyLocalCoord_Leader_Information
import Theorems.Thm_EntropyLocalCoord_Leader_lemma_4_1
import Theorems.Thm_EntropyLocalCoord_Leader_theorem_4_2
import Theorems.Thm_EntropyLocalCoord_Leader_infoMeasure_prob_support
import Theorems.Thm_EntropyLocalCoord_Leader_ileader_le_cut_fraction

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace EntropyLocalCoord.Dev.PerProfile

open EntropyLocalCoord.Leader

section profile

variable {n k : ℕ} {S : InformationSkeleton n k} (π : CoordinationProfile S)

lemma sourceSigma_le (T : Finset (Fin k)) : sourceSigma π.Z T ≤ π.mΩ :=
  iSup₂_le fun j _ => (π.Z_measurable j).comap_le

lemma X_meas_univ (i : Fin n) : Measurable[sourceSigma π.Z Finset.univ] (π.X i) :=
  (π.X_measurable i).mono
    (iSup₂_mono' fun j _ => ⟨j, Finset.mem_univ j, le_rfl⟩) le_rfl

lemma X_meas (i : Fin n) : Measurable (π.X i) :=
  (π.X_measurable i).mono (sourceSigma_le π _) le_rfl

lemma unbiased (hπ : π.IsBinary) (i : Fin n) : IsUnbiasedSign π.P (π.X i) := by
  refine ⟨hπ i, ?_⟩
  have hm : MeasurableSet {ω | π.X i ω = 1} := (X_meas π i) (measurableSet_singleton 1)
  have h0 := π.mean_zero i
  have : ∀ ω, π.X i ω = 2 * ({ω | π.X i ω = 1}.indicator (fun _ => (1:ℝ)) ω) - 1 := by
    intro ω
    rcases hπ i ω with h | h <;> simp [Set.indicator, h] <;> norm_num
  have h1 : ∫ ω, π.X i ω ∂π.P = 2 * π.P.real {ω | π.X i ω = 1} - 1 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall this)]
    rw [integral_sub, integral_const_mul, integral_indicator_const _ hm]
    · simp
    · exact ((integrable_const (1:ℝ)).indicator hm).const_mul 2
    · exact integrable_const _
  linarith

lemma cov_eq (hπ : π.IsBinary) (i j : Fin n) :
    π.cov i j = 1 - 2 * π.P.real {ω | π.X i ω ≠ π.X j ω} := by
  have hm : MeasurableSet {ω | π.X i ω ≠ π.X j ω} :=
    (measurableSet_eq_fun (X_meas π i) (X_meas π j)).compl
  have : ∀ ω, π.X i ω * π.X j ω =
      1 - 2 * ({ω | π.X i ω ≠ π.X j ω}.indicator (fun _ => (1:ℝ)) ω) := by
    intro ω
    rcases hπ i ω with h | h <;> rcases hπ j ω with h' | h' <;>
      simp [Set.indicator, h, h'] <;> norm_num
  simp only [CoordinationProfile.cov, covariance, π.mean_zero, sub_zero]
  rw [integral_congr_ae (Filter.Eventually.of_forall this)]
  rw [integral_sub, integral_const_mul, integral_indicator_const _ hm]
  · simp
  · exact integrable_const _
  · exact ((integrable_const (1:ℝ)).indicator hm).const_mul 2

end profile


open scoped Classical in
/-- Indicator that the edge `e` is cut by the assignment `x`. -/
noncomputable def cutInd {n k : ℕ} (e : Sym2 (Fin n)) (x : Fin n → Fin k) : ℝ :=
  if ∃ i j, e = s(i, j) ∧ x i ≠ x j then 1 else 0

lemma cutInd_mk {n k : ℕ} (a b : Fin n) (x : Fin n → Fin k) :
    cutInd s(a, b) x = if x a ≠ x b then 1 else 0 := by
  classical
  have : (∃ i j, s(a, b) = s(i, j) ∧ x i ≠ x j) ↔ x a ≠ x b := by
    constructor
    · rintro ⟨i, j, h, hne⟩
      rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne
      · exact fun h' => hne h'.symm
    · intro h
      exact ⟨a, b, rfl, h⟩
  unfold cutInd
  simp only [this]

open scoped Classical in
lemma cutFraction_eq {n k : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Fin k) :
    cutFraction G x = (∑ e ∈ G.edgeFinset, cutInd e x) / (G.edgeFinset.card : ℝ) := by
  classical
  unfold cutFraction cutInd
  rw [Finset.card_filter]
  push_cast
  rfl

lemma h_concave : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) h := by
  have := Real.strictConcave_binEntropy.concaveOn.smul
    (inv_nonneg.2 (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)))
  have e : h = fun x => (Real.log 2)⁻¹ • Real.binEntropy x := by
    funext p
    simp [h, div_eq_inv_mul]
  rw [e]
  exact this

lemma h_zero : h 0 = 0 := by simp [h]

lemma integrable_comp {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    {n k : ℕ} (L : Fin n → Ω' → Fin k) (hL : ∀ i, Measurable (L i))
    (g : (Fin n → Fin k) → ℝ) : Integrable (fun ω => g (fun i => L i ω)) P' := by
  have hm : Measurable (fun ω => g fun i => L i ω) :=
    (measurable_of_finite g).comp (measurable_pi_lambda _ hL)
  refine Integrable.of_bound hm.aestronglyMeasurable (∑ y, ‖g y‖)
    (Filter.Eventually.of_forall fun ω => ?_)
  exact Finset.single_le_sum (f := fun y => ‖g y‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ _)

end EntropyLocalCoord.Dev.PerProfile

namespace EntropyLocalCoord.Leader

open EntropyLocalCoord.Dev.PerProfile

/-- Proof of Theorem 3.2, p. 12: for every binary coordination profile `π`,
`I_leader(G, 𝔖) ≤ 2 h(½ C(G, π))`. -/
theorem chk_ileader_le_entropy_cost {n k : ℕ} (G : SimpleGraph (Fin n))
    (S : InformationSkeleton n k) (π : CoordinationProfile S) (hπ : π.IsBinary) :
    Ileader G S ≤ 2 * h (1 / 2 * cost G π) := by
  classical
  have hsup := fun i => infoMeasure_prob_support S π hπ i
  obtain ⟨Ω', m', P', hP', L, hLm, hLlaw, hLpair⟩ :=
    theorem_4_2 (fun i a => infoMeasure π.P π.Z (π.X i) a) (fun i a => (hsup i).1 a)
      (fun i => (hsup i).2.1)
  have hedge : ∀ e : Sym2 (Fin n),
      (∫ ω, cutInd e (fun i => L i ω) ∂P') ≤ 2 * h (1 / 2 * π.edgeLoss e) ∧
        1 / 2 * π.edgeLoss e ∈ Set.Icc (0:ℝ) 1 := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      have hl : π.edgeLoss s(a, b) = 1 - π.cov a b := rfl
      have hq : 1 / 2 * π.edgeLoss s(a, b) = π.P.real {ω | π.X a ω ≠ π.X b ω} := by
        rw [hl, cov_eq π hπ]; ring
      rw [hq]
      refine ⟨?_, measureReal_nonneg, measureReal_le_one⟩
      have hset : MeasurableSet {ω | L a ω ≠ L b ω} :=
        (measurableSet_eq_fun (hLm a) (hLm b)).compl
      have hint : ∫ ω, cutInd s(a, b) (fun i => L i ω) ∂P' = P'.real {ω | L a ω ≠ L b ω} := by
        have : (fun ω => cutInd s(a, b) (fun i => L i ω)) =
            {ω | L a ω ≠ L b ω}.indicator (fun _ => (1:ℝ)) := by
          funext ω
          simp [cutInd_mk, Set.indicator]
        rw [this, integral_indicator_const _ hset]
        simp
      rw [hint]
      have h41 := lemma_4_1 π.P π.Z π.Z_measurable (π.X a) (π.X b) (X_meas_univ π a)
        (X_meas_univ π b) (unbiased π hπ a) (unbiased π hπ b)
      have h42 := (hLpair a b)
      have htv : 0 ≤ tvNorm (fun c => infoMeasure π.P π.Z (π.X a) c - infoMeasure π.P π.Z (π.X b) c) := by
        unfold tvNorm
        positivity
      linarith [h42.1, h42.2]
  have hgood : P' {ω | ¬ ∀ i, L i ω ∈ S.B i} = 0 := by
    refine measure_mono_null (t := ⋃ i, ⋃ a, ⋃ (_ : a ∉ S.B i), L i ⁻¹' {a}) ?_ ?_
    · intro ω hω
      simp only [Set.mem_setOf_eq, not_forall] at hω
      obtain ⟨i, hi⟩ := hω
      simp only [Set.mem_iUnion]
      exact ⟨i, L i ω, hi, rfl⟩
    · refine measure_iUnion_null fun i => measure_iUnion_null fun a =>
        measure_iUnion_null fun ha => ?_
      have := hLlaw i a
      rw [(hsup i).2.2 a ha] at this
      exact (measureReal_eq_zero_iff).1 this
  have hbound : ∫ ω, cutFraction G (fun i => L i ω) ∂P' ≤ 2 * h (1 / 2 * cost G π) := by
    simp_rw [cutFraction_eq]
    by_cases hm : G.edgeFinset.card = 0
    · simp [cost, hm, h_zero]
    · have hmpos : (0:ℝ) < (G.edgeFinset.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
      rw [integral_div, integral_finset_sum _
        (fun e _ => integrable_comp P' L hLm (cutInd e))]
      have step1 : ∑ e ∈ G.edgeFinset, ∫ ω, cutInd e (fun i => L i ω) ∂P' ≤
          ∑ e ∈ G.edgeFinset, 2 * h (1 / 2 * π.edgeLoss e) :=
        Finset.sum_le_sum fun e _ => (hedge e).1
      have jensen := h_concave.le_map_sum (t := G.edgeFinset) (w := fun _ => 1 / (G.edgeFinset.card : ℝ))
        (p := fun e => 1 / 2 * π.edgeLoss e) (fun _ _ => by positivity)
        (by simp [Finset.sum_const, nsmul_eq_mul]; field_simp) (fun e _ => (hedge e).2)
      have hc : ∑ e ∈ G.edgeFinset, (1 / (G.edgeFinset.card : ℝ)) • (1 / 2 * π.edgeLoss e) =
          1 / 2 * cost G π := by
        simp only [smul_eq_mul, cost]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring
      rw [hc] at jensen
      calc (∑ e ∈ G.edgeFinset, ∫ ω, cutInd e (fun i => L i ω) ∂P') / (G.edgeFinset.card : ℝ)
          ≤ (∑ e ∈ G.edgeFinset, 2 * h (1 / 2 * π.edgeLoss e)) / (G.edgeFinset.card : ℝ) :=
            div_le_div_of_nonneg_right step1 hmpos.le
        _ = 2 * ∑ e ∈ G.edgeFinset, (1 / (G.edgeFinset.card : ℝ)) • h (1 / 2 * π.edgeLoss e) := by
            simp only [smul_eq_mul]
            rw [← Finset.mul_sum, ← Finset.mul_sum, div_eq_mul_inv]
            ring
        _ ≤ 2 * h (1 / 2 * cost G π) := by linarith
  have hint : Integrable (fun ω => cutFraction G (fun i => L i ω)) P' :=
    integrable_comp P' L hLm (cutFraction G)
  obtain ⟨ω, hω, hle⟩ := exists_notMem_null_le_integral hint hgood
  have hω' : ∀ i, L i ω ∈ S.B i := by simpa using hω
  exact (ileader_le_cut_fraction G S (fun i => L i ω) hω').trans (hle.trans hbound)

end EntropyLocalCoord.Leader
end

theorem solution : type_of% @EntropyLocalCoord.Leader.chk_ileader_le_entropy_cost := @EntropyLocalCoord.Leader.chk_ileader_le_entropy_cost
