-- Prove2me | solution 1 for BwSC.LowerBound.eq_47
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T03:01:17.779512+00:00
-- url     : https://prove2.me/submissions/ca63a675-6417-4d0b-bcae-421d13870430

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof
import Theorems.Thm_BwSC_LowerBound_proposition_5
import Theorems.Thm_BwSC_LowerBound_property_1
import Theorems.Thm_BwSC_LowerBound_lemma_13
import Theorems.Thm_BwSC_LowerBound_corollary_4

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound.GRFAux

lemma act_congr {K T : ℕ} {h h' : BanditHistory K T} (e : actions h = actions h') :
    act h = act h' := by
  funext t; simp [act, e]

lemma measurableSet_of_actions {K T : ℕ} (E : Set (BanditHistory K T))
    (hE : ∀ h h', actions h = actions h' → h ∈ E → h' ∈ E) : MeasurableSet E := by
  have : E = actions ⁻¹' (actions '' E) := by
    ext h; constructor
    · intro hh; exact ⟨h, hh, rfl⟩
    · rintro ⟨h', hh', e⟩; exact hE h' h e hh'
  rw [this]; exact measurable_actions (Set.toFinite _).measurableSet

lemma measurableSet_E2 (S K T j : ℕ) (k : Fin K) : MeasurableSet (E2 S K T j k) := by
  apply measurableSet_of_actions
  intro h h' e hh
  simp only [E2, notChosen, Set.mem_setOf_eq] at hh ⊢
  rw [← act_congr e]; exact hh

lemma sum_Icc_shift (M : ℕ) (f : ℕ → ℝ) :
    ∑ j : Fin M, f (j.val + 1) = ∑ j ∈ Finset.Icc 1 M, f j := by
  rw [Fin.sum_univ_eq_sum_range (fun j => f (j + 1)) M]
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

lemma sum_reindex {K M : ℕ} (g : ℕ → Fin K → ℝ) :
    ∑ i : Fin (M * K), g ((finProdFinEquiv.symm i).1.val + 1) (finProdFinEquiv.symm i).2
      = ∑ j ∈ Finset.Icc 1 M, ∑ k : Fin K, g j k := by
  rw [Equiv.sum_comp finProdFinEquiv.symm (fun p => g (p.1.val + 1) p.2),
    Fintype.sum_prod_type]
  exact sum_Icc_shift M (fun j => ∑ k : Fin K, g j k)

lemma grf_final (pb qb Db L : ℝ) (h : qb - Real.sqrt (2 * qb * Db) ≤ pb) (hD0 : 0 ≤ Db)
    (hD : Db ≤ qb / 4) (hq : L / 2 ≤ qb) (hL : 0 ≤ L) :
    (2 - Real.sqrt 2) / 4 * L ≤ pb := by
  have hqb : 0 ≤ qb := by linarith
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2pos : 0 < Real.sqrt 2 := by positivity
  have hs2lt : Real.sqrt 2 < 2 := by nlinarith
  have h1 : Real.sqrt (2 * qb * Db) ≤ Real.sqrt (qb ^ 2 / 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have h2 : Real.sqrt (qb ^ 2 / 2) = qb * Real.sqrt 2 / 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    nlinarith
  rw [h2] at h1
  nlinarith

end BwSC.LowerBound.GRFAux

open BwSC.LowerBound BwSC.LowerBound.GRFAux in
theorem solution {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π) :
    (2 - Real.sqrt 2) / 4 * (1 / ((qIdx S K : ℝ) + 2) ^ 2) ≤ pbar2 π S T := by
  set M := qIdx S K + 2 with hM
  have hN : 0 < M * K := Nat.mul_pos (by omega) (by omega)
  let jj : Fin (M * K) → ℕ := fun i => (finProdFinEquiv.symm i).1.val + 1
  let kk : Fin (M * K) → Fin K := fun i => (finProdFinEquiv.symm i).2
  have hjj : ∀ i, jj i ∈ Finset.Icc 1 (qIdx S K + 2) := by
    intro i
    have := (finProdFinEquiv.symm i).1.isLt
    simp only [Finset.mem_Icc, jj]; omega
  let P : Fin (M * K) → Measure (BanditHistory K T) := fun i => artP2 π S T (jj i) (kk i)
  let Q : Fin (M * K) → Measure (BanditHistory K T) := fun i => artQ2 π S T (jj i) (kk i)
  haveI : ∀ i, IsProbabilityMeasure (P i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_stopCensor _ _ _).aemeasurable
  haveI : ∀ i, IsProbabilityMeasure (Q i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_stopCensor _ _ _).aemeasurable
  obtain ⟨L1, L2, L3⟩ := lemma_13 hK hT π hπ
  obtain ⟨_, C2⟩ := corollary_4 hK hT π hπ (0 : Fin K → ℝ)
  set X := ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K, klDiv (artQ2 π S T j k) (artP2 π S T j k)
    with hX
  have hXfin : X ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top L1
  have hterm : ∀ j ∈ Finset.Icc 1 (qIdx S K + 2), ∀ k : Fin K,
      klDiv (artQ2 π S T j k) (artP2 π S T j k) ≠ ∞ := by
    intro j hj k
    refine ne_top_of_le_ne_top hXfin ?_
    calc klDiv (artQ2 π S T j k) (artP2 π S T j k)
        ≤ ∑ k : Fin K, klDiv (artQ2 π S T j k) (artP2 π S T j k) :=
          Finset.single_le_sum (f := fun k => klDiv (artQ2 π S T j k) (artP2 π S T j k))
            (fun _ _ => zero_le) (Finset.mem_univ k)
      _ ≤ X := Finset.single_le_sum
            (f := fun j => ∑ k : Fin K, klDiv (artQ2 π S T j k) (artP2 π S T j k))
            (fun _ _ => zero_le) hj
  have hfin : ∀ i, klDiv (Q i) (P i) ≠ ∞ := fun i => hterm _ (hjj i) _
  have G := (proposition_5 hN (Ω := fun _ => BanditHistory K T) P Q
    (fun i => E2 S K T (jj i) (kk i)) (fun i => measurableSet_E2 _ _ _ _ _)).2 hfin
  -- identify the three averages
  have hNcast : ((M * K : ℕ) : ℝ) = ((qIdx S K : ℝ) + 2) * K := by rw [hM]; push_cast; ring
  have eP : ∑ i, (P i (E2 S K T (jj i) (kk i))).toReal =
      ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
        ((banditMeasure (gaussianBandit (envAlt2 S K T j k)) π T) (E2 S K T j k)).toReal := by
    rw [← sum_reindex (M := M) (fun j k =>
      ((banditMeasure (gaussianBandit (envAlt2 S K T j k)) π T) (E2 S K T j k)).toReal)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have := (property_1 (S := S) (T := T) π (jj i) (hjj i) (kk i)).2.2.2.2.1
    simp only [P]; rw [this]
  have eQ : ∑ i, (Q i (E2 S K T (jj i) (kk i))).toReal =
      ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
        ((banditMeasure (gaussianBandit (0 : Fin K → ℝ)) π T) (E2 S K T j k)).toReal := by
    rw [← sum_reindex (M := M) (fun j k =>
      ((banditMeasure (gaussianBandit (0 : Fin K → ℝ)) π T) (E2 S K T j k)).toReal)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have := (property_1 (S := S) (T := T) π (jj i) (hjj i) (kk i)).2.2.2.2.2
    simp only [Q]; rw [this]
  have eD : ∑ i, (klDiv (Q i) (P i)).toReal = X.toReal := by
    rw [sum_reindex (M := M) (fun j k => (klDiv (artQ2 π S T j k) (artP2 π S T j k)).toReal),
      hX, ENNReal.toReal_sum (fun j hj => ?_)]
    · refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [ENNReal.toReal_sum (fun k _ => hterm j hj k)]
    · exact ENNReal.sum_ne_top.mpr (fun k _ => hterm j hj k)
  rw [eP, eQ, eD, hNcast] at G
  -- the bound on the average divergence
  have hDb : 1 / (((qIdx S K : ℝ) + 2) * K) * X.toReal ≤ 1 / (8 * ((qIdx S K : ℝ) + 2) ^ 2) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top L2
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at this
    exact this
  have hq2 : (0 : ℝ) < (qIdx S K : ℝ) + 2 := by positivity
  refine grf_final (pbar2 π S T) (qbar2 π S T) (1 / (((qIdx S K : ℝ) + 2) * K) * X.toReal)
    (1 / ((qIdx S K : ℝ) + 2) ^ 2) ?_ (by positivity) (hDb.trans L3) ?_ (by positivity)
  · simpa [pbar2, qbar2] using G
  · have : 1 / ((qIdx S K : ℝ) + 2) ^ 2 / 2 = 1 / (2 * ((qIdx S K : ℝ) + 2) ^ 2) := by
      field_simp
    rw [this]; simpa [qbar2] using C2
