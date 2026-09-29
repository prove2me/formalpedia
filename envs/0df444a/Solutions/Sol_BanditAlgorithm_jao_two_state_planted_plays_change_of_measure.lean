-- Prove2me | solution 1 for BanditAlgorithm.jao_two_state_planted_plays_change_of_measure
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-05T18:33:58.373968+00:00
-- url     : https://prove2.me/submissions/82088f7d-ef9f-4942-beac-4a2138a2609b

import Mathlib.Data.Real.Sqrt
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Definitions.Def_UCRL2ConfidenceSets
import Definitions.Def_bernoulliRelativeEntropy
import Theorems.Thm_BanditAlgorithm_mdp_divergence_decomposition_single_row
import Theorems.Thm_BanditAlgorithm_pinsker_squared_bounded_expectation_difference
import Theorems.Thm_InformationTheory_categorical_toReal_klDiv_eq_sum
import Theorems.Thm_BanditAlgorithm_bernoulli_relative_entropy_le_sq_div_of_add_le_one

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal NNReal BigOperators

namespace JaoLemma13

lemma toMeasure_apply {S : ℕ} (d : MDPStateDistribution S) (A : Set (Fin S)) :
    d.toMeasure A = ∑ i, (d.prob i : ℝ≥0∞) * A.indicator 1 i := by
  rw [MDPStateDistribution.toMeasure, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

lemma toMeasure_singleton {S : ℕ} (d : MDPStateDistribution S) (s : Fin S) :
    d.toMeasure {s} = (d.prob s : ℝ≥0∞) := by
  rw [toMeasure_apply, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    simp [Set.indicator_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ s) h

lemma toMeasure_real_singleton {S : ℕ} (d : MDPStateDistribution S) (s : Fin S) :
    (d.toMeasure).real {s} = (d.prob s : ℝ) := by
  rw [measureReal_def, toMeasure_singleton]
  simp

lemma row_ext {u v : Fin 2 → ℝ≥0} (hu : ∑ i, u i = 1) (hv : ∑ i, v i = 1)
    (h : (u 0 : ℝ) = (v 0 : ℝ)) : u = v := by
  have h0 : u 0 = v 0 := NNReal.coe_injective h
  have hu' : u 0 + u 1 = 1 := by rwa [Fin.sum_univ_two] at hu
  have hv' : v 0 + v 1 = 1 := by rwa [Fin.sum_univ_two] at hv
  have h1 : u 1 = v 1 := by
    have hsum : u 0 + u 1 = v 0 + v 1 := by rw [hu', hv']
    rw [h0] at hsum
    exact add_left_cancel hsum
  funext i
  fin_cases i
  · exact h0
  · exact h1

lemma row_ext' {u v : Fin 2 → ℝ≥0} (hu : ∑ i, u i = 1) (hv : ∑ i, v i = 1)
    (h : (u 1 : ℝ) = (v 1 : ℝ)) : u = v := by
  have h1 : u 1 = v 1 := NNReal.coe_injective h
  have hu' : u 0 + u 1 = 1 := by rwa [Fin.sum_univ_two] at hu
  have hv' : v 0 + v 1 = 1 := by rwa [Fin.sum_univ_two] at hv
  have h0 : u 0 = v 0 := by
    have hsum : u 1 + u 0 = v 1 + v 0 := by rw [add_comm (u 1), add_comm (v 1), hu', hv']
    rw [h1] at hsum
    exact add_left_cancel hsum
  funext i
  fin_cases i
  · exact h0
  · exact h1

lemma fin2_cases (s : Fin 2) : s = 0 ∨ s = 1 := by
  have hlt := s.isLt
  rcases Nat.eq_zero_or_pos s.val with h | h
  · exact Or.inl (Fin.ext (by simp [h]))
  · exact Or.inr (Fin.ext (by simp; omega))

lemma visit_mono {m T : ℕ} (h : MDPTrajectory 2 m T) (s : Fin 2) (a : Fin m) {k l : ℕ}
    (hkl : k ≤ l) : mdpVisitCount h k s a ≤ mdpVisitCount h l s a := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨lt_of_lt_of_le hi.1 hkl, hi.2⟩

lemma visit_le {m T : ℕ} (h : MDPTrajectory 2 m T) (s : Fin 2) (a : Fin m) (k : ℕ) :
    mdpVisitCount h k s a ≤ T := by
  unfold mdpVisitCount
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)

lemma lintegral_visit_eq {m T : ℕ} (μ : Measure (MDPTrajectory 2 m T)) [IsProbabilityMeasure μ]
    (s : Fin 2) (a : Fin m) (k : ℕ) :
    (∫⁻ h, (mdpVisitCount h k s a : ℝ≥0∞) ∂μ)
      = ENNReal.ofReal (∫ h, (mdpVisitCount h k s a : ℝ) ∂μ) := by
  have hcast : ∀ h : MDPTrajectory 2 m T, ((mdpVisitCount h k s a : ℕ) : ℝ≥0∞)
      = (((mdpVisitCount h k s a : ℕ) : ℝ≥0) : ℝ≥0∞) := by
    intro h; simp
  simp_rw [hcast]
  rw [MeasureTheory.lintegral_coe_eq_integral _ Integrable.of_finite]
  norm_num

end JaoLemma13

open JaoLemma13

theorem solution
    {m : ℕ} (δ ε : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3) (hε0 : 0 < ε) (hεδ : ε ≤ δ)
    (a : Fin m) (M M₀ : FiniteMDP 2 m)
    (hr0 : ∀ b, M.r 0 b = 0) (hr1 : ∀ b, M.r 1 b = 1)
    (hP1 : ∀ b, (M.P 1 b 0 : ℝ) = δ)
    (hP0 : ∀ b, (M.P 0 b 1 : ℝ) = δ + (if b = a then ε else 0))
    (hr0' : ∀ b, M₀.r 0 b = 0) (hr1' : ∀ b, M₀.r 1 b = 1)
    (hP1' : ∀ b, (M₀.P 1 b 0 : ℝ) = δ) (hP0' : ∀ b, (M₀.P 0 b 1 : ℝ) = δ)
    (T : ℕ) (π : MDPPolicy 2 m) :
    (∫ h, (mdpVisitCount h T 0 a : ℝ) ∂(mdpMeasure M (mdpStateDirac 0) π T))
      ≤ (∫ h, (mdpVisitCount h T 0 a : ℝ) ∂(mdpMeasure M₀ (mdpStateDirac 0) π T))
        + (T : ℝ) / 2 * (ε / Real.sqrt δ)
            * Real.sqrt
                (2 * ∫ h, (mdpVisitCount h T 0 a : ℝ)
                        ∂(mdpMeasure M₀ (mdpStateDirac 0) π T)) := by
  -- basic numeric facts
  have hδ1 : δ + ε ≤ 2 / 3 := by linarith
  have hsum1 : δ + (δ + ε) ≤ 1 := by linarith
  have hpos1 : (0:ℝ) < 1 - δ - ε := by linarith
  -- the trajectory laws
  set P := mdpMeasure M₀ (mdpStateDirac (0 : Fin 2)) π T with hPdef
  set Q := mdpMeasure M (mdpStateDirac (0 : Fin 2)) π T with hQdef
  set A : ℝ := ∫ h, (mdpVisitCount h T 0 a : ℝ) ∂P with hAdef
  set B : ℝ := ∫ h, (mdpVisitCount h T 0 a : ℝ) ∂Q with hBdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    apply integral_nonneg
    intro h
    positivity
  -- the trivial horizon
  rcases Nat.eq_zero_or_pos T with hT0 | hTpos
  · subst hT0
    have hz : ∀ (μ : Measure (MDPTrajectory 2 m 0)),
        (∫ h, (mdpVisitCount h 0 (0 : Fin 2) a : ℝ) ∂μ) = 0 := by
      intro μ
      have : ∀ h : MDPTrajectory 2 m 0, (mdpVisitCount h 0 (0 : Fin 2) a : ℝ) = 0 := by
        intro h
        simp [mdpVisitCount]
      simp [this]
    rw [hBdef, hAdef, hz, hz]
    simp
  -- rows agree away from `(0, a)`
  have hrow : ∀ (s : Fin 2) (b : Fin m), (s, b) ≠ ((0 : Fin 2), a) → M₀.P s b = M.P s b := by
    intro s b hne
    rcases fin2_cases s with hs | hs
    · subst hs
      have hba : b ≠ a := by
        intro hb
        exact hne (by rw [hb])
      refine row_ext' (M₀.P_sum_one 0 b) (M.P_sum_one 0 b) ?_
      rw [hP0' b, hP0 b, if_neg hba]
      ring
    · subst hs
      exact row_ext (M₀.P_sum_one 1 b) (M.P_sum_one 1 b) (by rw [hP1' b, hP1 b])
  -- the planted row is everywhere positive, so the reference row is absolutely continuous
  have hM1 : (M.P 0 a 1 : ℝ) = δ + ε := by rw [hP0 a, if_pos rfl]
  have hM0 : (M.P 0 a 0 : ℝ) = 1 - δ - ε := by
    have hs := M.P_sum_one 0 a
    rw [Fin.sum_univ_two] at hs
    have : (M.P 0 a 0 : ℝ) + (M.P 0 a 1 : ℝ) = 1 := by
      rw [← NNReal.coe_add, hs, NNReal.coe_one]
    rw [hM1] at this
    linarith
  have hM0' : (M₀.P 0 a 1 : ℝ) = δ := hP0' a
  have hM00 : (M₀.P 0 a 0 : ℝ) = 1 - δ := by
    have hs := M₀.P_sum_one 0 a
    rw [Fin.sum_univ_two] at hs
    have : (M₀.P 0 a 0 : ℝ) + (M₀.P 0 a 1 : ℝ) = 1 := by
      rw [← NNReal.coe_add, hs, NNReal.coe_one]
    rw [hM0'] at this
    linarith
  have hac : (M₀.transitionDist 0 a).toMeasure ≪ (M.transitionDist 0 a).toMeasure := by
    intro s hs
    rw [toMeasure_apply] at hs ⊢
    refine Finset.sum_eq_zero ?_
    intro i _
    have hzero := (Finset.sum_eq_zero_iff.mp hs) i (Finset.mem_univ i)
    rcases mul_eq_zero.mp hzero with hh | hh
    · exfalso
      have : (M.transitionDist 0 a).prob i = 0 := by
        simpa using hh
      have hval : ((M.transitionDist 0 a).prob i : ℝ) = 0 := by rw [this]; simp
      rw [FiniteMDP.transitionDist] at hval
      simp only at hval
      rcases fin2_cases i with hi | hi
      · rw [hi, hM0] at hval; linarith
      · rw [hi, hM1] at hval; linarith
    · rw [hh, mul_zero]
  -- the two rows, as measures on `Fin 2`
  have hR0_0 : ((M₀.transitionDist 0 a).toMeasure).real {0} = 1 - δ := by
    rw [toMeasure_real_singleton, FiniteMDP.transitionDist]; exact hM00
  have hR0_1 : ((M₀.transitionDist 0 a).toMeasure).real {1} = δ := by
    rw [toMeasure_real_singleton, FiniteMDP.transitionDist]; exact hM0'
  have hR1_0 : ((M.transitionDist 0 a).toMeasure).real {0} = 1 - δ - ε := by
    rw [toMeasure_real_singleton, FiniteMDP.transitionDist]; exact hM0
  have hR1_1 : ((M.transitionDist 0 a).toMeasure).real {1} = δ + ε := by
    rw [toMeasure_real_singleton, FiniteMDP.transitionDist]; exact hM1
  -- the row divergence
  have hkl : (klDiv (M₀.transitionDist 0 a).toMeasure (M.transitionDist 0 a).toMeasure).toReal
      = bernoulliRelativeEntropy δ (δ + ε) := by
    rw [InformationTheory.categorical_toReal_klDiv_eq_sum _ _ hac, Fin.sum_univ_two,
      hR0_0, hR0_1, hR1_0, hR1_1, bernoulliRelativeEntropy]
    have h1 : (1:ℝ) - (δ + ε) = 1 - δ - ε := by ring
    rw [h1]
    ring
  have hkltop : klDiv (M₀.transitionDist 0 a).toMeasure (M.transitionDist 0 a).toMeasure ≠ ∞ :=
    klDiv_ne_top hac Integrable.of_finite
  have hklb : (klDiv (M₀.transitionDist 0 a).toMeasure
      (M.transitionDist 0 a).toMeasure).toReal ≤ ε ^ 2 / δ := by
    rw [hkl]
    have hb := BanditAlgorithm.bernoulli_relative_entropy_le_sq_div_of_add_le_one
      (p := δ) (q := δ + ε) hδ0 (by linarith) hsum1
    have hrw : (δ + ε - δ) ^ 2 / (δ * (2 - δ - (δ + ε))) ≤ ε ^ 2 / δ := by
      have h1 : (δ + ε - δ) ^ 2 = ε ^ 2 := by ring
      rw [h1]
      apply div_le_div_of_nonneg_left (by positivity) hδ0
      nlinarith
    linarith
  -- the divergence decomposition
  have hdecomp := BanditAlgorithm.mdp_divergence_decomposition_single_row
      (M₀ := M₀) (M₁ := M) (μ0 := mdpStateDirac (0 : Fin 2)) (π := π)
      (sStar := (0 : Fin 2)) (aStar := a) hrow hac T
  set L : ℝ := ∫ h, (mdpVisitCount h (T - 1) (0 : Fin 2) a : ℝ) ∂P with hLdef
  have hL0 : 0 ≤ L := by
    rw [hLdef]; apply integral_nonneg; intro h; positivity
  have hLA : L ≤ A := by
    rw [hLdef, hAdef]
    apply integral_mono Integrable.of_finite Integrable.of_finite
    intro h
    exact_mod_cast Nat.cast_le.mpr (visit_mono h 0 a (Nat.sub_le T 1))
  have hlint : (∫⁻ h, (mdpVisitCount h (T - 1) (0 : Fin 2) a : ℝ≥0∞) ∂P) = ENNReal.ofReal L :=
    lintegral_visit_eq P 0 a (T - 1)
  have hPQtop : klDiv P Q ≠ ∞ := by
    rw [hPdef, hQdef] at *
    rw [hdecomp, hlint]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hkltop
  have hPQval : (klDiv P Q).toReal ≤ L * (ε ^ 2 / δ) := by
    rw [hdecomp, hlint, ENNReal.toReal_mul, ENNReal.toReal_ofReal hL0]
    exact mul_le_mul_of_nonneg_left hklb hL0
  -- Pinsker
  have hTpos' : (0:ℝ) < T := by exact_mod_cast hTpos
  have hpin := BanditAlgorithm.pinsker_squared_bounded_expectation_difference P Q
      (fun h => (mdpVisitCount h T (0 : Fin 2) a : ℝ) / T)
      (measurable_of_countable _)
      (fun h => by positivity)
      (fun h => by
        rw [div_le_one hTpos']
        exact_mod_cast visit_le h 0 a T)
      hPQtop
  rw [integral_div, integral_div, ← hAdef, ← hBdef] at hpin
  -- combine
  have hsq : (B - A) ^ 2 ≤ (T : ℝ) ^ 2 * A * ε ^ 2 / (2 * δ) := by
    have h1 : 2 * (B / T - A / T) ^ 2 ≤ L * (ε ^ 2 / δ) := le_trans hpin hPQval
    have h2 : (B / T - A / T) ^ 2 = (B - A) ^ 2 / (T : ℝ) ^ 2 := by
      field_simp
    rw [h2] at h1
    have h3 : L * (ε ^ 2 / δ) ≤ A * (ε ^ 2 / δ) := by
      apply mul_le_mul_of_nonneg_right hLA
      positivity
    have h4 : 2 * ((B - A) ^ 2 / (T : ℝ) ^ 2) ≤ A * (ε ^ 2 / δ) := le_trans h1 h3
    have hT2 : (0:ℝ) < (T : ℝ) ^ 2 := by positivity
    have h5 : (B - A) ^ 2 / (T : ℝ) ^ 2 ≤ A * (ε ^ 2 / δ) / 2 := by linarith
    calc (B - A) ^ 2 = ((B - A) ^ 2 / (T : ℝ) ^ 2) * (T : ℝ) ^ 2 := by
          field_simp
      _ ≤ (A * (ε ^ 2 / δ) / 2) * (T : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h5 hT2.le
      _ = (T : ℝ) ^ 2 * A * ε ^ 2 / (2 * δ) := by
          field_simp
  have hrhs : ((T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * A)) ^ 2
      = (T : ℝ) ^ 2 * A * ε ^ 2 / (2 * δ) := by
    have hs1 : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ0.le
    have hs2 : Real.sqrt (2 * A) ^ 2 = 2 * A := Real.sq_sqrt (by positivity)
    have hsne : Real.sqrt δ ≠ 0 := by positivity
    field_simp
    nlinarith [hs1, hs2]
  have hfin : B - A ≤ (T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * A) := by
    by_contra hcon
    push_neg at hcon
    have hy0 : 0 ≤ (T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * A) := by positivity
    nlinarith [hsq, hrhs, hcon, hy0]
  linarith
