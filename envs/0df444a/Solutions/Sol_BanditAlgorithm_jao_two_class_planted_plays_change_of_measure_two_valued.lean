-- Prove2me | solution 1 for BanditAlgorithm.jao_two_class_planted_plays_change_of_measure_two_valued
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-06T03:42:08.551517+00:00
-- url     : https://prove2.me/submissions/b859b18f-f722-4be8-9816-bc21e97cd1d0

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

namespace JaoL13

lemma toMeasure_apply {S : ℕ} (d : MDPStateDistribution S) (s : Set (Fin S)) :
    d.toMeasure s = ∑ i, (d.prob i : ℝ≥0∞) * s.indicator 1 i := by
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

/-- A probability vector whose mass at two distinct points already sums to one
vanishes everywhere else. -/
lemma two_point_vanish {S : ℕ} {w : Fin S → ℝ≥0} (hw : ∑ i, w i = 1)
    (p q : Fin S) (hpq : p ≠ q) (h2 : w p + w q = 1) :
    ∀ i, i ≠ p → i ≠ q → w i = 0 := by
  have hpair : ∑ i ∈ ({p, q} : Finset (Fin S)), w i = 1 := by
    rw [Finset.sum_pair hpq]; exact h2
  have hsplit : ∑ i ∈ (Finset.univ \ ({p, q} : Finset (Fin S))), w i
      + ∑ i ∈ ({p, q} : Finset (Fin S)), w i = ∑ i, w i :=
    Finset.sum_sdiff (Finset.subset_univ _)
  rw [hpair, hw] at hsplit
  have hz : ∑ i ∈ (Finset.univ \ ({p, q} : Finset (Fin S))), w i = 0 := by
    have hc : ((∑ i ∈ (Finset.univ \ ({p, q} : Finset (Fin S))), w i : ℝ≥0) : ℝ) + 1 = 1 := by
      exact_mod_cast congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) hsplit
    have hc0 : ((∑ i ∈ (Finset.univ \ ({p, q} : Finset (Fin S))), w i : ℝ≥0) : ℝ) = 0 := by
      linarith
    exact_mod_cast hc0
  intro i hip hiq
  refine (Finset.sum_eq_zero_iff.mp hz) i ?_
  simp [hip, hiq]

/-- Two probability vectors supported on the same pair of distinct points and
agreeing there are equal. -/
lemma two_point_ext {S : ℕ} {u v : Fin S → ℝ≥0} (hu : ∑ i, u i = 1) (hv : ∑ i, v i = 1)
    (p q : Fin S) (hpq : p ≠ q) (hup : u p = v p) (huq : u q = v q)
    (h2 : u p + u q = 1) : u = v := by
  have h2' : v p + v q = 1 := by rw [← hup, ← huq]; exact h2
  funext i
  by_cases hip : i = p
  · rw [hip]; exact hup
  by_cases hiq : i = q
  · rw [hiq]; exact huq
  rw [two_point_vanish hu p q hpq h2 i hip hiq, two_point_vanish hv p q hpq h2' i hip hiq]

lemma row_eq_of_two_point {S A : ℕ} (M M₀ : FiniteMDP S A) (s : Fin S) (b : Fin A)
    (p q : Fin S) (hpq : p ≠ q)
    (h1 : (M.P s b p : ℝ) = (M₀.P s b p : ℝ)) (h2 : (M.P s b q : ℝ) = (M₀.P s b q : ℝ))
    (h3 : (M.P s b p : ℝ) + (M.P s b q : ℝ) = 1) : M₀.P s b = M.P s b := by
  refine (two_point_ext (M.P_sum_one s b) (M₀.P_sum_one s b) p q hpq
    (NNReal.coe_injective h1) (NNReal.coe_injective h2) ?_).symm
  have hc : ((M.P s b p + M.P s b q : ℝ≥0) : ℝ) = ((1 : ℝ≥0) : ℝ) := by push_cast; exact h3
  exact NNReal.coe_injective hc

lemma visit_mono {S A T : ℕ} (h : MDPTrajectory S A T) (s : Fin S) (b : Fin A) {k l : ℕ}
    (hkl : k ≤ l) : mdpVisitCount h k s b ≤ mdpVisitCount h l s b := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨lt_of_lt_of_le hi.1 hkl, hi.2⟩

lemma visit_le {S A T : ℕ} (h : MDPTrajectory S A T) (s : Fin S) (b : Fin A) (k : ℕ) :
    mdpVisitCount h k s b ≤ T := by
  unfold mdpVisitCount
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)

lemma lintegral_visit_eq {S A T : ℕ} (μ : Measure (MDPTrajectory S A T)) [IsProbabilityMeasure μ]
    (s : Fin S) (b : Fin A) (k : ℕ) :
    (∫⁻ h, (mdpVisitCount h k s b : ℝ≥0∞) ∂μ)
      = ENNReal.ofReal (∫ h, (mdpVisitCount h k s b : ℝ) ∂μ) := by
  have hcast : ∀ h : MDPTrajectory S A T, ((mdpVisitCount h k s b : ℕ) : ℝ≥0∞)
      = (((mdpVisitCount h k s b : ℕ) : ℝ≥0) : ℝ≥0∞) := by
    intro h; simp
  simp_rw [hcast]
  rw [MeasureTheory.lintegral_coe_eq_integral _ Integrable.of_finite]
  norm_num

lemma le_of_sq_le_sq {x y : ℝ} (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  by_contra hc
  push_neg at hc
  nlinarith [le_trans hy hc.le]

end JaoL13

open JaoL13

theorem solution {S A : ℕ}
    (δ ε : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3) (hε0 : 0 < ε) (hεδ : ε ≤ δ)
    (ρ : Fin S → ℝ) (up down : Fin S → Fin S) (nav : Fin S → Fin A → Fin S)
    (hρ01 : ∀ s, ρ s = 0 ∨ ρ s = 1)
    (sStar : Fin S) (bStar : Fin A) (M M₀ : FiniteMDP S A)
    (hstar : ρ sStar = 0)
    (hrM : ∀ s b, M.r s b = ρ s)
    (hrow0M : ∀ s b, ρ s = 0 →
        ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
        (M.P s b (up s) : ℝ) = δ + (if (s, b) = (sStar, bStar) then ε else 0) ∧
        (M.P s b (nav s b) : ℝ) = 1 - δ - (if (s, b) = (sStar, bStar) then ε else 0))
    (hrow1M : ∀ s b, ρ s = 1 →
        ρ (down s) = 0 ∧ down s ≠ s ∧
        (M.P s b (down s) : ℝ) = δ ∧ (M.P s b s : ℝ) = 1 - δ)
    (hrM₀ : ∀ s b, M₀.r s b = ρ s)
    (hrow0M₀ : ∀ s b, ρ s = 0 →
        ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
        (M₀.P s b (up s) : ℝ) = δ ∧
        (M₀.P s b (nav s b) : ℝ) = 1 - δ)
    (hrow1M₀ : ∀ s b, ρ s = 1 →
        ρ (down s) = 0 ∧ down s ≠ s ∧
        (M₀.P s b (down s) : ℝ) = δ ∧ (M₀.P s b s : ℝ) = 1 - δ)
    (T : ℕ) (π : MDPPolicy S A) (s₀ : Fin S) :
    (∫ h, (mdpVisitCount h T sStar bStar : ℝ) ∂(mdpMeasure M (mdpStateDirac s₀) π T))
      ≤ (∫ h, (mdpVisitCount h T sStar bStar : ℝ) ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T))
        + (T : ℝ) / 2 * (ε / Real.sqrt δ)
            * Real.sqrt
                (2 * ∫ h, (mdpVisitCount h T sStar bStar : ℝ)
                        ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T)) := by
  -- basic numeric facts
  have hsum1 : δ + (δ + ε) ≤ 1 := by linarith
  have hpos1 : (0 : ℝ) < 1 - δ - ε := by linarith
  have hSpos : 0 < S := lt_of_le_of_lt (Nat.zero_le _) sStar.isLt
  haveI : NeZero S := ⟨hSpos.ne'⟩
  -- the planted and reference rows at the planted pair
  obtain ⟨hρu, hρv, huv, hMu₀, hMv₀⟩ := hrow0M sStar bStar hstar
  obtain ⟨-, -, -, hM₀u, hM₀v⟩ := hrow0M₀ sStar bStar hstar
  rw [if_pos rfl] at hMu₀ hMv₀
  have hMu : (M.P sStar bStar (up sStar) : ℝ) = δ + ε := hMu₀
  have hMv : (M.P sStar bStar (nav sStar bStar) : ℝ) = 1 - δ - ε := hMv₀
  -- the trajectory laws
  set P := mdpMeasure M₀ (mdpStateDirac s₀) π T with hPdef
  set Q := mdpMeasure M (mdpStateDirac s₀) π T with hQdef
  set EP : ℝ := ∫ h, (mdpVisitCount h T sStar bStar : ℝ) ∂P with hEPdef
  set EQ : ℝ := ∫ h, (mdpVisitCount h T sStar bStar : ℝ) ∂Q with hEQdef
  have hEP0 : 0 ≤ EP := by
    rw [hEPdef]
    exact integral_nonneg fun h ↦ by positivity
  -- the trivial horizon
  rcases Nat.eq_zero_or_pos T with hT0 | hTpos
  · subst hT0
    have hz : ∀ (μ : Measure (MDPTrajectory S A 0)),
        (∫ h, (mdpVisitCount h 0 sStar bStar : ℝ) ∂μ) = 0 := by
      intro μ
      have hzero : ∀ h : MDPTrajectory S A 0, (mdpVisitCount h 0 sStar bStar : ℝ) = 0 := by
        intro h
        simp [mdpVisitCount]
      simp [hzero]
    rw [hEQdef, hEPdef, hz, hz]
    simp
  -- rows agree away from the planted pair
  have hrow : ∀ (s : Fin S) (b : Fin A), (s, b) ≠ (sStar, bStar) → M₀.P s b = M.P s b := by
    intro s b hne
    rcases hρ01 s with hs | hs
    · obtain ⟨-, -, huv', hMu', hMv'⟩ := hrow0M s b hs
      obtain ⟨-, -, -, hM₀u', hM₀v'⟩ := hrow0M₀ s b hs
      rw [if_neg hne] at hMu' hMv'
      exact row_eq_of_two_point M M₀ s b (up s) (nav s b) huv'
        (by rw [hMu', hM₀u']; ring) (by rw [hMv', hM₀v']; ring) (by rw [hMu', hMv']; ring)
    · obtain ⟨-, hdn, hMd, hMs⟩ := hrow1M s b hs
      obtain ⟨-, -, hM₀d, hM₀s⟩ := hrow1M₀ s b hs
      exact row_eq_of_two_point M M₀ s b (down s) s hdn
        (by rw [hMd, hM₀d]) (by rw [hMs, hM₀s]) (by rw [hMd, hMs]; ring)
  -- the reference row vanishes off the pair `{up sStar, nav sStar bStar}`
  have hM₀sum : (M₀.P sStar bStar (up sStar) : ℝ)
      + (M₀.P sStar bStar (nav sStar bStar) : ℝ) = 1 := by rw [hM₀u, hM₀v]; ring
  have hM₀vanish : ∀ i, i ≠ up sStar → i ≠ nav sStar bStar → M₀.P sStar bStar i = 0 := by
    refine two_point_vanish (M₀.P_sum_one sStar bStar) _ _ huv (NNReal.coe_injective ?_)
    push_cast
    exact hM₀sum
  -- absolute continuity of the reference row with respect to the planted row
  have hac : (M₀.transitionDist sStar bStar).toMeasure
      ≪ (M.transitionDist sStar bStar).toMeasure := by
    intro s hs
    rw [toMeasure_apply] at hs ⊢
    refine Finset.sum_eq_zero ?_
    intro i _
    have hzero := (Finset.sum_eq_zero_iff.mp hs) i (Finset.mem_univ i)
    rcases mul_eq_zero.mp hzero with hh | hh
    · have hMi : M.P sStar bStar i = 0 := ENNReal.coe_eq_zero.mp hh
      have hiu : i ≠ up sStar := by
        intro hi
        rw [hi] at hMi
        have : (M.P sStar bStar (up sStar) : ℝ) = 0 := by rw [hMi]; simp
        rw [hMu] at this; linarith
      have hiv : i ≠ nav sStar bStar := by
        intro hi
        rw [hi] at hMi
        have : (M.P sStar bStar (nav sStar bStar) : ℝ) = 0 := by rw [hMi]; simp
        rw [hMv] at this; linarith
      have h₀ : (M₀.transitionDist sStar bStar).prob i = 0 := hM₀vanish i hiu hiv
      simp [h₀]
    · rw [hh, mul_zero]
  -- the two rows, as measures on `Fin S`
  have hR0u : ((M₀.transitionDist sStar bStar).toMeasure).real {up sStar} = δ := by
    rw [toMeasure_real_singleton, FiniteMDP.transitionDist]; exact hM₀u
  have hR0v : ((M₀.transitionDist sStar bStar).toMeasure).real {nav sStar bStar} = 1 - δ := by
    rw [toMeasure_real_singleton, FiniteMDP.transitionDist]; exact hM₀v
  have hR1u : ((M.transitionDist sStar bStar).toMeasure).real {up sStar} = δ + ε := by
    rw [toMeasure_real_singleton, FiniteMDP.transitionDist]; exact hMu
  have hR1v : ((M.transitionDist sStar bStar).toMeasure).real {nav sStar bStar}
      = 1 - δ - ε := by
    rw [toMeasure_real_singleton, FiniteMDP.transitionDist]; exact hMv
  -- the row divergence is the Bernoulli one
  have hkl : (klDiv (M₀.transitionDist sStar bStar).toMeasure
      (M.transitionDist sStar bStar).toMeasure).toReal
      = bernoulliRelativeEntropy δ (δ + ε) := by
    rw [InformationTheory.categorical_toReal_klDiv_eq_sum _ _ hac]
    have hvan : ∀ x ∈ (Finset.univ : Finset (Fin S)),
        x ∉ ({up sStar, nav sStar bStar} : Finset (Fin S)) →
        ((M₀.transitionDist sStar bStar).toMeasure).real {x} *
          Real.log (((M₀.transitionDist sStar bStar).toMeasure).real {x} /
            ((M.transitionDist sStar bStar).toMeasure).real {x}) = 0 := by
      intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      have hx0 : ((M₀.transitionDist sStar bStar).toMeasure).real {x} = 0 := by
        rw [toMeasure_real_singleton, FiniteMDP.transitionDist]
        simp only
        rw [hM₀vanish x hx.1 hx.2]
        simp
      rw [hx0]; ring
    rw [← Finset.sum_subset (Finset.subset_univ _) hvan, Finset.sum_pair huv,
      hR0u, hR0v, hR1u, hR1v, bernoulliRelativeEntropy]
    have h1 : (1 : ℝ) - (δ + ε) = 1 - δ - ε := by ring
    rw [h1]
  have hkltop : klDiv (M₀.transitionDist sStar bStar).toMeasure
      (M.transitionDist sStar bStar).toMeasure ≠ ∞ :=
    klDiv_ne_top hac Integrable.of_finite
  have hklb : (klDiv (M₀.transitionDist sStar bStar).toMeasure
      (M.transitionDist sStar bStar).toMeasure).toReal ≤ ε ^ 2 / δ := by
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
      (M₀ := M₀) (M₁ := M) (μ0 := mdpStateDirac s₀) (π := π)
      (sStar := sStar) (aStar := bStar) hrow hac T
  set L : ℝ := ∫ h, (mdpVisitCount h (T - 1) sStar bStar : ℝ) ∂P with hLdef
  have hL0 : 0 ≤ L := by
    rw [hLdef]; exact integral_nonneg fun h ↦ by positivity
  have hLEP : L ≤ EP := by
    rw [hLdef, hEPdef]
    apply integral_mono Integrable.of_finite Integrable.of_finite
    intro h
    exact_mod_cast Nat.cast_le.mpr (visit_mono h sStar bStar (Nat.sub_le T 1))
  have hlint : (∫⁻ h, (mdpVisitCount h (T - 1) sStar bStar : ℝ≥0∞) ∂P) = ENNReal.ofReal L :=
    lintegral_visit_eq P sStar bStar (T - 1)
  have hPQtop : klDiv P Q ≠ ∞ := by
    rw [hPdef, hQdef] at *
    rw [hdecomp, hlint]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hkltop
  have hPQval : (klDiv P Q).toReal ≤ L * (ε ^ 2 / δ) := by
    rw [hdecomp, hlint, ENNReal.toReal_mul, ENNReal.toReal_ofReal hL0]
    exact mul_le_mul_of_nonneg_left hklb hL0
  -- Pinsker
  have hTpos' : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hpin := BanditAlgorithm.pinsker_squared_bounded_expectation_difference P Q
      (fun h ↦ (mdpVisitCount h T sStar bStar : ℝ) / T)
      (measurable_of_countable _)
      (fun h ↦ by positivity)
      (fun h ↦ by
        rw [div_le_one hTpos']
        exact_mod_cast visit_le h sStar bStar T)
      hPQtop
  rw [integral_div, integral_div, ← hEPdef, ← hEQdef] at hpin
  -- from here on only the three real numbers matter
  clear_value EP EQ L
  clear hEPdef hEQdef hLdef hlint hdecomp hac hrow
  -- combine
  have hsq : (EQ - EP) ^ 2 ≤ (T : ℝ) ^ 2 * EP * ε ^ 2 / (2 * δ) := by
    have h1 : 2 * (EQ / T - EP / T) ^ 2 ≤ L * (ε ^ 2 / δ) := le_trans hpin hPQval
    have h2 : (EQ / T - EP / T) ^ 2 = (EQ - EP) ^ 2 / (T : ℝ) ^ 2 := by
      field_simp
    rw [h2] at h1
    have h3 : L * (ε ^ 2 / δ) ≤ EP * (ε ^ 2 / δ) := by
      apply mul_le_mul_of_nonneg_right hLEP
      positivity
    have h4 : 2 * ((EQ - EP) ^ 2 / (T : ℝ) ^ 2) ≤ EP * (ε ^ 2 / δ) := le_trans h1 h3
    have hT2 : (0 : ℝ) < (T : ℝ) ^ 2 := by positivity
    have h5 : (EQ - EP) ^ 2 / (T : ℝ) ^ 2 ≤ EP * (ε ^ 2 / δ) / 2 := by linarith
    calc (EQ - EP) ^ 2 = ((EQ - EP) ^ 2 / (T : ℝ) ^ 2) * (T : ℝ) ^ 2 := by field_simp
      _ ≤ (EP * (ε ^ 2 / δ) / 2) * (T : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h5 hT2.le
      _ = (T : ℝ) ^ 2 * EP * ε ^ 2 / (2 * δ) := by field_simp
  have hrhs : ((T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * EP)) ^ 2
      = (T : ℝ) ^ 2 * EP * ε ^ 2 / (2 * δ) := by
    have hs1 : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ0.le
    have hs2 : Real.sqrt (2 * EP) ^ 2 = 2 * EP := Real.sq_sqrt (by linarith)
    have hsne : Real.sqrt δ ≠ 0 := by positivity
    field_simp
    nlinarith [hs1, hs2]
  have hy0 : 0 ≤ (T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * EP) :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity)) (Real.sqrt_nonneg _)
  have hfin : EQ - EP ≤ (T : ℝ) / 2 * (ε / Real.sqrt δ) * Real.sqrt (2 * EP) :=
    le_of_sq_le_sq hy0 (by rw [hrhs]; exact hsq)
  linarith
