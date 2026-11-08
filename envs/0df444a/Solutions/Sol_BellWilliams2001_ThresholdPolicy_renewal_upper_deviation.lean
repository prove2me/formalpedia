-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.renewal_upper_deviation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T07:24:49.607031+00:00
-- url     : https://prove2.me/submissions/1139f9ea-ee41-4344-b36a-315ca8eb5844

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BWRenewalUpperAux

open BellWilliams2001.ThresholdPolicy

lemma partialSum_mono {x : ℕ → ℝ} (hx : ∀ i, 1 ≤ i → 0 < x i) {n n' : ℕ} (h : n ≤ n') :
    partialSum x n ≤ partialSum x n' := by
  unfold partialSum
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl h)
  intro i hi _
  exact (hx i (Finset.mem_Icc.1 hi).1).le

lemma shifted_le_partialSum {x : ℕ → ℝ} (hx : ∀ i, 1 ≤ i → 0 < x i) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, x (j + 1) ≤ partialSum x (n + 1) := by
  induction n with
  | zero =>
    have : partialSum x (0 + 1) = x 1 := by simp [partialSum]
    rw [this]
    have h1 := hx 1 le_rfl
    simp
    linarith
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have : partialSum x (n + 1 + 1) = partialSum x (n + 1) + x (n + 1 + 1) := by
      unfold partialSum
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [this]
    linarith

/-- Final step: an EReal-sup bound from pointwise bounds. -/
lemma le_exp_neg_mul_iSup (p : ℝ≥0∞) (c : ℝ) (hc : 0 < c) (f : ℝ → EReal)
    (h : ∀ l, p ≤ EReal.exp (-((c : EReal) * f l))) :
    p ≤ EReal.exp (-((c : EReal) * ⨆ l, f l)) := by
  by_contra H
  push_neg at H
  have h1 : -((c : EReal) * ⨆ l, f l) < ENNReal.log p := by
    rw [← ENNReal.exp_log p] at H
    exact EReal.exp_lt_exp_iff.1 H
  rw [EReal.neg_lt_comm] at h1
  have hc0 : (0 : EReal) < c := by exact_mod_cast hc
  have hct : (c : EReal) ≠ ⊤ := EReal.coe_ne_top c
  have h2 : -ENNReal.log p / c < ⨆ l, f l := by
    rw [EReal.div_lt_iff hc0 hct, mul_comm]
    exact h1
  obtain ⟨l, hl⟩ := lt_iSup_iff.1 h2
  rw [EReal.div_lt_iff hc0 hct, mul_comm] at hl
  have h3 : -((c : EReal) * f l) < ENNReal.log p := by
    rw [EReal.neg_lt_comm]; exact hl
  have h4 := EReal.exp_lt_exp_iff.2 h3
  rw [ENNReal.exp_log] at h4
  exact absurd (h l) (not_le.2 h4)

end BWRenewalUpperAux

open BWRenewalUpperAux BellWilliams2001.ThresholdPolicy in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ζ : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ζ i))
    (hpos : ∀ i ω, 1 ≤ i → 0 < ζ i ω)
    (hindep : iIndepFun (fun i : ℕ => ζ (i + 1)) P)
    (hident : ∀ i, 2 ≤ i → IdentDistrib (ζ i) (ζ 2) P P)
    (hmgf : ∃ δ : ℝ, 0 < δ ∧ ∀ l ∈ Set.Ioo (-δ) δ, ∀ i, 2 ≤ i →
      Integrable (fun ω => Real.exp (l * ζ i ω)) P)
    (ν : ℝ) (hν : ν = 1 / ∫ ω, ζ 2 ω ∂P)
    (ε : ℝ) (hε : 0 < ε) (κ : ℝ) (hκ : κ = ν + ε) (t : ℝ) (ht : 2 / ε < t) :
    P {ω | ENNReal.ofReal (κ * t) < (renewalCount (partialSum (fun i => ζ i ω)) t : ℝ≥0∞)} ≤
        EReal.exp (-(((κ * t - 1 : ℝ) : EReal) *
          legendre (logMGF P (ζ 2)) (t / (κ * t - 1)))) ∧
      EReal.exp (-(((κ * t - 1 : ℝ) : EReal) *
          legendre (logMGF P (ζ 2)) (t / (κ * t - 1)))) ≤
        EReal.exp (-(((κ * t - 1 : ℝ) : EReal) *
          legendre (logMGF P (ζ 2)) (1 / (ν + ε / 2)))) := by
  obtain ⟨δ, hδ, hδint⟩ := hmgf
  have hp2 : ∀ ω, 0 < ζ 2 ω := fun ω => hpos 2 ω (by norm_num)
  set m := ∫ ω, ζ 2 ω ∂P with hm
  have hint2 : Integrable (ζ 2) P := by
    have hl : δ / 2 ∈ Set.Ioo (-δ) δ := ⟨by linarith, by linarith⟩
    have he := hδint (δ / 2) hl 2 le_rfl
    refine Integrable.mono' (he.div_const (δ / 2)) (hmeas 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (hp2 ω), le_div_iff₀ (by linarith)]
    have := Real.add_one_le_exp (δ / 2 * ζ 2 ω)
    nlinarith
  have hmpos : 0 < m := by
    rw [hm, integral_pos_iff_support_of_nonneg (fun ω => (hp2 ω).le) hint2]
    have : Function.support (ζ 2) = Set.univ :=
      Set.eq_univ_of_forall fun ω => (hp2 ω).ne'
    rw [this, measure_univ]; exact one_pos
  have hνpos : 0 < ν := by rw [hν]; positivity
  have hνm : ν * m = 1 := by rw [hν]; field_simp
  set Λ := logMGF P (ζ 2) with hΛdef
  have hΛ0 : Λ 0 = 0 := by simp [Λ, logMGF]
  have hΛneg : ∀ l : ℝ, l ≤ 0 → Λ l = ((Real.log (mgf (ζ 2) P l) : ℝ) : EReal) ∧
      0 < mgf (ζ 2) P l ∧ mgf (ζ 2) P l ≤ 1 := by
    intro l hl
    have hb : ∀ ω, Real.exp (l * ζ 2 ω) ≤ 1 := fun ω =>
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hl (hp2 ω).le)
    have hI : Integrable (fun ω => Real.exp (l * ζ 2 ω)) P := by
      refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hb ω
    have hM0 := mgf_pos hI
    have hM1 : mgf (ζ 2) P l ≤ 1 := by
      unfold mgf
      calc ∫ ω, Real.exp (l * ζ 2 ω) ∂P ≤ ∫ _ω, (1 : ℝ) ∂P :=
            integral_mono hI (integrable_const 1) hb
        _ = 1 := by simp
    refine ⟨?_, hM0, hM1⟩
    simp only [Λ, logMGF]
    rw [← ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
    exact ENNReal.log_ofReal_of_pos hM0
  have hΛpos : ∀ l : ℝ, 0 < l → ((l * m : ℝ) : EReal) ≤ Λ l := by
    intro l hl
    set g : Ω → ℝ := fun ω => Real.exp (l * m) * (1 - l * m) + Real.exp (l * m) * l * ζ 2 ω
    have hg : Integrable g P := (integrable_const _).add (hint2.const_mul _)
    have hgint : ∫ ω, g ω ∂P = Real.exp (l * m) := by
      simp only [g]
      rw [integral_add (integrable_const _) (hint2.const_mul _), integral_const,
        integral_const_mul, ← hm]
      simp
      ring
    have hgle : ∀ ω, g ω ≤ Real.exp (l * ζ 2 ω) := by
      intro ω
      have h1 := Real.add_one_le_exp (l * (ζ 2 ω - m))
      have h2 : Real.exp (l * ζ 2 ω) = Real.exp (l * m) * Real.exp (l * (ζ 2 ω - m)) := by
        rw [← Real.exp_add]; ring_nf
      rw [h2]
      have h3 := Real.exp_pos (l * m)
      simp only [g]
      nlinarith
    have hchain : ENNReal.ofReal (Real.exp (l * m)) ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (l * ζ 2 ω)) ∂P := by
      calc ENNReal.ofReal (Real.exp (l * m)) = ENNReal.ofReal (∫ ω, g ω ∂P) := by rw [hgint]
        _ ≤ ENNReal.ofReal (∫ ω, max (g ω) 0 ∂P) :=
            ENNReal.ofReal_le_ofReal (integral_mono hg hg.pos_part fun ω => le_max_left _ _)
        _ = ∫⁻ ω, ENNReal.ofReal (max (g ω) 0) ∂P :=
            ofReal_integral_eq_lintegral_ofReal hg.pos_part
              (Filter.Eventually.of_forall fun ω => le_max_right _ _)
        _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (l * ζ 2 ω)) ∂P := by
            apply lintegral_mono
            intro ω
            exact ENNReal.ofReal_le_ofReal (max_le (hgle ω) (Real.exp_pos _).le)
    have := ENNReal.log_le_log hchain
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp] at this
    exact this
  -- parameters
  have ht0 : 0 < t := lt_trans (by positivity) ht
  have hεt : 2 < ε * t := by
    have := (div_lt_iff₀ hε).1 ht
    linarith
  set c := κ * t - 1 with hcdef
  have hκt : κ * t = ν * t + ε * t := by rw [hκ]; ring
  have hc1 : 1 < c := by
    have : 0 < ν * t := by positivity
    linarith
  have hc0 : 0 < c := by linarith
  have htc : t / c < m := by
    rw [div_lt_iff₀ hc0]
    have : m * c = t + m * (ε * t) - m := by
      rw [hcdef, hκt]
      have : m * (ν * t) = t := by rw [← mul_assoc, mul_comm m ν, hνm, one_mul]
      linarith [this]
    rw [this]
    nlinarith
  set k := ⌊κ * t⌋₊ with hkdef
  have hk : c < k := by
    have := Nat.lt_floor_add_one (κ * t)
    rw [hcdef]
    linarith
  have hk1 : 1 ≤ k := by
    have : (1 : ℝ) < k := lt_trans hc1 hk
    exact_mod_cast this.le
  -- event inclusion
  set Y : ℕ → Ω → ℝ := fun j => ζ (j + 1) with hYdef
  set s := Finset.Icc 1 k with hs
  have hsub : {ω | ENNReal.ofReal (κ * t) <
      (renewalCount (partialSum (fun i => ζ i ω)) t : ℝ≥0∞)} ⊆
      {ω | (∑ j ∈ s, Y j) ω ≤ t} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [Finset.sum_apply]
    by_contra hcon
    push_neg at hcon
    apply (not_lt.2 _) hω
    have hle : renewalCount (partialSum fun i => ζ i ω) t ≤ (k : ℕ∞) := by
      unfold renewalCount
      apply iSup₂_le
      intro n hn
      by_contra hnk
      push_neg at hnk
      have hnk' : k + 1 ≤ n := by
        have : k < n := by exact_mod_cast hnk
        omega
      have h1 := partialSum_mono (x := fun i => ζ i ω) (fun i hi => hpos i ω hi) hnk'
      have h2 := shifted_le_partialSum (x := fun i => ζ i ω) (fun i hi => hpos i ω hi) k
      simp only [hYdef] at hcon
      linarith
    calc ((renewalCount (partialSum fun i => ζ i ω) t : ℕ∞) : ℝ≥0∞)
        ≤ ((k : ℕ∞) : ℝ≥0∞) := by exact_mod_cast hle
      _ = (k : ℝ≥0∞) := by simp
      _ ≤ ENNReal.ofReal (κ * t) := by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (Nat.floor_le (by linarith))
  have hYid : ∀ i ∈ s, ∀ j ∈ s, IdentDistrib (Y i) (Y j) P P := by
    intro i hi j hj
    rw [hs, Finset.mem_Icc] at hi hj
    exact (hident (i + 1) (by omega)).trans (hident (j + 1) (by omega)).symm
  have hYmeas : ∀ i, Measurable (Y i) := fun i => hmeas (i + 1)
  have hcard : s.card = k := by rw [hs, Nat.card_Icc]; omega
  have hbound : ∀ l : ℝ, P {ω | ENNReal.ofReal (κ * t) <
      (renewalCount (partialSum (fun i => ζ i ω)) t : ℝ≥0∞)} ≤
      EReal.exp (-((c : EReal) * (((l * (t / c) : ℝ) : EReal) - Λ l))) := by
    intro l
    rcases le_or_gt l 0 with hl | hl
    · obtain ⟨hΛl, hM0, hM1⟩ := hΛneg l hl
      have hSmeas : Measurable (∑ j ∈ s, Y j) := by
        have := Finset.measurable_sum s fun i _ => hYmeas i
        convert this using 1
        ext ω
        exact Finset.sum_apply ω s Y
      have hSnn : ∀ ω, 0 ≤ (∑ j ∈ s, Y j) ω := by
        intro ω
        rw [Finset.sum_apply]
        exact Finset.sum_nonneg fun j _ => (hpos (j + 1) ω (by omega)).le
      have hSint : Integrable (fun ω => Real.exp (l * (∑ j ∈ s, Y j) ω)) P := by
        refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg hl (hSnn ω))
      have hch := measure_le_le_exp_mul_mgf (X := ∑ j ∈ s, Y j) (μ := P) t hl hSint
      rw [mgf_sum_of_identDistrib hYmeas hindep hYid (j := 1) (by rw [hs]; simp; omega),
        hcard] at hch
      have hY1 : Y 1 = ζ 2 := rfl
      rw [hY1] at hch
      set M := mgf (ζ 2) P l
      have hMk : M ^ k = Real.exp (k * Real.log M) := by
        rw [Real.exp_nat_mul, Real.exp_log hM0]
      rw [hMk, ← Real.exp_add] at hch
      rw [hΛl, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_neg, EReal.exp_coe]
      calc P {ω | ENNReal.ofReal (κ * t) <
            (renewalCount (partialSum (fun i => ζ i ω)) t : ℝ≥0∞)}
          ≤ P {ω | (∑ j ∈ s, Y j) ω ≤ t} := measure_mono hsub
        _ = ENNReal.ofReal (P.real {ω | (∑ j ∈ s, Y j) ω ≤ t}) := (ofReal_measureReal).symm
        _ ≤ ENNReal.ofReal (Real.exp (-l * t + k * Real.log M)) := ENNReal.ofReal_le_ofReal hch
        _ ≤ ENNReal.ofReal (Real.exp (-(c * (l * (t / c) - Real.log M)))) := by
            apply ENNReal.ofReal_le_ofReal
            apply Real.exp_le_exp.2
            have hlog : Real.log M ≤ 0 := Real.log_nonpos hM0.le hM1
            have e1 : c * (l * (t / c)) = l * t := by field_simp
            have e2 : (k - c) * Real.log M ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (by linarith) hlog
            nlinarith
    · have hneg : ((l * (t / c) : ℝ) : EReal) - Λ l ≤ ((l * (t / c - m) : ℝ) : EReal) := by
        calc ((l * (t / c) : ℝ) : EReal) - Λ l ≤ ((l * (t / c) : ℝ) : EReal) - ((l * m : ℝ) : EReal) :=
              EReal.sub_le_sub le_rfl (hΛpos l hl)
          _ = ((l * (t / c - m) : ℝ) : EReal) := by rw [← EReal.coe_sub]; congr 1; ring
      have hc0' : (0 : EReal) ≤ c := by exact_mod_cast hc0.le
      have h1 : (c : EReal) * (((l * (t / c) : ℝ) : EReal) - Λ l) ≤ 0 := by
        calc (c : EReal) * (((l * (t / c) : ℝ) : EReal) - Λ l)
            ≤ (c : EReal) * ((l * (t / c - m) : ℝ) : EReal) := mul_le_mul_of_nonneg_left hneg hc0'
          _ = ((c * (l * (t / c - m)) : ℝ) : EReal) := by norm_cast
          _ ≤ 0 := by
              have : c * (l * (t / c - m)) ≤ 0 :=
                mul_nonpos_of_nonneg_of_nonpos hc0.le
                  (mul_nonpos_of_nonneg_of_nonpos hl.le (by linarith))
              exact_mod_cast this
      calc _ ≤ (1 : ℝ≥0∞) := prob_le_one
        _ ≤ _ := EReal.one_le_exp_iff.2 (EReal.neg_nonneg.2 h1)
  refine ⟨?_, ?_⟩
  · exact le_exp_neg_mul_iSup _ c hc0 _ hbound
  · apply EReal.exp_le_exp_iff.2
    apply EReal.neg_le_neg_iff.2
    have hc0' : (0 : EReal) ≤ c := by exact_mod_cast hc0.le
    apply mul_le_mul_of_nonneg_left _ hc0'
    have hy1 : t / c ≤ 1 / (ν + ε / 2) := by
      rw [div_le_div_iff₀ hc0 (by positivity), hcdef, hκt]
      nlinarith
    have hy2 : 1 / (ν + ε / 2) ≤ m := by
      have : m = 1 / ν := by field_simp; linarith [hνm]
      rw [this]
      exact one_div_le_one_div_of_le hνpos (by linarith)
    unfold legendre
    apply iSup_le
    intro l
    rcases le_or_gt l 0 with hl | hl
    · apply le_iSup_of_le l
      apply EReal.sub_le_sub _ le_rfl
      exact_mod_cast mul_le_mul_of_nonpos_left hy1 hl
    · apply le_iSup_of_le 0
      rw [hΛ0]
      simp only [zero_mul, EReal.coe_zero, sub_zero]
      calc ((l * (1 / (ν + ε / 2)) : ℝ) : EReal) - Λ l
          ≤ ((l * (1 / (ν + ε / 2)) : ℝ) : EReal) - ((l * m : ℝ) : EReal) :=
            EReal.sub_le_sub le_rfl (hΛpos l hl)
        _ = ((l * (1 / (ν + ε / 2) - m) : ℝ) : EReal) := by
            rw [← EReal.coe_sub]; congr 1; ring
        _ ≤ 0 := by
            have : l * (1 / (ν + ε / 2) - m) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos hl.le (by linarith)
            exact_mod_cast this
