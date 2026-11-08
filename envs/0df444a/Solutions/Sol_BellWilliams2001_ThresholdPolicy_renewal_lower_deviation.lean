-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.renewal_lower_deviation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T07:28:00.449434+00:00
-- url     : https://prove2.me/submissions/98847f9e-1892-4b97-8ae8-00ceea351066

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BWRenewalLowerAux

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


lemma partialSum_succ_eq (x : ℕ → ℝ) (n : ℕ) :
    partialSum x (n + 1) = x 1 + ∑ j ∈ Finset.Icc 1 n, x (j + 1) := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have : partialSum x (n + 1 + 1) = partialSum x (n + 1) + x (n + 1 + 1) := by
      unfold partialSum
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [this, ih]
    ring

end BWRenewalLowerAux

open BWRenewalLowerAux BellWilliams2001.ThresholdPolicy in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ζ : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (ζ i))
    (hpos : ∀ i ω, 1 ≤ i → 0 < ζ i ω)
    (hindep : iIndepFun (fun i : ℕ => ζ (i + 1)) P)
    (hident : ∀ i, 2 ≤ i → IdentDistrib (ζ i) (ζ 2) P P)
    (hmgf : ∃ δ : ℝ, 0 < δ ∧ ∀ l ∈ Set.Ioo (-δ) δ, ∀ i, 2 ≤ i →
      Integrable (fun ω => Real.exp (l * ζ i ω)) P)
    (ν : ℝ) (hν : ν = 1 / ∫ ω, ζ 2 ω ∂P)
    (ε : ℝ) (hε : 0 < ε) (χ : ℝ) (hχ : χ = ν - ε) (hχpos : 0 < χ)
    (δ : ℝ) (hδ : δ = ε / (2 * ν)) (t : ℝ) (ht : 0 ≤ t) :
    P {ω | (renewalCount (partialSum (fun i => ζ i ω)) t : ℝ≥0∞) < ENNReal.ofReal (χ * t)} ≤
      EReal.exp (-(((χ * t : ℝ) : EReal) *
          legendre (logMGF P (ζ 2)) ((1 / ν) * (1 + ε / (2 * (ν - ε)))))) +
        P {ω | δ * t < ζ 1 ω} := by
  obtain ⟨δ₀, hδ₀, hδint⟩ := hmgf
  have hp2 : ∀ ω, 0 < ζ 2 ω := fun ω => hpos 2 ω (by norm_num)
  set m := ∫ ω, ζ 2 ω ∂P with hm
  have hint2 : Integrable (ζ 2) P := by
    have hl : δ₀ / 2 ∈ Set.Ioo (-δ₀) δ₀ := ⟨by linarith, by linarith⟩
    have he := hδint (δ₀ / 2) hl 2 le_rfl
    refine Integrable.mono' (he.div_const (δ₀ / 2)) (hmeas 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (hp2 ω), le_div_iff₀ (by linarith)]
    have := Real.add_one_le_exp (δ₀ / 2 * ζ 2 ω)
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
  have hΛpos : ∀ l : ℝ, ((l * m : ℝ) : EReal) ≤ Λ l := by
    intro l
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
  -- t = 0 is trivial
  rcases eq_or_lt_of_le ht with ht0 | ht0
  · subst ht0
    simp
  have hχt : 0 < χ * t := by positivity
  set y := (1 / ν) * (1 + ε / (2 * (ν - ε))) with hy
  have hyχ : y * χ = 1 - δ := by
    rw [hy, hχ, hδ]
    have : ν - ε ≠ 0 := by rw [← hχ]; exact hχpos.ne'
    field_simp
    ring
  have hym : m ≤ y := by
    have hm' : m = 1 / ν := by field_simp; linarith [hνm]
    rw [hy, hm']
    have : 0 ≤ ε / (2 * (ν - ε)) := by
      apply div_nonneg hε.le
      linarith
    have : 0 < 1 / ν := by positivity
    nlinarith
  set n := ⌈χ * t⌉₊ with hndef
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2 hχt))
  set Y : ℕ → Ω → ℝ := fun j => ζ (j + 1) with hYdef
  set s := Finset.Icc 1 (n - 1) with hs
  have hcard : (s.card : ℝ) < χ * t := by
    rw [hs, Nat.card_Icc]
    have h1 := Nat.ceil_lt_add_one hχt.le
    have : n - 1 + 1 - 1 = n - 1 := by omega
    rw [this]
    have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1]; simp
    rw [this]
    linarith
  have hsub : {ω | (renewalCount (partialSum (fun i => ζ i ω)) t : ℝ≥0∞) <
      ENNReal.ofReal (χ * t)} ⊆ {ω | (1 - δ) * t ≤ (∑ j ∈ s, Y j) ω} ∪ {ω | δ * t < ζ 1 ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    have hX : t < partialSum (fun i => ζ i ω) n := by
      by_contra hcon
      push_neg at hcon
      apply (not_lt.2 _) hω
      have hle : (n : ℕ∞) ≤ renewalCount (partialSum fun i => ζ i ω) t := by
        unfold renewalCount
        exact le_iSup₂ (f := fun (k : ℕ) (_ : partialSum (fun i => ζ i ω) k ≤ t) => (k : ℕ∞))
          n hcon
      calc ENNReal.ofReal (χ * t) ≤ (n : ℝ≥0∞) := by
            rw [← ENNReal.ofReal_natCast]
            exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
        _ = ((n : ℕ∞) : ℝ≥0∞) := by simp
        _ ≤ _ := by exact_mod_cast hle
    have hXeq := partialSum_succ_eq (fun i => ζ i ω) (n - 1)
    rw [show n - 1 + 1 = n by omega] at hXeq
    rcases le_or_gt (ζ 1 ω) (δ * t) with h1 | h1
    · left
      simp only [Set.mem_setOf_eq]
      rw [Finset.sum_apply]
      simp only [hYdef]
      linarith
    · right
      exact h1
  have hYid : ∀ i ∈ s, IdentDistrib (Y i) (ζ 2) P P := by
    intro i hi
    rw [hs, Finset.mem_Icc] at hi
    exact hident (i + 1) (by omega)
  have hYmeas : ∀ i, Measurable (Y i) := fun i => hmeas (i + 1)
  have hbound : ∀ l : ℝ, P {ω | (1 - δ) * t ≤ (∑ j ∈ s, Y j) ω} ≤
      EReal.exp (-(((χ * t : ℝ) : EReal) * (((l * y : ℝ) : EReal) - Λ l))) := by
    intro l
    have hχt' : (0 : EReal) ≤ ((χ * t : ℝ) : EReal) := by exact_mod_cast hχt.le
    rcases lt_or_ge l 0 with hl | hl
    · have h1 : ((χ * t : ℝ) : EReal) * (((l * y : ℝ) : EReal) - Λ l) ≤ 0 := by
        calc ((χ * t : ℝ) : EReal) * (((l * y : ℝ) : EReal) - Λ l)
            ≤ ((χ * t : ℝ) : EReal) * ((l * (y - m) : ℝ) : EReal) := by
              apply mul_le_mul_of_nonneg_left _ hχt'
              calc ((l * y : ℝ) : EReal) - Λ l ≤ ((l * y : ℝ) : EReal) - ((l * m : ℝ) : EReal) :=
                    EReal.sub_le_sub le_rfl (hΛpos l)
                _ = ((l * (y - m) : ℝ) : EReal) := by rw [← EReal.coe_sub]; congr 1; ring
          _ = (((χ * t) * (l * (y - m)) : ℝ) : EReal) := by norm_cast
          _ ≤ 0 := by
              have : (χ * t) * (l * (y - m)) ≤ 0 :=
                mul_nonpos_of_nonneg_of_nonpos hχt.le
                  (mul_nonpos_of_nonpos_of_nonneg hl.le (by linarith))
              exact_mod_cast this
      calc _ ≤ (1 : ℝ≥0∞) := prob_le_one
        _ ≤ _ := EReal.one_le_exp_iff.2 (EReal.neg_nonneg.2 h1)
    · by_cases hfin : ∫⁻ ω, ENNReal.ofReal (Real.exp (l * ζ 2 ω)) ∂P = ⊤
      · have hΛtop : Λ l = ⊤ := by simp only [Λ, logMGF, hfin, ENNReal.log_top]
        rw [hΛtop, EReal.sub_top, EReal.coe_mul_bot_of_pos hχt,
          EReal.neg_bot, EReal.exp_top]
        exact le_top
      · have hI : Integrable (fun ω => Real.exp (l * ζ 2 ω)) P := by
          refine ⟨by fun_prop, ?_⟩
          unfold HasFiniteIntegral
          simp_rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]
          exact lt_top_iff_ne_top.2 hfin
        have hM1 : 1 ≤ mgf (ζ 2) P l := by
          unfold mgf
          calc (1 : ℝ) = ∫ _ω, (1 : ℝ) ∂P := by simp
            _ ≤ ∫ ω, Real.exp (l * ζ 2 ω) ∂P := integral_mono (integrable_const 1) hI
                fun ω => Real.one_le_exp (mul_nonneg hl (hp2 ω).le)
        have hM0 : 0 < mgf (ζ 2) P l := by linarith
        have hΛl : Λ l = ((Real.log (mgf (ζ 2) P l) : ℝ) : EReal) := by
          simp only [Λ, logMGF]
          rw [← ofReal_integral_eq_lintegral_ofReal hI
            (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
          exact ENNReal.log_ofReal_of_pos hM0
        have hYI : ∀ i ∈ s, Integrable (fun ω => Real.exp (l * Y i ω)) P := by
          intro i hi
          have := (hYid i hi).comp (show Measurable fun x : ℝ => Real.exp (l * x) by fun_prop)
          exact this.integrable_iff.2 hI
        have hSint := hindep.integrable_exp_mul_sum (t := l) hYmeas hYI
        have hch := measure_ge_le_exp_mul_mgf (X := ∑ j ∈ s, Y j) (μ := P) ((1 - δ) * t) hl hSint
        rw [hindep.mgf_sum hYmeas, Finset.prod_congr rfl (fun i hi =>
          mgf_congr_of_identDistrib (Y i) (ζ 2) (hYid i hi) l), Finset.prod_const] at hch
        set M := mgf (ζ 2) P l
        have hMk : M ^ s.card = Real.exp (s.card * Real.log M) := by
          rw [Real.exp_nat_mul, Real.exp_log hM0]
        rw [hMk, ← Real.exp_add] at hch
        rw [hΛl, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_neg, EReal.exp_coe]
        calc P {ω | (1 - δ) * t ≤ (∑ j ∈ s, Y j) ω}
            = ENNReal.ofReal (P.real {ω | (1 - δ) * t ≤ (∑ j ∈ s, Y j) ω}) :=
              (ofReal_measureReal).symm
          _ ≤ ENNReal.ofReal (Real.exp (-l * ((1 - δ) * t) + s.card * Real.log M)) :=
              ENNReal.ofReal_le_ofReal hch
          _ ≤ ENNReal.ofReal (Real.exp (-((χ * t) * (l * y - Real.log M)))) := by
              apply ENNReal.ofReal_le_ofReal
              apply Real.exp_le_exp.2
              have hlog : 0 ≤ Real.log M := Real.log_nonneg hM1
              have e1 : (χ * t) * (l * y) = l * ((1 - δ) * t) := by
                rw [← hyχ]; ring
              have e2 : (s.card - χ * t) * Real.log M ≤ 0 :=
                mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog
              nlinarith
  calc _ ≤ P ({ω | (1 - δ) * t ≤ (∑ j ∈ s, Y j) ω} ∪ {ω | δ * t < ζ 1 ω}) := measure_mono hsub
    _ ≤ P {ω | (1 - δ) * t ≤ (∑ j ∈ s, Y j) ω} + P {ω | δ * t < ζ 1 ω} := measure_union_le _ _
    _ ≤ _ := by
        gcongr
        exact le_exp_neg_mul_iSup _ (χ * t) hχt _ hbound
