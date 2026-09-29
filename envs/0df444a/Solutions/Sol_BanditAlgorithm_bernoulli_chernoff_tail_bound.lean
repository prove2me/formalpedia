-- Prove2me | solution 1 for BanditAlgorithm.bernoulli_chernoff_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-28T21:06:08.082675+00:00
-- url     : https://prove2.me/submissions/c0c436ee-d0f7-4621-b0ff-3992b2d89c20

import Definitions.Def_bernoulliRelativeEntropy
import Mathlib.Probability.Moments.Basic

open MeasureTheory ProbabilityTheory Real Filter

namespace BanditAlgorithm

/-!
Lattimore--Szepesvári, *Bandit Algorithms*, Lemma 10.3, printed p. 135,
equations (10.1)--(10.2).  This follows the displayed exponential-Markov
argument in the source: factor the Bernoulli moment-generating function and
optimize its parameter.
-/

private lemma bernoulli_exp_integrable
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} {μ t : ℝ} (hX : Measurable X)
    (h_law : Measure.map X P =
      ENNReal.ofReal μ • Measure.dirac (1 : ℝ) +
        ENNReal.ofReal (1 - μ) • Measure.dirac (0 : ℝ)) :
    Integrable (fun ω ↦ exp (t * X ω)) P := by
  change Integrable ((fun x : ℝ ↦ exp (t * x)) ∘ X) P
  rw [← integrable_map_measure (by fun_prop) hX.aemeasurable]
  rw [h_law]
  exact
    (integrable_dirac (f := fun x : ℝ ↦ exp (t * x)) (by simp)).smul_measure
      ENNReal.ofReal_ne_top |>.add_measure <|
    (integrable_dirac (f := fun x : ℝ ↦ exp (t * x)) (by simp)).smul_measure
      ENNReal.ofReal_ne_top

private lemma bernoulli_mgf_eq
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} {μ t : ℝ} (hX : Measurable X)
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1)
    (h_law : Measure.map X P =
      ENNReal.ofReal μ • Measure.dirac (1 : ℝ) +
        ENNReal.ofReal (1 - μ) • Measure.dirac (0 : ℝ)) :
    mgf X P t = μ * exp t + (1 - μ) := by
  rw [← mgf_id_map hX.aemeasurable, h_law]
  rw [mgf_add_measure]
  · simp [mgf, ENNReal.toReal_ofReal hμ.1,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hμ.2)]
  · exact
      (integrable_dirac (f := fun x : ℝ ↦ exp (t * x)) (by simp)).smul_measure
        ENNReal.ofReal_ne_top
  · exact
      (integrable_dirac (f := fun x : ℝ ↦ exp (t * x)) (by simp)).smul_measure
        ENNReal.ofReal_ne_top

private lemma bernoulli_sum_upper_chernoff
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {μ r t : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X P)
    (h_law : ∀ i, Measure.map (X i) P =
      ENNReal.ofReal μ • Measure.dirac (1 : ℝ) +
        ENNReal.ofReal (1 - μ) • Measure.dirac (0 : ℝ))
    (ht : 0 ≤ t) :
    P.real {ω | (n : ℝ) * r ≤ ∑ i, X i ω} ≤
      exp (-t * ((n : ℝ) * r)) * (μ * exp t + (1 - μ)) ^ n := by
  have h_int :
      Integrable (fun ω ↦ exp (t * (∑ i, X i) ω)) P :=
    h_indep.integrable_exp_mul_sum h_meas
      (fun i _ ↦ bernoulli_exp_integrable (h_meas i) (h_law i))
  have hbound :=
    measure_ge_le_exp_mul_mgf (X := ∑ i, X i) ((n : ℝ) * r) ht h_int
  rw [h_indep.mgf_sum h_meas Finset.univ] at hbound
  simp_rw [bernoulli_mgf_eq (h_meas _) hμ (h_law _)] at hbound
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_apply] using hbound

private lemma bernoulli_sum_lower_chernoff
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {μ r t : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X P)
    (h_law : ∀ i, Measure.map (X i) P =
      ENNReal.ofReal μ • Measure.dirac (1 : ℝ) +
        ENNReal.ofReal (1 - μ) • Measure.dirac (0 : ℝ))
    (ht : t ≤ 0) :
    P.real {ω | (∑ i, X i ω) ≤ (n : ℝ) * r} ≤
      exp (-t * ((n : ℝ) * r)) * (μ * exp t + (1 - μ)) ^ n := by
  have h_int :
      Integrable (fun ω ↦ exp (t * (∑ i, X i) ω)) P :=
    h_indep.integrable_exp_mul_sum h_meas
      (fun i _ ↦ bernoulli_exp_integrable (h_meas i) (h_law i))
  have hbound :=
    measure_le_le_exp_mul_mgf (X := ∑ i, X i) ((n : ℝ) * r) ht h_int
  rw [h_indep.mgf_sum h_meas Finset.univ] at hbound
  simp_rw [bernoulli_mgf_eq (h_meas _) hμ (h_law _)] at hbound
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_apply] using hbound

private lemma bernoulli_chernoff_factor_eq
    {n : ℕ} {μ r : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hr0 : 0 < r) (hr1 : r < 1) :
    let t := log (r * (1 - μ) / (μ * (1 - r)))
    exp (-t * ((n : ℝ) * r)) * (μ * exp t + (1 - μ)) ^ n =
      exp (-((n : ℝ) * bernoulliRelativeEntropy r μ)) := by
  dsimp only
  have hOneMu : 0 < 1 - μ := sub_pos.mpr hμ1
  have hOneR : 0 < 1 - r := sub_pos.mpr hr1
  have hratio :
      0 < r * (1 - μ) / (μ * (1 - r)) :=
    div_pos (mul_pos hr0 hOneMu) (mul_pos hμ0 hOneR)
  have hmgf :
      μ * exp (log (r * (1 - μ) / (μ * (1 - r)))) + (1 - μ) =
        (1 - μ) / (1 - r) := by
    rw [exp_log hratio]
    field_simp [ne_of_gt hμ0, ne_of_gt hOneR]
    ring
  rw [hmgf]
  have hquot : 0 < (1 - μ) / (1 - r) := div_pos hOneMu hOneR
  rw [← exp_log (pow_pos hquot n), ← exp_add]
  congr 1
  rw [log_pow, bernoulliRelativeEntropy]
  rw [log_div (ne_of_gt hr0) (ne_of_gt hμ0)]
  rw [log_div (ne_of_gt hOneR) (ne_of_gt hOneMu)]
  rw [log_div (ne_of_gt hOneMu) (ne_of_gt hOneR)]
  rw [log_div (mul_ne_zero (ne_of_gt hr0) (ne_of_gt hOneMu))
    (mul_ne_zero (ne_of_gt hμ0) (ne_of_gt hOneR))]
  rw [log_mul (ne_of_gt hr0) (ne_of_gt hOneMu)]
  rw [log_mul (ne_of_gt hμ0) (ne_of_gt hOneR)]
  ring

private lemma bernoulli_entropy_self
    {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    bernoulliRelativeEntropy μ μ = 0 := by
  rcases eq_or_ne μ 0 with rfl | hμ0
  · simp [bernoulliRelativeEntropy]
  rcases eq_or_ne μ 1 with rfl | hμ1
  · simp [bernoulliRelativeEntropy]
  have hOneMu : 1 - μ ≠ 0 := sub_ne_zero.mpr hμ1.symm
  simp [bernoulliRelativeEntropy, div_self hμ0, div_self hOneMu]

private lemma bernoulli_entropy_one_exp
    {n : ℕ} {μ : ℝ} (hμ0 : 0 < μ) :
    μ ^ n = exp (-((n : ℝ) * bernoulliRelativeEntropy 1 μ)) := by
  rw [bernoulliRelativeEntropy]
  simp only [one_mul, one_div, sub_self, zero_mul, add_zero]
  rw [log_inv]
  rw [show -((n : ℝ) * -log μ) = (n : ℝ) * log μ by ring,
    Real.exp_nat_mul, exp_log hμ0]

private lemma bernoulli_entropy_zero_exp
    {n : ℕ} {μ : ℝ} (hμ1 : μ < 1) :
    (1 - μ) ^ n = exp (-((n : ℝ) * bernoulliRelativeEntropy 0 μ)) := by
  have hOneMu : 0 < 1 - μ := sub_pos.mpr hμ1
  rw [bernoulliRelativeEntropy]
  norm_num only [zero_div, log_zero, zero_mul, zero_add, one_div, one_mul,
    sub_zero]
  rw [log_inv]
  rw [show -((n : ℝ) * -log (1 - μ)) = (n : ℝ) * log (1 - μ) by ring,
    Real.exp_nat_mul, exp_log hOneMu]

private lemma bernoulli_sum_upper_endpoint
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hμ0 : 0 < μ)
    (h_meas : ∀ i, Measurable (X i)) (h_indep : iIndepFun X P)
    (h_law : ∀ i, Measure.map (X i) P =
      ENNReal.ofReal μ • Measure.dirac (1 : ℝ) +
        ENNReal.ofReal (1 - μ) • Measure.dirac (0 : ℝ)) :
    P.real {ω | (n : ℝ) ≤ ∑ i, X i ω} ≤
      exp (-((n : ℝ) * bernoulliRelativeEntropy 1 μ)) := by
  have hbound (k : ℕ) :
      P.real {ω | (n : ℝ) ≤ ∑ i, X i ω} ≤
        (μ + (1 - μ) * exp (-(k : ℝ))) ^ n := by
    have h := bernoulli_sum_upper_chernoff hμ h_meas h_indep h_law
      (r := (1 : ℝ)) (t := (k : ℝ)) (by positivity)
    calc
      P.real {ω | (n : ℝ) ≤ ∑ i, X i ω}
          ≤ exp (-(k : ℝ) * ((n : ℝ) * 1)) *
              (μ * exp (k : ℝ) + (1 - μ)) ^ n := by simpa using h
      _ = (μ + (1 - μ) * exp (-(k : ℝ))) ^ n := by
        rw [show -(k : ℝ) * ((n : ℝ) * 1) = (n : ℝ) * (-(k : ℝ)) by ring,
          Real.exp_nat_mul, ← mul_pow]
        congr 1
        rw [exp_neg]
        field_simp [exp_ne_zero]
  have hexp :
      Tendsto (fun k : ℕ ↦ exp (-(k : ℝ))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hconstMu :
      Tendsto (fun _ : ℕ ↦ μ) atTop (nhds μ) := tendsto_const_nhds
  have hconstOneMu :
      Tendsto (fun _ : ℕ ↦ (1 - μ)) atTop (nhds (1 - μ)) := tendsto_const_nhds
  have hlim :
      Tendsto (fun k : ℕ ↦ (μ + (1 - μ) * exp (-(k : ℝ))) ^ n)
        atTop (nhds (μ ^ n)) := by
    simpa using (hconstMu.add (hconstOneMu.mul hexp)).pow n
  rw [← bernoulli_entropy_one_exp hμ0]
  exact ge_of_tendsto' hlim hbound

private lemma bernoulli_sum_lower_endpoint
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {X : Fin n → Ω → ℝ} {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hμ1 : μ < 1)
    (h_meas : ∀ i, Measurable (X i)) (h_indep : iIndepFun X P)
    (h_law : ∀ i, Measure.map (X i) P =
      ENNReal.ofReal μ • Measure.dirac (1 : ℝ) +
        ENNReal.ofReal (1 - μ) • Measure.dirac (0 : ℝ)) :
    P.real {ω | (∑ i, X i ω) ≤ 0} ≤
      exp (-((n : ℝ) * bernoulliRelativeEntropy 0 μ)) := by
  have hbound (k : ℕ) :
      P.real {ω | (∑ i, X i ω) ≤ 0} ≤
        (μ * exp (-(k : ℝ)) + (1 - μ)) ^ n := by
    have h := bernoulli_sum_lower_chernoff hμ h_meas h_indep h_law
      (r := (0 : ℝ)) (t := -(k : ℝ)) (neg_nonpos.mpr (Nat.cast_nonneg k))
    simpa using h
  have hexp :
      Tendsto (fun k : ℕ ↦ exp (-(k : ℝ))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hconstMu :
      Tendsto (fun _ : ℕ ↦ μ) atTop (nhds μ) := tendsto_const_nhds
  have hconstOneMu :
      Tendsto (fun _ : ℕ ↦ (1 - μ)) atTop (nhds (1 - μ)) := tendsto_const_nhds
  have hlim :
      Tendsto (fun k : ℕ ↦ (μ * exp (-(k : ℝ)) + (1 - μ)) ^ n)
        atTop (nhds ((1 - μ) ^ n)) := by
    simpa using ((hconstMu.mul hexp).add hconstOneMu).pow n
  rw [← bernoulli_entropy_zero_exp hμ1]
  exact ge_of_tendsto' hlim hbound

private lemma ae_eq_const_of_map_eq_dirac
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X : Ω → ℝ} {c : ℝ} (hX : Measurable X)
    (hmap : Measure.map X P = Measure.dirac c) :
    ∀ᵐ ω ∂P, X ω = c := by
  change ∀ᵐ ω ∂P, (fun x : ℝ ↦ x = c) (X ω)
  refine (ae_map_iff (p := fun x : ℝ ↦ x = c) hX.aemeasurable (by measurability)).mp ?_
  rw [hmap]
  simp

private lemma avg_upper_set_eq
    {Ω : Type} {n : ℕ} (hn : 0 < n) {S : Ω → ℝ} {r : ℝ} :
    {ω | r ≤ S ω / n} = {ω | (n : ℝ) * r ≤ S ω} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  rw [le_div_iff₀ (Nat.cast_pos.mpr hn)]
  exact mul_comm r (n : ℝ) ▸ Iff.rfl

private lemma avg_lower_set_eq
    {Ω : Type} {n : ℕ} (hn : 0 < n) {S : Ω → ℝ} {r : ℝ} :
    {ω | S ω / n ≤ r} = {ω | S ω ≤ (n : ℝ) * r} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  rw [div_le_iff₀ (Nat.cast_pos.mpr hn)]
  exact mul_comm r (n : ℝ) ▸ Iff.rfl

private lemma bernoulli_upper_interior
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {μ r : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hrμ : μ < r) (hr1 : r < 1)
    (h_meas : ∀ i, Measurable (X i)) (h_indep : iIndepFun X P)
    (h_law : ∀ i, Measure.map (X i) P =
      ENNReal.ofReal μ • Measure.dirac (1 : ℝ) +
        ENNReal.ofReal (1 - μ) • Measure.dirac (0 : ℝ)) :
    P.real {ω | r ≤ (∑ i, X i ω) / n} ≤
      exp (-((n : ℝ) * bernoulliRelativeEntropy r μ)) := by
  let t := log (r * (1 - μ) / (μ * (1 - r)))
  have hden : 0 < μ * (1 - r) := mul_pos hμ0 (sub_pos.mpr hr1)
  have ht : 0 ≤ t := by
    apply log_nonneg
    rw [le_div_iff₀ hden]
    nlinarith
  rw [avg_upper_set_eq hn]
  calc
    P.real {ω | (n : ℝ) * r ≤ ∑ i, X i ω}
        ≤ exp (-t * ((n : ℝ) * r)) *
            (μ * exp t + (1 - μ)) ^ n :=
      bernoulli_sum_upper_chernoff hμ h_meas h_indep h_law ht
    _ = exp (-((n : ℝ) * bernoulliRelativeEntropy r μ)) :=
      bernoulli_chernoff_factor_eq hμ0 hμ1 (hμ0.trans hrμ) hr1

private lemma bernoulli_lower_interior
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {μ r : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hr0 : 0 < r) (hrμ : r < μ)
    (h_meas : ∀ i, Measurable (X i)) (h_indep : iIndepFun X P)
    (h_law : ∀ i, Measure.map (X i) P =
      ENNReal.ofReal μ • Measure.dirac (1 : ℝ) +
        ENNReal.ofReal (1 - μ) • Measure.dirac (0 : ℝ)) :
    P.real {ω | (∑ i, X i ω) / n ≤ r} ≤
      exp (-((n : ℝ) * bernoulliRelativeEntropy r μ)) := by
  let t := log (r * (1 - μ) / (μ * (1 - r)))
  have hden : 0 < μ * (1 - r) :=
    mul_pos hμ0 (sub_pos.mpr (hrμ.trans hμ1))
  have hratio : 0 ≤ r * (1 - μ) / (μ * (1 - r)) :=
    (div_pos (mul_pos hr0 (sub_pos.mpr hμ1)) hden).le
  have ht : t ≤ 0 := by
    apply log_nonpos hratio
    rw [div_le_iff₀ hden]
    nlinarith
  rw [avg_lower_set_eq hn]
  calc
    P.real {ω | (∑ i, X i ω) ≤ (n : ℝ) * r}
        ≤ exp (-t * ((n : ℝ) * r)) *
            (μ * exp t + (1 - μ)) ^ n :=
      bernoulli_sum_lower_chernoff hμ h_meas h_indep h_law ht
    _ = exp (-((n : ℝ) * bernoulliRelativeEntropy r μ)) :=
      bernoulli_chernoff_factor_eq hμ0 hμ1 hr0 (hrμ.trans hμ1)

private lemma probability_le_entropy_self
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (s : Set Ω) :
    P.real s ≤ exp (-((n : ℝ) * bernoulliRelativeEntropy μ μ)) := by
  rw [bernoulli_entropy_self hμ]
  simpa using (measureReal_le_one (μ := P) (s := s))

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X P)
    (h_law : ∀ i, Measure.map (X i) P =
      ENNReal.ofReal μ • Measure.dirac (1 : ℝ) +
        ENNReal.ofReal (1 - μ) • Measure.dirac (0 : ℝ)) :
    (∀ ε ∈ Set.Icc (0 : ℝ) (1 - μ),
      P.real {ω | μ + ε ≤ (∑ t, X t ω) / n} ≤
        exp (-(n * BanditAlgorithm.bernoulliRelativeEntropy (μ + ε) μ))) ∧
    (∀ ε ∈ Set.Icc (0 : ℝ) μ,
      P.real {ω | (∑ t, X t ω) / n ≤ μ - ε} ≤
        exp (-(n * BanditAlgorithm.bernoulliRelativeEntropy (μ - ε) μ))) := by
  rcases eq_or_ne μ 0 with rfl | hμ0ne
  · have hmap0 (i : Fin n) : Measure.map (X i) P = Measure.dirac (0 : ℝ) := by
      simpa using h_law i
    have hX0 (i : Fin n) : ∀ᵐ ω ∂P, X i ω = 0 :=
      ae_eq_const_of_map_eq_dirac (h_meas i) (hmap0 i)
    have h_all_zero : ∀ᵐ ω ∂P, ∀ i, X i ω = 0 :=
      ae_all_iff.2 hX0
    constructor
    · intro ε hε
      rcases eq_or_ne ε 0 with rfl | hε0
      · simpa using (probability_le_entropy_self (P := P) (n := n) hμ
          {ω | (0 : ℝ) ≤ (∑ t, X t ω) / n})
      have hεpos : 0 < ε := lt_of_le_of_ne hε.1 (Ne.symm hε0)
      have hzero :
          P {ω | 0 + ε ≤ (∑ t, X t ω) / n} = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [h_all_zero] with ω hω
        simp only [not_le]
        have hsum : (∑ t, X t ω) = 0 := by simp [hω]
        rw [hsum]
        norm_num [Nat.ne_of_gt hn, hεpos]
      rw [measureReal_def, hzero]
      exact (exp_pos _).le
    · intro ε hε
      have hεzero : ε = 0 := le_antisymm hε.2 hε.1
      subst ε
      simpa using (probability_le_entropy_self (P := P) (n := n) hμ
        {ω | (∑ t, X t ω) / n ≤ (0 : ℝ)})
  rcases eq_or_ne μ 1 with rfl | hμ1ne
  · have hmap1 (i : Fin n) : Measure.map (X i) P = Measure.dirac (1 : ℝ) := by
      simpa using h_law i
    have hX1 (i : Fin n) : ∀ᵐ ω ∂P, X i ω = 1 :=
      ae_eq_const_of_map_eq_dirac (h_meas i) (hmap1 i)
    have h_all_one : ∀ᵐ ω ∂P, ∀ i, X i ω = 1 :=
      ae_all_iff.2 hX1
    constructor
    · intro ε hε
      have hεzero : ε = 0 := by
        apply le_antisymm
        · simpa using hε.2
        · exact hε.1
      subst ε
      simpa using (probability_le_entropy_self (P := P) (n := n) hμ
        {ω | (1 : ℝ) ≤ (∑ t, X t ω) / n})
    · intro ε hε
      rcases eq_or_ne ε 0 with rfl | hε0
      · simpa using (probability_le_entropy_self (P := P) (n := n) hμ
          {ω | (∑ t, X t ω) / n ≤ (1 : ℝ)})
      have hεpos : 0 < ε := lt_of_le_of_ne hε.1 (Ne.symm hε0)
      have hzero :
          P {ω | (∑ t, X t ω) / n ≤ 1 - ε} = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [h_all_one] with ω hω
        simp only [not_le]
        have hsum : (∑ t, X t ω) = (n : ℝ) := by simp [hω]
        rw [hsum, div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))]
        linarith
      rw [measureReal_def, hzero]
      exact (exp_pos _).le
  have hμ0 : 0 < μ := lt_of_le_of_ne hμ.1 (Ne.symm hμ0ne)
  have hμ1 : μ < 1 := lt_of_le_of_ne hμ.2 hμ1ne
  constructor
  · intro ε hε
    rcases eq_or_ne ε 0 with rfl | hε0
    · simpa using (probability_le_entropy_self (P := P) (n := n) hμ
        {ω | μ ≤ (∑ t, X t ω) / n})
    have hεpos : 0 < ε := lt_of_le_of_ne hε.1 (Ne.symm hε0)
    have hrμ : μ < μ + ε := lt_add_of_pos_right μ hεpos
    have hrle : μ + ε ≤ 1 := by linarith [hε.2]
    rcases eq_or_ne (μ + ε) 1 with hr1 | hr1
    · rw [hr1, avg_upper_set_eq hn]
      simpa using bernoulli_sum_upper_endpoint hμ hμ0 h_meas h_indep h_law
    · exact bernoulli_upper_interior hn hμ hμ0 hμ1 hrμ
        (lt_of_le_of_ne hrle hr1) h_meas h_indep h_law
  · intro ε hε
    rcases eq_or_ne ε 0 with rfl | hε0
    · simpa using (probability_le_entropy_self (P := P) (n := n) hμ
        {ω | (∑ t, X t ω) / n ≤ μ})
    have hεpos : 0 < ε := lt_of_le_of_ne hε.1 (Ne.symm hε0)
    have hrμ : μ - ε < μ := sub_lt_self μ hεpos
    have hrnonneg : 0 ≤ μ - ε := sub_nonneg.mpr hε.2
    rcases eq_or_ne (μ - ε) 0 with hr0 | hr0
    · rw [hr0, avg_lower_set_eq hn]
      simpa using bernoulli_sum_lower_endpoint hμ hμ1 h_meas h_indep h_law
    · exact bernoulli_lower_interior hn hμ hμ0 hμ1
        (lt_of_le_of_ne hrnonneg (Ne.symm hr0)) hrμ h_meas h_indep h_law
