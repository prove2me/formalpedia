-- Prove2me | solution 1 for ExploreFirst.Absolute.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T07:33:07.701719+00:00
-- url     : https://prove2.me/submissions/f2a9cf80-e125-4677-9eb6-c56641ace5f8

import Mathlib
import Definitions.Def_ExploreFirst_Absolute_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace A07Aux

/-- Fenchel-Young inequality for `klFun`: `x s ≤ klFun x + (exp s - 1)` for `x ≥ 0`. -/
lemma mul_le_klFun_add (x s : ℝ) (hx : 0 ≤ x) :
    x * s ≤ klFun x + (Real.exp s - 1) := by
  rw [klFun_apply]
  rcases hx.eq_or_lt with h | h
  · subst h
    simp only [zero_mul]
    linarith [Real.exp_pos s]
  · have hu := Real.add_one_le_exp (s - Real.log x)
    rw [Real.exp_sub, Real.exp_log h] at hu
    have h2 : x * (s - Real.log x + 1) ≤ Real.exp s := by
      have := mul_le_mul_of_nonneg_left hu h.le
      rwa [mul_div_cancel₀ _ h.ne'] at this
    nlinarith [h2]

/-- Variational (Donsker-Varadhan type) lower bound for the KL divergence. -/
lemma integral_le_klDiv_add {Ω : Type*} [MeasurableSpace Ω] (P P' : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] (hKL : klDiv P P' ≠ ∞)
    (g : Ω → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ ω, |g ω| ≤ C) :
    ∫ ω, g ω ∂P ≤ (klDiv P P').toReal + ∫ ω, (Real.exp (g ω) - 1) ∂P' := by
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hKL
  have hgi : Integrable g P := by
    refine Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall ?_)
    intro ω; simpa [Real.norm_eq_abs] using hC ω
  have hexpi : Integrable (fun ω => Real.exp (g ω) - 1) P' := by
    refine Integrable.of_bound ((Real.measurable_exp.comp hg).sub measurable_const).aestronglyMeasurable
      (Real.exp C + 1) (Filter.Eventually.of_forall ?_)
    intro ω
    have h1 : Real.exp (g ω) ≤ Real.exp C := Real.exp_le_exp.2 (le_of_abs_le (hC ω))
    have h2 := Real.exp_pos (g ω)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [Real.exp_pos C]
  have h1 : ∫ ω, g ω ∂P = ∫ ω, (P.rnDeriv P' ω).toReal * g ω ∂P' :=
    (integral_toReal_rnDeriv_mul hac).symm
  have h2 : (klDiv P P').toReal = ∫ ω, klFun (P.rnDeriv P' ω).toReal ∂P' :=
    toReal_klDiv_eq_integral_klFun hac
  have hkli : Integrable (fun ω => klFun (P.rnDeriv P' ω).toReal) P' :=
    (integrable_klFun_rnDeriv_iff hac).mpr hint
  have hmi : Integrable (fun ω => (P.rnDeriv P' ω).toReal * g ω) P' :=
    (integrable_toReal_rnDeriv_mul_iff hac).mpr hgi
  rw [h1, h2, ← integral_add hkli hexpi]
  refine integral_mono hmi (hkli.add hexpi) ?_
  intro ω
  exact mul_le_klFun_add _ _ ENNReal.toReal_nonneg

/-- Second-order upper bound for `exp (-β)`. -/
lemma exp_neg_le_quad (b : ℝ) (hb : 0 ≤ b) : Real.exp (-b) ≤ 1 - b + b ^ 2 / 2 := by
  have h4 := Real.sum_le_exp_of_nonneg hb 4
  simp [Finset.sum_range_succ, Nat.factorial] at h4
  have hpos : 0 < 1 - b + b ^ 2 / 2 := by nlinarith [sq_nonneg (b - 1)]
  rw [Real.exp_neg, ← one_div, div_le_iff₀ (Real.exp_pos b)]
  have key : 1 ≤ (1 - b + b ^ 2 / 2) * (1 + b + b ^ 2 / 2 + b ^ 3 / 6) := by
    nlinarith [pow_nonneg hb 3, pow_nonneg hb 4, pow_nonneg hb 5]
  calc (1 : ℝ) ≤ (1 - b + b ^ 2 / 2) * (1 + b + b ^ 2 / 2 + b ^ 3 / 6) := key
    _ ≤ (1 - b + b ^ 2 / 2) * Real.exp b := by
      apply mul_le_mul_of_nonneg_left _ hpos.le
      linarith

/-- Convexity bound `exp (-β z) ≤ 1 - z (1 - exp (-β))` for `z ∈ [0,1]`. -/
lemma exp_neg_mul_le (b z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.exp (-(b * z)) ≤ 1 - z * (1 - Real.exp (-b)) := by
  have := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-b)) (sub_nonneg.2 hz1) hz0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at this
  calc Real.exp (-(b * z)) = Real.exp (z * -b) := by ring_nf
    _ ≤ 1 - z + z * Real.exp (-b) := this
    _ = 1 - z * (1 - Real.exp (-b)) := by ring

set_option maxHeartbeats 1000000 in
/-- Abstract form of the lower bound: change of measure + refined Pinsker. -/
lemma pulls_lower_bound {Ω : Type*} [MeasurableSpace Ω] (P P' : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] (N : Ω → ℝ) (hN : Measurable N)
    (T : ℝ) (hT : 0 < T) (hN0 : ∀ ω, 0 ≤ N ω) (hNT : ∀ ω, N ω ≤ T) (Kr : ℝ) (hK : 0 < Kr)
    (D : ℝ) (hD0 : 0 ≤ D) (hKL : klDiv P P' ≠ ∞)
    (hKLle : (klDiv P P').toReal ≤ (∫ ω, N ω ∂P) * D) (hq : T / Kr ≤ ∫ ω, N ω ∂P') :
    T / Kr * (1 - Real.sqrt (2 * T * D)) ≤ ∫ ω, N ω ∂P := by
  have hNi : ∀ (μ : Measure Ω) [IsProbabilityMeasure μ], Integrable N μ := by
    intro μ _
    refine Integrable.of_bound hN.aestronglyMeasurable T (Filter.Eventually.of_forall ?_)
    intro ω; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hN0 ω, hNT ω]
  set EP := ∫ ω, N ω ∂P with hEP
  set EQ := ∫ ω, N ω ∂P' with hEQ
  have hEP0 : 0 ≤ EP := integral_nonneg hN0
  have hEQT : EQ ≤ T := by
    calc EQ ≤ ∫ _ω, T ∂P' := integral_mono (hNi P') (integrable_const T) hNT
      _ = T := by simp
  have hTK : 0 ≤ T / Kr := div_nonneg hT.le hK.le
  set s := Real.sqrt (2 * T * D) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 * T * D := Real.sq_sqrt (by positivity)
  by_cases hpq : EQ ≤ EP
  · have : T / Kr * (1 - s) ≤ T / Kr := by nlinarith
    linarith
  push_neg at hpq
  set p := EP / T with hp
  set q := EQ / T with hq_def
  have hpq' : p < q := div_lt_div_of_pos_right hpq hT
  have hp0 : 0 ≤ p := div_nonneg hEP0 hT.le
  have hq0 : 0 < q := lt_of_le_of_lt hp0 hpq'
  have hq1 : q ≤ 1 := by rw [hq_def, div_le_one hT]; exact hEQT
  set b := (q - p) / q with hb
  have hb0 : 0 ≤ b := div_nonneg (by linarith) hq0.le
  set c := 1 - Real.exp (-b) with hc
  have hc0 : 0 ≤ c := by
    have : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  have hc1 : c ≤ 1 := by have := Real.exp_pos (-b); linarith
  have hcq : b - b ^ 2 / 2 ≤ c := by have := exp_neg_le_quad b hb0; linarith
  set g : Ω → ℝ := fun ω => q * c - b * (N ω / T) with hg
  have hgm : Measurable g := measurable_const.sub (measurable_const.mul (hN.div_const T))
  have hZ0 : ∀ ω, 0 ≤ N ω / T := fun ω => div_nonneg (hN0 ω) hT.le
  have hZ1 : ∀ ω, N ω / T ≤ 1 := fun ω => (div_le_one hT).2 (hNT ω)
  have hgb : ∀ ω, |g ω| ≤ q * c + b := by
    intro ω
    have h0 := hZ0 ω
    have h1 := hZ1 ω
    have hqc : 0 ≤ q * c := mul_nonneg hq0.le hc0
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hb0 h0, mul_le_mul_of_nonneg_left h1 hb0]
  have hV := integral_le_klDiv_add P P' hKL g hgm (q * c + b) hgb
  have hgP : ∫ ω, g ω ∂P = q * c - b * p := by
    simp only [hg]
    rw [integral_sub (integrable_const _) (((hNi P).div_const T).const_mul b), integral_const,
      integral_const_mul, integral_div]
    simp [hp]
    try (left; rfl)
  have hexp : ∫ ω, (Real.exp (g ω) - 1) ∂P' ≤ 0 := by
    have hpt : ∀ ω, Real.exp (g ω) - 1 ≤ Real.exp (q * c) * (1 - c * (N ω / T)) - 1 := by
      intro ω
      have h := exp_neg_mul_le b (N ω / T) (hZ0 ω) (hZ1 ω)
      have : Real.exp (g ω) = Real.exp (q * c) * Real.exp (-(b * (N ω / T))) := by
        rw [← Real.exp_add]; simp only [hg]; ring_nf
      rw [this]
      have hpos := Real.exp_pos (q * c)
      have : Real.exp (q * c) * Real.exp (-(b * (N ω / T))) ≤
          Real.exp (q * c) * (1 - c * (N ω / T)) := by
        apply mul_le_mul_of_nonneg_left _ hpos.le
        have e : 1 - c * (N ω / T) = 1 - N ω / T * (1 - Real.exp (-b)) := by rw [hc]; ring
        rw [e]; exact h
      linarith
    have hint1 : Integrable (fun ω => Real.exp (g ω) - 1) P' := by
      refine Integrable.of_bound ((Real.measurable_exp.comp hgm).sub measurable_const).aestronglyMeasurable
        (Real.exp (q * c + b) + 1) (Filter.Eventually.of_forall ?_)
      intro ω
      have h1 : Real.exp (g ω) ≤ Real.exp (q * c + b) :=
        Real.exp_le_exp.2 (le_of_abs_le (hgb ω))
      have h2 := Real.exp_pos (g ω)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [Real.exp_pos (q * c + b)]
    have hint2 : Integrable (fun ω => Real.exp (q * c) * (1 - c * (N ω / T)) - 1) P' :=
      (((integrable_const 1).sub (((hNi P').div_const T).const_mul c)).const_mul _).sub
        (integrable_const 1)
    calc ∫ ω, (Real.exp (g ω) - 1) ∂P'
        ≤ ∫ ω, (Real.exp (q * c) * (1 - c * (N ω / T)) - 1) ∂P' := integral_mono hint1 hint2 hpt
      _ = Real.exp (q * c) * (1 - c * q) - 1 := by
          rw [integral_sub _ (integrable_const 1), integral_const_mul,
            integral_sub (integrable_const 1) (((hNi P').div_const T).const_mul c),
            integral_const_mul, integral_div]
          · simp [hq_def]
            try (left; rfl)
          · exact ((integrable_const 1).sub (((hNi P').div_const T).const_mul c)).const_mul _
      _ ≤ 0 := by
          have := Real.add_one_le_exp (-(q * c))
          have h3 : Real.exp (q * c) * Real.exp (-(q * c)) = 1 := by
            rw [← Real.exp_add]; simp
          have hqc1 : 0 ≤ 1 - c * q := by nlinarith
          nlinarith [Real.exp_pos (q * c)]
  -- main chain
  have hmain : q * c - b * p ≤ (T * p) * D := by
    have hEPeq : EP = T * p := by rw [hp]; field_simp
    have := hV
    rw [hgP] at this
    calc q * c - b * p ≤ (klDiv P P').toReal + 0 := by linarith
      _ ≤ EP * D := by linarith
      _ = T * p * D := by rw [hEPeq]
  have hquad : (q - p) ^ 2 ≤ 2 * q * (T * p * D) := by
    have h1 : q * (b - b ^ 2 / 2) - b * p ≤ T * p * D := by
      have := mul_le_mul_of_nonneg_left hcq hq0.le
      linarith
    have hbq : b * q = q - p := by rw [hb]; field_simp
    have : (q - p) ^ 2 / (2 * q) ≤ T * p * D := by
      have e : q * (b - b ^ 2 / 2) - b * p = (q - p) ^ 2 / (2 * q) := by
        rw [hb]; field_simp; ring
      linarith
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have hquad2 : (q - p) ^ 2 ≤ q ^ 2 * s ^ 2 := by
    rw [hs2]
    have hTD : 0 ≤ T * D := mul_nonneg hT.le hD0
    nlinarith [mul_le_mul_of_nonneg_left hpq'.le (mul_nonneg (mul_nonneg hq0.le hT.le) hD0)]
  have hKq : 1 / Kr ≤ q := by
    have e : T / Kr / T = 1 / Kr := by field_simp
    rw [← e, hq_def]; exact div_le_div_of_nonneg_right hq hT.le
  by_cases hs1 : 1 ≤ s
  · have : T / Kr * (1 - s) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hTK (by linarith)
    linarith
  push_neg at hs1
  have hqs : q - p ≤ q * s := by
    by_contra hcon
    push_neg at hcon
    have h0 : 0 ≤ q * s := mul_nonneg hq0.le hs0
    nlinarith [mul_self_lt_mul_self h0 hcon]
  have hp2 : 1 / Kr * (1 - s) ≤ p := by
    calc 1 / Kr * (1 - s) ≤ q * (1 - s) :=
          mul_le_mul_of_nonneg_right hKq (by linarith : (0 : ℝ) ≤ 1 - s)
      _ = q - q * s := by ring
      _ ≤ p := by linarith
  have hEPeq : EP = T * p := by rw [hp]; field_simp
  rw [hEPeq]
  calc T / Kr * (1 - s) = T * (1 / Kr * (1 - s)) := by ring
    _ ≤ T * p := mul_le_mul_of_nonneg_left hp2 hT.le

section StepKL

variable {β : Type*} [MeasurableSpace β] {K : ℕ}

/-- KL divergence of one bandit round where only arm `a` changes its law. -/
lemma klDiv_compProd_comap_eq (ρ : Measure β) [IsProbabilityMeasure ρ] (g : β → Fin K)
    (hg : Measurable g) (P P' : Fin K → Measure ℝ) [hP : ∀ i, IsProbabilityMeasure (P i)]
    [hP' : ∀ i, IsProbabilityMeasure (P' i)]
    (a : Fin K) (hPP : ∀ i, i ≠ a → P i = P' i) (hD : klDiv (P a) (P' a) ≠ ∞) :
    haveI : IsMarkovKernel (Kernel.ofFunOfCountable P) := ⟨fun i => hP i⟩
    haveI : IsMarkovKernel (Kernel.ofFunOfCountable P') := ⟨fun i => hP' i⟩
    klDiv (ρ ⊗ₘ ((Kernel.ofFunOfCountable P).comap g hg))
      (ρ ⊗ₘ ((Kernel.ofFunOfCountable P').comap g hg)) = ρ (g ⁻¹' {a}) * klDiv (P a) (P' a) := by
  haveI : IsMarkovKernel (Kernel.ofFunOfCountable P) := ⟨fun i => hP i⟩
  haveI : IsMarkovKernel (Kernel.ofFunOfCountable P') := ⟨fun i => hP' i⟩
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hD
  set f : ℝ → ℝ≥0∞ := (P a).rnDeriv (P' a) with hf_def
  have hfm : Measurable f := Measure.measurable_rnDeriv _ _
  set F : β → ℝ → ℝ≥0∞ := fun x y => if g x = a then f y else 1 with hF_def
  have hsa : MeasurableSet {p : β × ℝ | g p.1 = a} :=
    (hg.comp measurable_fst) (measurableSet_singleton a)
  have hFm : Measurable (Function.uncurry F) := by
    show Measurable (fun p : β × ℝ => if g p.1 = a then f p.2 else 1)
    exact Measurable.ite hsa (hfm.comp measurable_snd) measurable_const
  have hker : (Kernel.ofFunOfCountable P).comap g hg =
      ((Kernel.ofFunOfCountable P').comap g hg).withDensity F := by
    ext x : 1
    rw [Kernel.withDensity_apply _ hFm, Kernel.comap_apply, Kernel.comap_apply]
    show P (g x) = (P' (g x)).withDensity (F x)
    by_cases hx : g x = a
    · have hFx : F x = f := by funext y; simp [hF_def, hx]
      rw [hFx, hx]
      exact (Measure.withDensity_rnDeriv_eq _ _ hac).symm
    · have hFx : F x = fun _ => 1 := by funext y; simp [hF_def, hx]
      rw [hFx, show (fun _ : ℝ => (1 : ℝ≥0∞)) = 1 from rfl, withDensity_one, hPP _ hx]
  set G : β × ℝ → ℝ≥0∞ := fun p => F p.1 p.2 with hG
  have hGm : Measurable G := hFm
  set Y := ρ ⊗ₘ ((Kernel.ofFunOfCountable P').comap g hg) with hY
  set X := ρ ⊗ₘ ((Kernel.ofFunOfCountable P).comap g hg) with hXdef
  haveI : IsSFiniteKernel (((Kernel.ofFunOfCountable P').comap g hg).withDensity F) := by
    rw [← hker]; infer_instance
  have hX : X = Y.withDensity G := by
    rw [hXdef, hker, Measure.compProd_withDensity hFm]
  have hXY : X ≪ Y := by rw [hX]; exact withDensity_absolutelyContinuous _ _
  have hll : llr X Y =ᵐ[X] fun p => Real.log (G p).toReal := by
    have h1 : X.rnDeriv Y =ᵐ[Y] G := by rw [hX]; exact Measure.rnDeriv_withDensity Y hGm
    filter_upwards [hXY.ae_le h1] with p hp
    simp only [llr, hp]
  set I : ℝ := ∫ y, llr (P a) (P' a) y ∂(P a) with hI
  have hLm : Measurable (fun p : β × ℝ => Real.log (G p).toReal) :=
    Real.measurable_log.comp hGm.ennreal_toReal
  have hinner : ∀ x, ∫ y, Real.log (G (x, y)).toReal ∂(((Kernel.ofFunOfCountable P).comap g hg) x)
      = if g x = a then I else 0 := by
    intro x
    rw [Kernel.comap_apply]
    show ∫ y, Real.log (G (x, y)).toReal ∂(P (g x)) = _
    by_cases hx : g x = a
    · simp only [hG, hF_def, hx, if_true]
      rfl
    · simp [hG, hF_def, hx]
  have hint_inner : ∀ x, Integrable (fun y => Real.log (G (x, y)).toReal)
      (((Kernel.ofFunOfCountable P).comap g hg) x) := by
    intro x
    rw [Kernel.comap_apply]
    show Integrable (fun y => Real.log (G (x, y)).toReal) (P (g x))
    by_cases hx : g x = a
    · simp only [hG, hF_def, hx, if_true]
      exact hint
    · simp [hG, hF_def, hx]
  have hnorm : ∀ x, ∫ y, ‖Real.log (G (x, y)).toReal‖ ∂(((Kernel.ofFunOfCountable P).comap g hg) x)
      = (g ⁻¹' {a}).indicator (fun _ => ∫ y, ‖llr (P a) (P' a) y‖ ∂(P a)) x := by
    intro x
    rw [Kernel.comap_apply]
    show ∫ y, ‖Real.log (G (x, y)).toReal‖ ∂(P (g x)) = _
    by_cases hx : g x = a
    · simp only [hG, hF_def, hx, if_true, Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
      rfl
    · simp [hG, hF_def, hx, Set.indicator]
  have hLint : Integrable (fun p => Real.log (G p).toReal) X := by
    rw [hXdef, Measure.integrable_compProd_iff hLm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall hint_inner, ?_⟩
    simp_rw [hnorm]
    exact (integrable_const _).indicator (hg (measurableSet_singleton a))
  have hllint : Integrable (llr X Y) X := hLint.congr (hll.symm)
  have hIX : ∫ p, llr X Y p ∂X = (ρ (g ⁻¹' {a})).toReal * I := by
    rw [integral_congr_ae hll, hXdef, Measure.integral_compProd hLint]
    simp_rw [hinner]
    have : (fun x => if g x = a then I else 0) = (g ⁻¹' {a}).indicator (fun _ => I) := by
      funext x; by_cases hx : g x = a <;> simp [Set.indicator, hx]
    rw [this, integral_indicator_const _ (hg (measurableSet_singleton a))]
    simp [Measure.real, smul_eq_mul]
  rw [klDiv_of_ac_of_integrable hXY hllint, klDiv_of_ac_of_integrable hac hint, hIX]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end StepKL

section Bandit

open BanditAlgorithm

variable {K : ℕ}

lemma armPullCount_eq_sum {n : ℕ} (a : Fin K) (h : BanditHistory K n) :
    armPullCount a h = ∑ t, if (h t).1 = a then 1 else 0 := by
  unfold armPullCount
  rw [Set.toFinset_setOf, Finset.card_filter]

lemma measurable_armPullCount {n : ℕ} (a : Fin K) :
    Measurable (fun h : BanditHistory K n => armPullCount a h) := by
  have e : (fun h : BanditHistory K n => armPullCount a h) =
      fun h => ∑ t, if (h t).1 = a then 1 else 0 := funext (armPullCount_eq_sum a)
  rw [e]
  refine Finset.measurable_sum _ (fun t _ => ?_)
  exact Measurable.ite ((measurable_fst.comp (measurable_pi_apply t)) (measurableSet_singleton a))
    measurable_const measurable_const

lemma armPullCount_le {n : ℕ} (a : Fin K) (h : BanditHistory K n) : armPullCount a h ≤ n := by
  rw [armPullCount_eq_sum]
  calc ∑ t : Fin n, (if (h t).1 = a then 1 else 0) ≤ ∑ _t : Fin n, 1 :=
        Finset.sum_le_sum (fun t _ => by split_ifs <;> norm_num)
    _ = n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

lemma armPullCount_snoc {n : ℕ} (a : Fin K) (h : BanditHistory K n) (x : Fin K × ℝ) :
    armPullCount a (Fin.snoc (α := fun _ => Fin K × ℝ) h x) =
      armPullCount a h + if x.1 = a then 1 else 0 := by
  rw [armPullCount_eq_sum, armPullCount_eq_sum, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

lemma lintegral_pulls_succ (ν : StochasticBandit K) (π : BanditPolicy K) (a : Fin K) (n : ℕ) :
    ∫⁻ h, (armPullCount a h : ℝ≥0∞) ∂(banditMeasure ν π (n + 1)) =
      ∫⁻ h, (armPullCount a h : ℝ≥0∞) ∂(banditMeasure ν π n) +
        ∫⁻ h, π.select n h {a} ∂(banditMeasure ν π n) := by
  have hm := measurable_armPullCount (K := K) (n := n) a
  have hmE : Measurable (fun h : BanditHistory K (n + 1) => (armPullCount a h : ℝ≥0∞)) :=
    measurable_from_nat.comp (measurable_armPullCount a)
  rw [banditMeasure, lintegral_map hmE measurable_banditHistorySnoc]
  simp_rw [armPullCount_snoc]
  push_cast
  have hm1 : Measurable (fun p : BanditHistory K n × (Fin K × ℝ) => (armPullCount a p.1 : ℝ≥0∞)) :=
    measurable_from_nat.comp (hm.comp measurable_fst)
  have hset : MeasurableSet {y : Fin K × ℝ | y.1 = a} := measurable_fst (measurableSet_singleton a)
  rw [lintegral_add_left hm1]
  congr 1
  · rw [Measure.lintegral_compProd hm1]
    simp
  · have hm2 : Measurable (fun p : BanditHistory K n × (Fin K × ℝ) =>
        (if p.2.1 = a then (1 : ℝ≥0∞) else 0)) :=
      Measurable.ite ((measurable_fst.comp measurable_snd) (measurableSet_singleton a))
        measurable_const measurable_const
    rw [Measure.lintegral_compProd hm2]
    congr 1
    funext h
    have e : (fun y : Fin K × ℝ => if y.1 = a then (1 : ℝ≥0∞) else 0) =
        Set.indicator {y : Fin K × ℝ | y.1 = a} 1 := by
      funext y; by_cases hy : y.1 = a <;> simp [Set.indicator, hy]
    simp only
    rw [e, lintegral_indicator_one hset]
    have := Kernel.fst_apply' (banditStepKernel ν π n) h (measurableSet_singleton a)
    rw [banditStepKernel, Kernel.fst_compProd] at this
    rw [banditStepKernel]
    exact this.symm

/-- Divergence decomposition for bandit measures differing only in arm `a`. -/
lemma klDiv_banditMeasure_le (ν ν' : StochasticBandit K) (π : BanditPolicy K) (a : Fin K)
    (hPP : ∀ i, i ≠ a → ν.P i = ν'.P i) (hD : klDiv (ν.P a) (ν'.P a) ≠ ∞) (n : ℕ) :
    klDiv (banditMeasure ν π n) (banditMeasure ν' π n) ≤
      (∫⁻ h, (armPullCount a h : ℝ≥0∞) ∂(banditMeasure ν π n)) * klDiv (ν.P a) (ν'.P a) := by
  induction n with
  | zero => simp [banditMeasure, klDiv_self]
  | succ n ih =>
    set Pn := banditMeasure ν π n with hPn
    have hS : klDiv (Pn ⊗ₘ banditStepKernel ν π n) (Pn ⊗ₘ banditStepKernel ν' π n) ≤
        (∫⁻ h, π.select n h {a} ∂Pn) * klDiv (ν.P a) (ν'.P a) := by
      simp only [banditStepKernel]
      rw [← Measure.compProd_assoc', ← Measure.compProd_assoc']
      refine (klDiv_map_le _ _ (MeasurableEquiv.measurable _)).trans (le_of_eq ?_)
      have := klDiv_compProd_comap_eq (Pn ⊗ₘ π.select n) Prod.snd measurable_snd ν.P ν'.P a hPP hD
      refine this.trans ?_
      rw [Measure.compProd_apply (measurable_snd (measurableSet_singleton a))]
      rfl
    calc klDiv (banditMeasure ν π (n + 1)) (banditMeasure ν' π (n + 1))
        ≤ klDiv (Pn ⊗ₘ banditStepKernel ν π n) (banditMeasure ν' π n ⊗ₘ banditStepKernel ν' π n) := by
          rw [banditMeasure, banditMeasure]
          exact klDiv_map_le _ _ measurable_banditHistorySnoc
      _ = klDiv Pn (banditMeasure ν' π n) +
            klDiv (Pn ⊗ₘ banditStepKernel ν π n) (Pn ⊗ₘ banditStepKernel ν' π n) :=
          klDiv_compProd_eq_add _ _ _ _
      _ ≤ (∫⁻ h, (armPullCount a h : ℝ≥0∞) ∂Pn) * klDiv (ν.P a) (ν'.P a) +
            (∫⁻ h, π.select n h {a} ∂Pn) * klDiv (ν.P a) (ν'.P a) := add_le_add ih hS
      _ = (∫⁻ h, (armPullCount a h : ℝ≥0∞) ∂(banditMeasure ν π (n + 1))) *
            klDiv (ν.P a) (ν'.P a) := by
          rw [lintegral_pulls_succ, add_mul]

end Bandit

end A07Aux

/-- Garivier–Ménard–Stoltz, Theorem 2, p. 10, with the necessary model-membership and finite-divergence conditions. -/
theorem solution {K : ℕ} (𝒟 : Set (MeasureTheory.Measure ℝ))
    (hmodel : ExploreFirst.Asymptotic.IsModel 𝒟) (π : BanditAlgorithm.BanditPolicy K)
    (hπ : ExploreFirst.Absolute.IsSmarterThanUniform 𝒟 π)
    (ν : BanditAlgorithm.StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a : Fin K)
    (hfinite : BanditAlgorithm.banditDInf 𝒟 (ν.P a) (BanditAlgorithm.banditOptimalMean ν) ≠ ⊤)
    (T : ℕ) (hT : 1 ≤ T) :
    (T : ℝ) / K * (1 - Real.sqrt (2 * T *
      (BanditAlgorithm.banditDInf 𝒟 (ν.P a) (BanditAlgorithm.banditOptimalMean ν)).toReal)) ≤
      ExploreFirst.FundIneq.expPulls ν π T a := by
  have hKpos : 0 < K := a.pos
  have perQ : ∀ Q ∈ 𝒟, BanditAlgorithm.banditOptimalMean ν < ∫ x, x ∂Q →
      klDiv (ν.P a) Q ≠ ⊤ →
      (T : ℝ) / K * (1 - Real.sqrt (2 * T * (klDiv (ν.P a) Q).toReal)) ≤
        ExploreFirst.FundIneq.expPulls ν π T a := by
    intro Q hQ hmean hKLQ
    haveI hQp : IsProbabilityMeasure Q := (hmodel Q hQ).1
    let ν' : BanditAlgorithm.StochasticBandit K :=
      ⟨Function.update ν.P a Q, fun i => by
        rcases eq_or_ne i a with rfl | h
        · rw [Function.update_self]; exact hQp
        · rw [Function.update_of_ne h]; exact ν.prob i⟩
    have hν'a : ν'.P a = Q := Function.update_self _ _ _
    have hν'i : ∀ i, i ≠ a → ν.P i = ν'.P i := fun i h => (Function.update_of_ne h _ _).symm
    have hin : ExploreFirst.Asymptotic.InModel 𝒟 ν' := by
      intro i
      rcases eq_or_ne i a with rfl | h
      · rw [hν'a]; exact hQ
      · rw [← hν'i i h]; exact hν i
    have hopt : a ∈ ExploreFirst.Asymptotic.optimalArms ν' := by
      simp only [ExploreFirst.Asymptotic.optimalArms, Finset.mem_filter, Finset.mem_univ, true_and]
      have h3 : BanditAlgorithm.banditArmMean ν' a = ∫ x, x ∂Q := by
        simp only [BanditAlgorithm.banditArmMean, hν'a]
      have hmeanle : ∀ i, BanditAlgorithm.banditArmMean ν' i ≤
          BanditAlgorithm.banditArmMean ν' a := by
        intro i
        rcases eq_or_ne i a with rfl | h
        · exact le_rfl
        · have h1 : BanditAlgorithm.banditArmMean ν' i = BanditAlgorithm.banditArmMean ν i := by
            simp only [BanditAlgorithm.banditArmMean, ← hν'i i h]
          have h2 : BanditAlgorithm.banditArmMean ν i ≤ BanditAlgorithm.banditOptimalMean ν := by
            show _ ≤ ⨆ j, BanditAlgorithm.banditArmMean ν j
            exact le_ciSup (Finite.bddAbove_range _) i
          linarith
      haveI : Nonempty (Fin K) := ⟨a⟩
      show _ = ⨆ j, BanditAlgorithm.banditArmMean ν' j
      exact le_antisymm (le_ciSup (Finite.bddAbove_range _) a) (ciSup_le hmeanle)
    have hq := hπ ν' hin a hopt T hT
    have hDfin : klDiv (ν.P a) (ν'.P a) ≠ ⊤ := by rw [hν'a]; exact hKLQ
    have hKLb := A07Aux.klDiv_banditMeasure_le ν ν' π a hν'i hDfin T
    have hmR : Measurable (fun h : BanditAlgorithm.BanditHistory K T =>
        (BanditAlgorithm.armPullCount a h : ℝ)) :=
      measurable_from_nat.comp (A07Aux.measurable_armPullCount a)
    have hlin_le : ∫⁻ h, (BanditAlgorithm.armPullCount a h : ℝ≥0∞)
        ∂(BanditAlgorithm.banditMeasure ν π T) ≤ T := by
      calc ∫⁻ h, (BanditAlgorithm.armPullCount a h : ℝ≥0∞) ∂(BanditAlgorithm.banditMeasure ν π T)
          ≤ ∫⁻ _h, (T : ℝ≥0∞) ∂(BanditAlgorithm.banditMeasure ν π T) :=
            lintegral_mono (fun h => Nat.cast_le.mpr (A07Aux.armPullCount_le a h))
        _ = T := by simp
    have hlin_ne : ∫⁻ h, (BanditAlgorithm.armPullCount a h : ℝ≥0∞)
        ∂(BanditAlgorithm.banditMeasure ν π T) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top T) hlin_le
    have hint_eq : ∫ h, (BanditAlgorithm.armPullCount a h : ℝ) ∂(BanditAlgorithm.banditMeasure ν π T) =
        (∫⁻ h, (BanditAlgorithm.armPullCount a h : ℝ≥0∞)
          ∂(BanditAlgorithm.banditMeasure ν π T)).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun h => Nat.cast_nonneg _))
        hmR.aestronglyMeasurable]
      simp [ENNReal.ofReal_natCast]
    have hKLne : klDiv (BanditAlgorithm.banditMeasure ν π T) (BanditAlgorithm.banditMeasure ν' π T)
        ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top hlin_ne hDfin) hKLb
    have hKLle : (klDiv (BanditAlgorithm.banditMeasure ν π T)
        (BanditAlgorithm.banditMeasure ν' π T)).toReal ≤
        (∫ h, (BanditAlgorithm.armPullCount a h : ℝ) ∂(BanditAlgorithm.banditMeasure ν π T)) *
          (klDiv (ν.P a) Q).toReal := by
      rw [hint_eq, ← hν'a, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top hlin_ne hDfin) hKLb
    exact A07Aux.pulls_lower_bound (BanditAlgorithm.banditMeasure ν π T)
      (BanditAlgorithm.banditMeasure ν' π T) (fun h => (BanditAlgorithm.armPullCount a h : ℝ)) hmR
      T (Nat.cast_pos.mpr hT) (fun h => Nat.cast_nonneg _)
      (fun h => by exact_mod_cast A07Aux.armPullCount_le a h) K (Nat.cast_pos.mpr hKpos) _
      ENNReal.toReal_nonneg hKLne hKLle hq
  -- infimum over the alternatives
  set Kinf := BanditAlgorithm.banditDInf 𝒟 (ν.P a) (BanditAlgorithm.banditOptimalMean ν) with hKinf
  by_contra hlt
  push Not at hlt
  have hcont : Continuous (fun x : ℝ => (T : ℝ) / K * (1 - Real.sqrt (2 * T * x))) :=
    continuous_const.mul (continuous_const.sub
      (Real.continuous_sqrt.comp (continuous_const.mul continuous_id)))
  have hev := hcont.continuousAt.eventually_const_lt hlt
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hlt2 : Kinf < ENNReal.ofReal (Kinf.toReal + δ) := by
    rw [ENNReal.lt_ofReal_iff_toReal_lt hfinite]; linarith
  have hlt3 := hlt2
  rw [hKinf, BanditAlgorithm.banditDInf] at hlt3
  simp only [iInf_lt_iff] at hlt3
  obtain ⟨Q, hQS, hQlt⟩ := hlt3
  have hle : Kinf ≤ klDiv (ν.P a) Q := by
    rw [hKinf, BanditAlgorithm.banditDInf]
    exact iInf₂_le Q hQS
  obtain ⟨hQ𝒟, hQmean⟩ := hQS
  have hQne : klDiv (ν.P a) Q ≠ ⊤ := ne_top_of_lt hQlt
  have h1 : Kinf.toReal ≤ (klDiv (ν.P a) Q).toReal := ENNReal.toReal_mono hQne hle
  have h2 : (klDiv (ν.P a) Q).toReal < Kinf.toReal + δ := ENNReal.toReal_lt_of_lt_ofReal hQlt
  have h3 : ExploreFirst.FundIneq.expPulls ν π T a <
      (T : ℝ) / K * (1 - Real.sqrt (2 * T * (klDiv (ν.P a) Q).toReal)) :=
    hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  have h4 := perQ Q hQ𝒟 hQmean hQne
  linarith
