-- Prove2me | solution 2 for EthierKurtz.kmt_affine_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T06:24:37.15423+00:00
-- url     : https://prove2.me/submissions/fae3eec9-17fc-4c05-b335-b2c1d7ccab5a

import Mathlib
import Definitions.Def_EthierKurtz_kmtApproximation

open MeasureTheory ProbabilityTheory in
private lemma p2m37e3_exists_dirac
    (mu : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real)))
    (hvar : variance (fun x : Real => x) (mu : Measure Real) = 0) :
    Exists fun m : Real => Measure.map (fun _ : Real => m) (mu : Measure Real) = (mu : Measure Real) := by
  obtain ⟨a0, ha0, hint⟩ := hexp
  have hpos : Integrable (fun x : Real => Real.exp (a0 * x)) (mu : Measure Real) :=
    hint a0 (by rw [abs_of_pos ha0])
  have hneg : Integrable (fun x : Real => Real.exp (-a0 * x)) (mu : Measure Real) :=
    hint (-a0) (by rw [abs_neg, abs_of_pos ha0])
  have hsq : Integrable (fun x : Real => x ^ 2) (mu : Measure Real) :=
    integrable_pow_of_integrable_exp_mul (X := fun x : Real => x) ha0.ne' hpos hneg 2
  have hLp : MemLp (fun x : Real => x) 2 (mu : Measure Real) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hsq
  have hlt : evariance (fun x : Real => x) (mu : Measure Real) < ⊤ :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).2 hLp
  have hev : evariance (fun x : Real => x) (mu : Measure Real) = 0 := by
    have h0 : (evariance (fun x : Real => x) (mu : Measure Real)).toReal = 0 := hvar
    rcases ENNReal.toReal_eq_zero_iff _ |>.1 h0 with h | h
    · exact h
    · exact absurd h hlt.ne
  have hae := (evariance_eq_zero_iff (X := fun x : Real => x) measurable_id.aemeasurable).1 hev
  refine ⟨MeasureTheory.integral (mu : Measure Real) (fun x : Real => x), ?_⟩
  exact (Measure.map_congr hae.symm).trans Measure.map_id'

open MeasureTheory ProbabilityTheory in
private lemma d4d73198_zero_case
    (mu : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real)))
    (hvar : variance (fun x : Real => x) (mu : Measure Real) = 0) :
    Exists fun (nu : ProbabilityMeasure Real) => Exists fun m : Real => Exists fun sigma : Real =>
      And (0 <= sigma) (And (Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
      (And (MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
      (And (variance (fun y : Real => y) (nu : Measure Real) = 1)
      (Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
        Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)))))) := by
  obtain ⟨m, hm⟩ := p2m37e3_exists_dirac mu hexp hvar
  refine ⟨⟨gaussianReal 0 1, inferInstance⟩, m, 0, le_refl 0, ?_, ?_, ?_, 1, one_pos, fun a _ => ?_⟩
  · have h1 : Measure.map (fun y : Real => m + 0 * y) (gaussianReal 0 1)
        = Measure.map (fun _ : Real => m) (gaussianReal 0 1) := by
      congr 1
      funext y
      simp
    change Measure.map (fun y : Real => m + 0 * y) (gaussianReal 0 1) = (mu : Measure Real)
    rw [h1, Measure.map_const, ← hm, Measure.map_const]
    simp
  · exact integral_id_gaussianReal
  · simp
  · exact integrable_exp_mul_gaussianReal a

open MeasureTheory ProbabilityTheory in
private lemma d15a1b08_standardize
    (mu : ProbabilityMeasure Real)
    (hvar : 0 < variance (fun x : Real => x) (mu : Measure Real)) :
    Exists fun (nu : ProbabilityMeasure Real) => Exists fun m : Real => Exists fun sigma : Real =>
      And (0 < sigma) (And (Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
      (And (MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
      (variance (fun y : Real => y) (nu : Measure Real) = 1))) := by
  set V : Real := variance (fun x : Real => x) (mu : Measure Real) with hV
  set m : Real := MeasureTheory.integral (mu : Measure Real) (fun y : Real => y) with hm
  set s : Real := Real.sqrt V with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hvar
  have hsne : s ≠ 0 := hspos.ne'
  have hs2 : s ^ 2 = V := Real.sq_sqrt hvar.le
  have hLp : MemLp (fun y : Real => y) 2 (mu : Measure Real) :=
    memLp_two_of_variance_ne_zero measurable_id.aestronglyMeasurable hvar.ne'
  have hint : Integrable (fun y : Real => y) (mu : Measure Real) :=
    hLp.integrable one_le_two
  let f : Real → Real := fun x => s⁻¹ * (x - m)
  have hf : Measurable f := by fun_prop
  let nu : ProbabilityMeasure Real := mu.map hf.aemeasurable
  have hnu : (nu : Measure Real) = Measure.map f (mu : Measure Real) :=
    ProbabilityMeasure.toMeasure_map mu hf.aemeasurable
  have hg : Measurable (fun y : Real => m + s * y) := by fun_prop
  refine ⟨nu, m, s, hspos, ?_, ?_, ?_⟩
  · rw [hnu, Measure.map_map hg hf]
    have : ((fun y : Real => m + s * y) ∘ f) = id := by
      funext x
      simp only [Function.comp, f, id]
      field_simp
      ring
    rw [this, Measure.map_id]
  · rw [hnu, integral_map hf.aemeasurable (by fun_prop)]
    simp only [f]
    rw [integral_const_mul, integral_sub hint (integrable_const m), integral_const]
    simp [hm]
  · rw [hnu]
    have h1 := variance_id_map (μ := (mu : Measure Real)) hf.aemeasurable
    have h2 := variance_const_mul s⁻¹ (fun x : Real => x - m) (mu : Measure Real)
    have h3 := variance_sub_const (μ := (mu : Measure Real))
      (X := fun x : Real => x) measurable_id.aestronglyMeasurable m
    calc variance (fun y : Real => y) (Measure.map f (mu : Measure Real))
        = variance f (mu : Measure Real) := h1
      _ = s⁻¹ ^ 2 * variance (fun x : Real => x - m) (mu : Measure Real) := h2
      _ = s⁻¹ ^ 2 * V := by rw [h3]
      _ = 1 := by rw [← hs2]; field_simp

open MeasureTheory ProbabilityTheory in
private lemma d15a1b08_exp_transport
    (mu nu : ProbabilityMeasure Real) (m sigma : Real)
    (hsigma : 0 < sigma)
    (hmap : Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real))) :
    Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)) := by
  obtain ⟨a0, ha0, hint⟩ := hexp
  refine ⟨a0 * sigma, mul_pos ha0 hsigma, fun b hb => ?_⟩
  have hmeas : Measurable (fun y : Real => m + sigma * y) := by fun_prop
  have hab : |b / sigma| ≤ a0 := by
    rw [abs_div, abs_of_pos hsigma, div_le_iff₀ hsigma]
    exact hb
  have h1 := hint (b / sigma) hab
  rw [← hmap, integrable_map_measure (by fun_prop) hmeas.aemeasurable] at h1
  have h2 := h1.const_mul (Real.exp (-(b / sigma * m)))
  refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply]
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

open MeasureTheory ProbabilityTheory in
private lemma d4d73198_pos_case
    (mu : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real)))
    (hvar : 0 < variance (fun x : Real => x) (mu : Measure Real)) :
    Exists fun (nu : ProbabilityMeasure Real) => Exists fun m : Real => Exists fun sigma : Real =>
      And (0 <= sigma) (And (Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
      (And (MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
      (And (variance (fun y : Real => y) (nu : Measure Real) = 1)
      (Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
        Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)))))) := by
  obtain ⟨nu, m, sigma, hsigma, hmap, hmean, hv⟩ := d15a1b08_standardize mu hvar
  exact ⟨nu, m, sigma, hsigma.le, hmap, hmean, hv,
    d15a1b08_exp_transport mu nu m sigma hsigma hmap hexp⟩

open MeasureTheory ProbabilityTheory in
private lemma d2269163_standardize
    (μ : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => 0 < a0 ∧ ∀ a : Real, abs a ≤ a0 →
      Integrable (fun x : Real => Real.exp (a * x)) (μ : Measure Real)) :
    ∃ (ν : ProbabilityMeasure Real) (m σ : Real),
      0 ≤ σ ∧
      Measure.map (fun y : Real => m + σ * y) (ν : Measure Real) = (μ : Measure Real) ∧
      MeasureTheory.integral (ν : Measure Real) (fun y : Real => y) = 0 ∧
      variance (fun y : Real => y) (ν : Measure Real) = 1 ∧
      (Exists fun a0 : Real => 0 < a0 ∧ ∀ a : Real, abs a ≤ a0 →
        Integrable (fun y : Real => Real.exp (a * y)) (ν : Measure Real)) := by
  rcases (variance_nonneg (fun x : Real => x) (μ : Measure Real)).lt_or_eq with hpos | hzero
  · exact d4d73198_pos_case μ hexp hpos
  · exact d4d73198_zero_case μ hexp hzero.symm

open MeasureTheory ProbabilityTheory EthierKurtz in
private lemma kmt_transport_core_72bcd0a0
    (mu nu : ProbabilityMeasure Real) (m sig : Real)
    (hsig : 0 <= sig)
    (hmap : Measure.map (fun y : Real => m + sig * y) (nu : Measure Real) = (mu : Measure Real))
    (hmean : MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
    (hvariance : variance (fun y : Real => y) (nu : Measure Real) = 1)
    (hmu_mean : MeasureTheory.integral (mu : Measure Real) (fun y : Real => y) = m)
    (hmu_variance : variance (fun y : Real => y) (mu : Measure Real) = sig ^ 2)
    (happrox : kmtApproximation nu) :
    kmtApproximation mu := by
  obtain ⟨Q, hind, hlaw, hBM, C, K, lam, hC, hK, hlam, hbound⟩ := happrox
  let T : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} →
      (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} :=
    fun z => (fun i => m + sig * z.1 i, z.2)
  have hT : Measurable T := by
    refine Measurable.prodMk ?_ measurable_snd
    exact measurable_pi_lambda _ fun i => measurable_const.add
      (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst))
  have haff : Measurable (fun y : ℝ => m + sig * y) := by fun_prop
  have hcoord : ∀ i : ℕ,
      Measurable (fun z : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} => z.1 i) :=
    fun i => (measurable_pi_apply i).comp measurable_fst
  have hB : ∀ t : NNReal,
      Measurable (fun z : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} => z.2.val t) :=
    fun t => (measurable_pi_apply t).comp (measurable_subtype_coe.comp measurable_snd)
  have hQT : ((Q.map hT.aemeasurable : ProbabilityMeasure _) : Measure _) =
      (Q : Measure _).map T :=
    ProbabilityMeasure.toMeasure_map _ _
  refine ⟨Q.map hT.aemeasurable, ?_, ?_, ?_, ?_⟩
  · rw [hQT, iIndepFun_iff_measure_inter_preimage_eq_mul]
    have h2 := hind.comp (fun _ x => m + sig * x) (fun _ => haff)
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h2
    intro S sets hS
    have hmS : MeasurableSet (⋂ i ∈ S,
        (fun z : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} => z.1 i) ⁻¹' sets i) :=
      Finset.measurableSet_biInter S fun i hi => hcoord i (hS i hi)
    rw [Measure.map_apply hT hmS,
      Finset.prod_congr rfl fun i hi => Measure.map_apply hT (hcoord i (hS i hi))]
    simp only [Set.preimage_iInter]
    exact h2 S hS
  · intro i
    refine ⟨(hcoord i).aemeasurable, ?_⟩
    rw [hQT, Measure.map_map (hcoord i) hT]
    have hcomp : (fun z : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} => z.1 i) ∘ T
        = (fun y : ℝ => m + sig * y) ∘
          (fun z : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} => z.1 i) := rfl
    rw [hcomp, ← Measure.map_map haff (hcoord i), (hlaw i).map_eq, hmap]
  · refine ⟨⟨fun I => ?_⟩, ?_⟩
    · have hF : Measurable (fun z : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} =>
          I.restrict (fun t => z.2.val t)) :=
        measurable_pi_lambda _ fun t => hB t
      refine ⟨hF.aemeasurable, ?_⟩
      rw [hQT, Measure.map_map hF hT]
      exact (hBM.hasLaw I).map_eq
    · exact Filter.Eventually.of_forall fun z => z.2.property
  · have hm' : ∫ x : ℝ, x ∂(mu : Measure ℝ) = m := hmu_mean
    have hs' : Real.sqrt (variance (fun x : ℝ => x) (mu : Measure ℝ)) = sig := by
      rw [hmu_variance, Real.sqrt_sq hsig]
    have hm0 : ∫ x : ℝ, x ∂(nu : Measure ℝ) = 0 := hmean
    have hs1 : Real.sqrt (variance (fun x : ℝ => x) (nu : Measure ℝ)) = 1 := by
      rw [hvariance, Real.sqrt_one]
    simp only [hm0, hs1] at hbound
    simp only [hQT, hm', hs']
    have hmeasE : ∀ (n : ℕ) (c a b : ℝ), MeasurableSet
        {z : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b} |
          ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ c < |(∑ i ∈ Finset.range k, z.1 i) -
            (a * ((k : NNReal) : ℝ) + b * z.2.val (k : NNReal))|} := by
      intro n c a b
      simp only [Set.ofPred_exists, Set.ofPred_and]
      refine MeasurableSet.iUnion fun k =>
        (MeasurableSet.const _).inter ((MeasurableSet.const _).inter ?_)
      refine measurableSet_lt measurable_const ?_
      exact ((Finset.measurable_sum _ fun i _ => hcoord i).sub
        (measurable_const.add (measurable_const.mul (hB _)))).abs
    have halg : ∀ (z : (ℕ → ℝ) × {b : NNReal → ℝ // Continuous b}) (k : ℕ),
        (∑ i ∈ Finset.range k, (T z).1 i) -
            (m * ((k : NNReal) : ℝ) + sig * (T z).2.val (k : NNReal))
          = sig * ((∑ i ∈ Finset.range k, z.1 i) -
            (0 * ((k : NNReal) : ℝ) + 1 * z.2.val (k : NNReal))) := by
      intro z k
      simp only [T, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, ← Finset.mul_sum, NNReal.coe_natCast]
      ring
    rcases hsig.eq_or_lt with h0 | hpos
    · refine ⟨C, K, lam, hC, hK, hlam, ?_⟩
      intro n hn x hx
      rw [Measure.map_apply hT (hmeasE n _ _ _)]
      refine lt_of_le_of_lt (measure_mono ?_) (hbound n hn x hx)
      intro z hz
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hz
      obtain ⟨k, hk1, hkn, hlt⟩ := hz
      exfalso
      rw [halg z k, ← h0, zero_mul, abs_zero] at hlt
      have hlog : 0 ≤ Real.log (n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hn)
      have := mul_nonneg hC.le hlog
      linarith
    · refine ⟨sig * C, K, lam / sig, mul_pos hpos hC, hK, div_pos hlam hpos, ?_⟩
      intro n hn x hx
      rw [Measure.map_apply hT (hmeasE n _ _ _)]
      have hx' : 0 < x / sig := div_pos hx hpos
      have hlt2 := hbound n hn (x / sig) hx'
      have hexp : -lam * (x / sig) = -(lam / sig) * x := by ring
      rw [hexp] at hlt2
      refine lt_of_le_of_lt (measure_mono ?_) hlt2
      intro z hz
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hz ⊢
      obtain ⟨k, hk1, hkn, hlt⟩ := hz
      refine ⟨k, hk1, hkn, ?_⟩
      rw [halg z k, abs_mul, abs_of_pos hpos] at hlt
      have hC' : C * Real.log (n : ℝ) + x / sig = (sig * C * Real.log (n : ℝ) + x) / sig := by
        field_simp
      rw [hC', div_lt_iff₀ hpos]
      linarith

open MeasureTheory ProbabilityTheory EthierKurtz in
private lemma d2269163_image_transfer
    (μ ν : ProbabilityMeasure Real) (m σ : Real)
    (hσ : 0 ≤ σ)
    (hmap : Measure.map (fun y : Real => m + σ * y) (ν : Measure Real) = (μ : Measure Real))
    (hmean : MeasureTheory.integral (ν : Measure Real) (fun y : Real => y) = 0)
    (hvariance : variance (fun y : Real => y) (ν : Measure Real) = 1)
    (happrox : kmtApproximation ν) :
    kmtApproximation μ := by
  have hmeas : Measurable (fun y : Real => m + σ * y) := by fun_prop
  have hLp : MemLp (fun y : Real => y) 2 (ν : Measure Real) :=
    memLp_two_of_variance_ne_zero measurable_id.aestronglyMeasurable
      (by rw [hvariance]; exact one_ne_zero)
  have hint : Integrable (fun y : Real => y) (ν : Measure Real) :=
    hLp.integrable one_le_two
  have hmu_mean : MeasureTheory.integral (μ : Measure Real) (fun y : Real => y) = m := by
    rw [← hmap, integral_map hmeas.aemeasurable (by fun_prop)]
    rw [integral_add (integrable_const m) (hint.const_mul σ), integral_const,
      integral_const_mul, hmean]
    simp
  have hmu_variance : variance (fun y : Real => y) (μ : Measure Real) = σ ^ 2 := by
    rw [← hmap]
    have h1 := variance_id_map (μ := (ν : Measure Real)) hmeas.aemeasurable
    have h2 := variance_const_add (μ := (ν : Measure Real))
      (X := fun y : Real => σ * y) (by fun_prop) m
    have h3 := variance_const_mul σ (fun y : Real => y) (ν : Measure Real)
    calc variance (fun y : Real => y) (Measure.map (fun y : Real => m + σ * y) (ν : Measure Real))
        = variance (fun y : Real => m + σ * y) (ν : Measure Real) := h1
      _ = variance (fun y : Real => σ * y) (ν : Measure Real) := h2
      _ = σ ^ 2 * variance (fun y : Real => y) (ν : Measure Real) := h3
      _ = σ ^ 2 := by rw [hvariance, mul_one]
  exact kmt_transport_core_72bcd0a0 μ ν m σ hσ hmap hmean hvariance hmu_mean hmu_variance happrox

open MeasureTheory ProbabilityTheory in open scoped ENNReal NNReal in
theorem solution
    (H : ∀ (ν : ProbabilityMeasure Real),
      (Exists fun a0 : Real => 0 < a0∧∀ a : Real, abs a <= a0 ->
        Integrable (fun x : Real => Real.exp (a * x)) (ν : Measure Real)) ->
      MeasureTheory.integral (ν : Measure Real) (fun x : Real => x) = 0 ->
      variance (fun x : Real => x) (ν : Measure Real) = 1 ->
        ∃ Q : ProbabilityMeasure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}),
      iIndepFun (fun (i : ℕ) (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.1 i) (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) ∧
      (∀ i : ℕ, HasLaw (fun (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.1 i) (ν : Measure ℝ) (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}))) ∧
      IsBrownianReal (fun t (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.2.val t) (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) ∧
      ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
        let m := ∫ x : ℝ, x ∂(ν : Measure ℝ)
        let σ := Real.sqrt (variance (fun x : ℝ => x) (ν : Measure ℝ))
        let W := fun (t : ℝ≥0) (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) =>
          m * (t : ℝ) + σ * z.2.val t
        ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
          (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
            C * Real.log (n : ℝ) + x <
              |(∑ i ∈ Finset.range k, z.1 i) - W (k : ℝ≥0) z|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)))
    (μ : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => 0 < a0∧∀ a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (μ : Measure Real)) :
      ∃ Q : ProbabilityMeasure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}),
      iIndepFun (fun (i : ℕ) (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.1 i) (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) ∧
      (∀ i : ℕ, HasLaw (fun (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.1 i) (μ : Measure ℝ) (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}))) ∧
      IsBrownianReal (fun t (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.2.val t) (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) ∧
      ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
        let m := ∫ x : ℝ, x ∂(μ : Measure ℝ)
        let σ := Real.sqrt (variance (fun x : ℝ => x) (μ : Measure ℝ))
        let W := fun (t : ℝ≥0) (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) =>
          m * (t : ℝ) + σ * z.2.val t
        ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
          (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
            C * Real.log (n : ℝ) + x <
              |(∑ i ∈ Finset.range k, z.1 i) - W (k : ℝ≥0) z|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)) := by
  obtain ⟨ν, m, σ, hσ, hmap, hmean, hvar, hexpν⟩ := d2269163_standardize μ hexp
  have hν : EthierKurtz.kmtApproximation ν := H ν hexpν hmean hvar
  exact d2269163_image_transfer μ ν m σ hσ hmap hmean hvar hν
