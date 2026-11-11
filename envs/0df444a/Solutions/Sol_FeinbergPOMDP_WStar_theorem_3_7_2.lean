-- Prove2me | solution 2 for FeinbergPOMDP.WStar.theorem_3_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T01:46:37.105279+00:00
-- url     : https://prove2.me/submissions/5188318e-76e9-4a19-acc4-b779f4708f88

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model
import Theorems.Thm_FeinbergPOMDP_WStar_filter_exists
import Theorems.Thm_FeinbergPOMDP_WStar_theorem_3_5

open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

/-! Draft for FeinbergPOMDP.WStar.theorem_3_7 (7bcc0ff6). Glue layer: parts 1 and 3 from
TV continuity of R' and theorem_3_5; part 2 (Assumption H) from a filter, L1 convergence of
posterior integrals (Kara-Saldi-Yuksel 2019) and a countable convergence-determining family. -/

namespace FeinbergPOMDP.WStar.Draft7bcc

open FeinbergPOMDP.WStar

/-- TV continuity implies setwise continuity (test functions = indicators). -/
theorem setwise_of_tv {S T : Type*} [TopologicalSpace S] [MeasurableSpace T]
    (R : S → ProbabilityMeasure T) (h : IsTVContinuous R) : IsSetwiseContinuous R := by
  intro s ss hs C hC
  have hreal : Tendsto (fun n => ((R (ss n) : Measure T)).real C) atTop
      (𝓝 ((R s : Measure T).real C)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := h s ss hs (ε / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have key := hN n hn (C.indicator 1) (measurable_one.indicator hC) (fun t => by
      by_cases ht : t ∈ C <;> simp [ht])
    rw [integral_indicator_one hC, integral_indicator_one hC] at key
    rw [Real.dist_eq]; linarith
  have e : ∀ μ : ProbabilityMeasure T, ENNReal.ofReal ((μ : Measure T).real C) = (μ : Measure T) C :=
    fun μ => ofReal_measureReal (measure_ne_top _ _)
  have := ENNReal.tendsto_ofReal hreal
  simpa only [e] using this

/-- Child statement (KSY 2019): L1(R'(z,a)) convergence of posterior integrals. -/
def PosteriorL1 {X Y A : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [TopologicalSpace A] [MeasurableSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q] : Prop :=
  ∀ H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X, IsFilter P Q H →
    ∀ (z : ProbabilityMeasure X) (a : A) (zs : ℕ → ProbabilityMeasure X) (as : ℕ → A),
      Tendsto zs atTop (𝓝 z) → Tendsto as atTop (𝓝 a) → ∀ f : X →ᵇ ℝ,
        Tendsto (fun n => ∫⁻ y, ENNReal.ofReal |∫ x, f x ∂(H (zs n) (as n) y : Measure X) -
            ∫ x, f x ∂(H z a y : Measure X)| ∂(obsLaw P Q z a : Measure Y)) atTop (𝓝 0)

/-- Child statement: a countable convergence-determining family of bounded continuous functions. -/
def CountableDetermining (X : Type*) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] :
    Prop :=
  ∃ fs : ℕ → X →ᵇ ℝ, (∀ k, ‖fs k‖ ≤ 1) ∧
    ∀ (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X),
      (∀ k, Tendsto (fun n => ∫ x, fs k x ∂(μs n : Measure X)) atTop
        (𝓝 (∫ x, fs k x ∂(μ : Measure X)))) → Tendsto μs atTop (𝓝 μ)

/-- Child statement (Ranga Rao 1962, Thm 3.1): weak convergence is uniform over a uniformly bounded
family of functions equicontinuous at every point (separable metrizable `X`). -/
def RangaRao (X : Type*) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] : Prop :=
  ∀ {ι : Type} (F : ι → X → ℝ), (∀ x, EquicontinuousAt F x) → (∃ M : ℝ, ∀ i x, |F i x| ≤ M) →
    ∀ (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X), Tendsto μs atTop (𝓝 μ) →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ i,
        |∫ x, F i x ∂(μs n : Measure X) - ∫ x, F i x ∂(μ : Measure X)| ≤ ε

/-- Tannery in `ℝ≥0∞` via dominated convergence for the counting measure. -/
theorem ennreal_tannery (I : ℕ → ℕ → ℝ≥0∞) (hb : ∀ n k, I n k ≤ 2)
    (h0 : ∀ k, Tendsto (fun n => I n k) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' k, (2⁻¹ : ℝ≥0∞) ^ k * I n k) atTop (𝓝 0) := by
  have key := tendsto_lintegral_of_dominated_convergence (μ := (Measure.count : Measure ℕ))
    (F := fun n k => (2⁻¹ : ℝ≥0∞) ^ k * I n k) (f := fun _ => 0)
    (fun k => (2⁻¹ : ℝ≥0∞) ^ k * 2) (fun n => measurable_of_countable _)
    (fun n => Filter.Eventually.of_forall fun k =>
      show (2⁻¹ : ℝ≥0∞) ^ k * I n k ≤ (2⁻¹ : ℝ≥0∞) ^ k * 2 from
        mul_le_mul_of_nonneg_left (hb n k) bot_le) ?_
    (Filter.Eventually.of_forall fun k => by
      simpa using ENNReal.Tendsto.const_mul (h0 k) (Or.inr (ENNReal.pow_ne_top (by simp))))
  · simpa [lintegral_count] using key
  · rw [lintegral_count, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    simp only [ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.mul_ne_top (by simp) (by simp)

theorem assumptionH_of {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y]
    [TopologicalSpace A] [MeasurableSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hex : ∃ H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X, IsFilter P Q H)
    (hL1 : PosteriorL1 P Q) (hCD : CountableDetermining X) : AssumptionH P Q := by
  obtain ⟨H, hF⟩ := hex
  obtain ⟨fs, hfs1, hfsdet⟩ := hCD
  refine ⟨H, hF, ?_⟩
  intro z a zs as hz ha
  have hmeasI : ∀ (w : ProbabilityMeasure X) (b : A) (f : X →ᵇ ℝ),
      Measurable (fun y => ∫ x, f x ∂(H w b y : Measure X)) := by
    intro w b f
    let κ : Kernel Y X := ⟨fun y => (H w b y : Measure X),
      measurable_subtype_coe.comp (hF.measurable w b)⟩
    exact (StronglyMeasurable.integral_kernel (κ := κ)
      f.continuous.measurable.stronglyMeasurable).measurable
  have hbd : ∀ (ν : ProbabilityMeasure X) (k : ℕ), |∫ x, fs k x ∂(ν : Measure X)| ≤ 1 := by
    intro ν k
    have := BoundedContinuousFunction.norm_integral_le_norm (μ := (ν : Measure X)) (fs k)
    rw [Real.norm_eq_abs] at this
    exact this.trans (hfs1 k)
  let e : ℕ → ℕ → Y → ℝ≥0∞ := fun n k y => ENNReal.ofReal
    |∫ x, fs k x ∂(H (zs n) (as n) y : Measure X) - ∫ x, fs k x ∂(H z a y : Measure X)|
  have he_meas : ∀ n k, Measurable (e n k) := fun n k =>
    ENNReal.measurable_ofReal.comp (((hmeasI _ _ _).sub (hmeasI _ _ _)).abs)
  have he_le : ∀ n k y, e n k y ≤ 2 := by
    intro n k y
    have h1 := hbd (H (zs n) (as n) y) k
    have h2 := hbd (H z a y) k
    have : |∫ x, fs k x ∂(H (zs n) (as n) y : Measure X) - ∫ x, fs k x ∂(H z a y : Measure X)|
        ≤ 2 := (abs_sub _ _).trans (by linarith)
    calc e n k y ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal this
      _ = 2 := by simp
  let G : ℕ → Y → ℝ≥0∞ := fun n y => ∑' k, (2⁻¹ : ℝ≥0∞) ^ k * e n k y
  have hG_meas : ∀ n, Measurable (G n) := fun n =>
    Measurable.ennreal_tsum fun k => (he_meas n k).const_mul _
  have hG_int : ∀ n, ∫⁻ y, G n y ∂(obsLaw P Q z a : Measure Y) =
      ∑' k, (2⁻¹ : ℝ≥0∞) ^ k * ∫⁻ y, e n k y ∂(obsLaw P Q z a : Measure Y) := by
    intro n
    rw [lintegral_tsum (fun k => ((he_meas n k).const_mul _).aemeasurable)]
    congr 1; ext k
    rw [lintegral_const_mul _ (he_meas n k)]
  have hI0 : ∀ k, Tendsto (fun n => ∫⁻ y, e n k y ∂(obsLaw P Q z a : Measure Y)) atTop (𝓝 0) :=
    fun k => hL1 H hF z a zs as hz ha (fs k)
  have hIle : ∀ n k, ∫⁻ y, e n k y ∂(obsLaw P Q z a : Measure Y) ≤ 2 := fun n k =>
    (lintegral_mono fun y => he_le n k y).trans (by simp)
  have hGt : Tendsto (fun n => ∫⁻ y, G n y ∂(obsLaw P Q z a : Measure Y)) atTop (𝓝 0) := by
    simp_rw [hG_int]
    exact ennreal_tannery _ hIle hI0
  have hev : ∀ i, ∀ᶠ n in atTop,
      ∫⁻ y, G n y ∂(obsLaw P Q z a : Measure Y) ≤ (2⁻¹ : ℝ≥0∞) ^ i := fun i =>
    (ENNReal.tendsto_nhds_zero.1 hGt) _ (ENNReal.pow_pos (by simp) i)
  obtain ⟨φ, hφ, hφle⟩ := extraction_forall_of_eventually hev
  have hsum_int : ∫⁻ y, ∑' i, G (φ i) y ∂(obsLaw P Q z a : Measure Y) ≠ ∞ := by
    rw [lintegral_tsum (fun i => (hG_meas _).aemeasurable)]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hφle)
    rw [ENNReal.tsum_geometric]
    simp
  have hae : ∀ᵐ y ∂(obsLaw P Q z a : Measure Y), ∑' i, G (φ i) y < ∞ :=
    ae_lt_top (Measurable.ennreal_tsum fun i => hG_meas _) hsum_int
  have key : ∀ y, ∑' i, G (φ i) y < ∞ →
      Tendsto (fun i => H (zs (φ i)) (as (φ i)) y) atTop (𝓝 (H z a y)) := by
    intro y hy
    have hG0 : Tendsto (fun i => G (φ i) y) atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top hy.ne
    apply hfsdet
    intro k
    have he0 : Tendsto (fun i => e (φ i) k y) atTop (𝓝 0) := by
      have h1 : ∀ i, e (φ i) k y ≤ 2 ^ k * G (φ i) y := fun i => by
        have hle := ENNReal.le_tsum (f := fun k => (2⁻¹ : ℝ≥0∞) ^ k * e (φ i) k y) k
        calc e (φ i) k y = 2 ^ k * ((2⁻¹ : ℝ≥0∞) ^ k * e (φ i) k y) := by
              rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (by simp) (by simp), one_pow,
                one_mul]
          _ ≤ 2 ^ k * G (φ i) y := by gcongr
      have h2 : Tendsto (fun i => (2 : ℝ≥0∞) ^ k * G (φ i) y) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul hG0 (Or.inr (ENNReal.pow_ne_top (by simp)))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
        (fun i => bot_le) h1
    have hr : Tendsto (fun i => |∫ x, fs k x ∂(H (zs (φ i)) (as (φ i)) y : Measure X) -
        ∫ x, fs k x ∂(H z a y : Measure X)|) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp he0
      simpa [e, Function.comp_def, ENNReal.toReal_ofReal (abs_nonneg _)] using this
    exact tendsto_iff_norm_sub_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using hr)
  refine ⟨φ, hφ, (toMeasurable (obsLaw P Q z a : Measure Y) {y | ¬ (∑' i, G (φ i) y < ∞)})ᶜ,
    (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · rw [prob_compl_eq_one_iff (measurableSet_toMeasurable _ _), measure_toMeasurable]
    exact ae_iff.1 hae
  · intro y hy
    apply key y
    by_contra h
    exact hy (subset_toMeasurable _ _ h)

/-! ### Child 6: a countable convergence-determining family (open-set Portmanteau). -/

theorem delta_pos (m : ℕ) : (0 : ℝ) < 1 / ((m : ℝ) + 1) := Nat.one_div_pos_of_nat

/-- Real-valued thickened indicator. -/
noncomputable def thR {X : Type*} [PseudoMetricSpace X] (m : ℕ) (E : Set X) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => (thickenedIndicator (delta_pos m) E x : ℝ),
      NNReal.continuous_coe.comp (thickenedIndicator (delta_pos m) E).continuous⟩ 1
    (fun x y => by
      have h1 := thickenedIndicator_le_one (delta_pos m) E x
      have h2 := thickenedIndicator_le_one (delta_pos m) E y
      have h1' : ((thickenedIndicator (delta_pos m) E x : ℝ≥0) : ℝ) ≤ 1 := by exact_mod_cast h1
      have h2' : ((thickenedIndicator (delta_pos m) E y : ℝ≥0) : ℝ) ≤ 1 := by exact_mod_cast h2
      have h3 := (thickenedIndicator (delta_pos m) E x).2
      have h4 := (thickenedIndicator (delta_pos m) E y).2
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      rw [abs_le]; constructor <;> linarith)

theorem thR_apply {X : Type*} [PseudoMetricSpace X] (m : ℕ) (E : Set X) (x : X) :
    thR m E x = (thickenedIndicator (delta_pos m) E x : ℝ) := rfl

/-- Approximation of an open set `V` from below. -/
noncomputable def hfun {X : Type*} [PseudoMetricSpace X] (V : Set X) (m : ℕ) : X →ᵇ ℝ :=
  1 - thR m Vᶜ

theorem hfun_apply {X : Type*} [PseudoMetricSpace X] (V : Set X) (m : ℕ) (x : X) :
    hfun V m x = 1 - (thickenedIndicator (delta_pos m) Vᶜ x : ℝ) := rfl

theorem hfun_bounds {X : Type*} [PseudoMetricSpace X] (V : Set X) (m : ℕ) (x : X) :
    0 ≤ hfun V m x ∧ hfun V m x ≤ 1 := by
  rw [hfun_apply]
  have h1 : ((thickenedIndicator (delta_pos m) Vᶜ x : ℝ≥0) : ℝ) ≤ 1 := by
    exact_mod_cast thickenedIndicator_le_one (delta_pos m) Vᶜ x
  have h3 := (thickenedIndicator (delta_pos m) Vᶜ x).2
  constructor <;> linarith

theorem hfun_norm {X : Type*} [PseudoMetricSpace X] (V : Set X) (m : ℕ) : ‖hfun V m‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le zero_le_one).2 fun x => by
    rw [Real.norm_eq_abs, abs_le]
    have := hfun_bounds V m x
    constructor <;> linarith

theorem hfun_le_indicator {X : Type*} [PseudoMetricSpace X] (V : Set X) (m : ℕ) (x : X) :
    hfun V m x ≤ V.indicator 1 x := by
  by_cases hx : x ∈ V
  · rw [Set.indicator_of_mem hx]; exact (hfun_bounds V m x).2
  · rw [Set.indicator_of_notMem hx, hfun_apply,
      thickenedIndicator_one (delta_pos m) Vᶜ hx]
    simp

theorem open_le_liminf {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (V G : Set X) (hV : IsOpen V) (hVG : V ⊆ G)
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hconv : ∀ m, Tendsto (fun n => ∫ x, hfun V m x ∂(μs n : Measure X)) atTop
      (𝓝 (∫ x, hfun V m x ∂(μ : Measure X)))) :
    (μ : Measure X) V ≤ liminf (fun n => (μs n : Measure X) G) atTop := by
  have step : ∀ (ν : ProbabilityMeasure X) m,
      ENNReal.ofReal (∫ x, hfun V m x ∂(ν : Measure X)) ≤ (ν : Measure X) G := by
    intro ν m
    have hle : ∫ x, hfun V m x ∂(ν : Measure X) ≤ (ν : Measure X).real V := by
      rw [← integral_indicator_one hV.measurableSet]
      exact integral_mono ((hfun V m).integrable _)
        ((integrable_const (1 : ℝ)).indicator hV.measurableSet) (hfun_le_indicator V m)
    calc ENNReal.ofReal (∫ x, hfun V m x ∂(ν : Measure X))
        ≤ ENNReal.ofReal ((ν : Measure X).real V) := ENNReal.ofReal_le_ofReal hle
      _ = (ν : Measure X) V := ofReal_measureReal (measure_ne_top _ _)
      _ ≤ (ν : Measure X) G := measure_mono hVG
  have hm : ∀ m, ENNReal.ofReal (∫ x, hfun V m x ∂(μ : Measure X)) ≤
      liminf (fun n => (μs n : Measure X) G) atTop := by
    intro m
    have hlim := ENNReal.tendsto_ofReal (hconv m)
    rw [← hlim.liminf_eq]
    exact liminf_le_liminf (Filter.Eventually.of_forall fun n => step (μs n) m)
  -- the approximants converge to `μ V`
  have hint : ∀ m, ∫ x, hfun V m x ∂(μ : Measure X) =
      1 - (∫⁻ x, (thickenedIndicator (delta_pos m) Vᶜ x : ℝ≥0∞) ∂(μ : Measure X)).toReal := by
    intro m
    have e1 : ∫ x, hfun V m x ∂(μ : Measure X) =
        ∫ x, (1 : ℝ) ∂(μ : Measure X) - ∫ x, thR m Vᶜ x ∂(μ : Measure X) :=
      integral_sub (integrable_const _) ((thR m Vᶜ).integrable _)
    rw [e1, integral_const, probReal_univ, one_smul]
    congr 1
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by
        rw [thR_apply]; exact (thickenedIndicator (delta_pos m) Vᶜ x).2)
      (thR m Vᶜ).continuous.aestronglyMeasurable]
    simp only [thR_apply, ENNReal.ofReal_coe_nnreal]
  have hT := tendsto_lintegral_thickenedIndicator_of_isClosed (μ : Measure X) hV.isClosed_compl
    delta_pos tendsto_one_div_add_atTop_nhds_zero_nat
  have hT2 : Tendsto (fun m => ENNReal.ofReal (∫ x, hfun V m x ∂(μ : Measure X))) atTop
      (𝓝 ((μ : Measure X) V)) := by
    simp_rw [hint]
    have h1 := ((ENNReal.tendsto_toReal (measure_ne_top (μ : Measure X) Vᶜ)).comp hT).const_sub 1
    have h2 := ENNReal.tendsto_ofReal h1
    have hlimV : ENNReal.ofReal (1 - ((μ : Measure X) Vᶜ).toReal) = (μ : Measure X) V := by
      rw [prob_compl_eq_one_sub hV.measurableSet,
        ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one, sub_sub_cancel,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [← hlimV]
    exact h2
  exact le_of_tendsto' hT2 hm

theorem countableDetermining_of (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] : CountableDetermining X := by
  classical
  let _ := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis X
  obtain ⟨B, hB⟩ : ∃ B : ℕ → Set X, insert ∅ b = Set.range B :=
    (hbc.insert ∅).exists_eq_range (Set.insert_nonempty _ _)
  have hBopen : ∀ i, IsOpen (B i) := by
    intro i
    have : B i ∈ insert ∅ b := hB ▸ Set.mem_range_self i
    rcases this with h | h
    · rw [h]; exact isOpen_empty
    · exact hb.isOpen h
  have hBcov : ∀ G : Set X, IsOpen G → ∀ x ∈ G, ∃ i, x ∈ B i ∧ B i ⊆ G := by
    intro G hG x hx
    obtain ⟨s, hs, hxs, hsG⟩ := hb.exists_subset_of_mem_open hx hG
    have : s ∈ Set.range B := hB ▸ Set.mem_insert_of_mem _ hs
    obtain ⟨i, rfl⟩ := this
    exact ⟨i, hxs, hsG⟩
  let V : Finset ℕ → Set X := fun s => ⋃ i ∈ s, B i
  have hVopen : ∀ s, IsOpen (V s) := fun s => isOpen_biUnion fun i _ => hBopen i
  obtain ⟨e, he⟩ := exists_surjective_nat (Finset ℕ × ℕ)
  refine ⟨fun n => hfun (V (e n).1) (e n).2, fun n => hfun_norm _ _, ?_⟩
  intro μs μ hconv
  apply tendsto_of_forall_isOpen_le_liminf'
  intro G hG
  have hconv' : ∀ s m, Tendsto (fun n => ∫ x, hfun (V s) m x ∂(μs n : Measure X)) atTop
      (𝓝 (∫ x, hfun (V s) m x ∂(μ : Measure X))) := by
    intro s m
    obtain ⟨n, hn⟩ := he (s, m)
    have := hconv n
    simp only [hn] at this
    exact this
  let C : ℕ → Set X := fun i => if B i ⊆ G then B i else ∅
  have hCU : ⋃ i, C i = G := by
    ext x
    simp only [Set.mem_iUnion, C]
    constructor
    · rintro ⟨i, hi⟩
      split_ifs at hi with h
      exacts [h hi, hi.elim]
    · intro hx
      obtain ⟨i, hxi, hiG⟩ := hBcov G hG x hx
      exact ⟨i, by rw [if_pos hiG]; exact hxi⟩
  have hacc := tendsto_measure_iUnion_accumulate (μ := (μ : Measure X)) (f := C)
  rw [hCU] at hacc
  refine le_of_tendsto' hacc fun N => ?_
  let s := (Finset.range (N + 1)).filter (fun i => B i ⊆ G)
  have h1 : Set.accumulate C N ⊆ V s := by
    intro x hx
    simp only [Set.mem_accumulate, C] at hx
    obtain ⟨i, hiN, hi⟩ := hx
    split_ifs at hi with h
    · simp only [V, s, Set.mem_iUnion, Finset.mem_filter, Finset.mem_range]
      exact ⟨i, ⟨by omega, h⟩, hi⟩
    · exact hi.elim
  have h2 : V s ⊆ G := by
    intro x hx
    simp only [V, s, Set.mem_iUnion, Finset.mem_filter] at hx
    obtain ⟨i, ⟨-, h⟩, hi⟩ := hx
    exact h hi
  exact (measure_mono h1).trans (open_le_liminf (V s) G (hVopen s) h2 μs μ (hconv' s))


/-! ### Child 5: Ranga Rao (1962, Thm 3.1). -/

noncomputable def bcfOf {X : Type*} [TopologicalSpace X] (f : X → ℝ) (hf : Continuous f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) : X →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * C) (fun x y => by
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    have h1 := hC x
    have h2 := hC y
    calc |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
      _ ≤ 2 * C := by linarith)

theorem bcfOf_apply {X : Type*} [TopologicalSpace X] (f : X → ℝ) (hf : Continuous f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) (x : X) : bcfOf f hf C hC x = f x := rfl

set_option maxHeartbeats 1000000 in
theorem rr_core {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [SecondCountableTopology X] {ι : Type*} (F : ι → X → ℝ) (hEq : ∀ x, EquicontinuousAt F x)
    (M : ℝ) (hM : ∀ i x, |F i x| ≤ M) (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hμ : Tendsto μs atTop (𝓝 μ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ i,
      |∫ x, F i x ∂(μs n : Measure X) - ∫ x, F i x ∂(μ : Measure X)| ≤ ε := by
  have hne : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := measure_univ (μ := (μ : Measure X))
    rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at this
    exact zero_ne_one this
  set M₀ := max M 0 with hM₀_def
  have hM₀0 : 0 ≤ M₀ := le_max_right _ _
  have hM₀ : ∀ i x, |F i x| ≤ M₀ := fun i x => (hM i x).trans (le_max_left _ _)
  set η := ε / (4 * M₀ + 2) with hη_def
  have hη : 0 < η := div_pos hε (by linarith)
  have hηe : (4 * M₀ + 2) * η = ε := by rw [hη_def]; field_simp
  have hcont : ∀ i, Continuous (F i) := fun i =>
    continuous_iff_continuousAt.2 fun x => (hEq x).continuousAt i
  have hδ : ∀ x, ∃ δ > 0, ∀ y, dist y x < δ → ∀ i, dist (F i x) (F i y) < η :=
    fun x => Metric.equicontinuousAt_iff.1 (hEq x) η hη
  choose δ hδpos hδ using hδ
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x => Metric.ball x (δ x / 2)) (fun x => Metric.isOpen_ball)
  have hmem : ∀ y, ∃ x ∈ T, y ∈ Metric.ball x (δ x / 2) := by
    intro y
    have : y ∈ ⋃ x, Metric.ball x (δ x / 2) :=
      Set.mem_iUnion.2 ⟨y, Metric.mem_ball_self (by linarith [hδpos y])⟩
    rw [← hTU] at this
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hxT, hyx⟩ := this
    exact ⟨x, hxT, hyx⟩
  have hTne : T.Nonempty := by
    obtain ⟨x0⟩ := hne
    obtain ⟨x, hx, -⟩ := hmem x0
    exact ⟨x, hx⟩
  obtain ⟨c, hc⟩ := hTc.exists_eq_range hTne
  let r : ℕ → ℝ := fun j => δ (c j) / 2
  have hr : ∀ j, 0 < r j := fun j => by simp only [r]; linarith [hδpos (c j)]
  have hcov : ∀ y, ∃ j, dist y (c j) < r j := by
    intro y
    obtain ⟨x, hxT, hyx⟩ := hmem y
    rw [hc] at hxT
    obtain ⟨j, rfl⟩ := hxT
    exact ⟨j, hyx⟩
  have hclose : ∀ j y, dist y (c j) < 2 * r j → ∀ i, |F i y - F i (c j)| < η := by
    intro j y hy i
    have := hδ (c j) y (by simp only [r] at hy; linarith) i
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this
  let φ : ℕ → X → ℝ := fun j y => max 0 (min 1 (2 - dist y (c j) / r j))
  have hφc : ∀ j, Continuous (φ j) := fun j =>
    continuous_const.max (continuous_const.min
      (continuous_const.sub ((continuous_id.dist continuous_const).div_const _)))
  have hφ0 : ∀ j y, 0 ≤ φ j y := fun j y => le_max_left _ _
  have hφ1 : ∀ j y, φ j y ≤ 1 := fun j y => max_le zero_le_one (min_le_left _ _)
  have hφone : ∀ j y, dist y (c j) < r j → φ j y = 1 := by
    intro j y hy
    have h1 : 1 ≤ 2 - dist y (c j) / r j := by
      have : dist y (c j) / r j < 1 := (div_lt_one (hr j)).2 hy
      linarith
    simp only [φ, min_eq_left h1]
    exact max_eq_right zero_le_one
  have hφsupp : ∀ j y, φ j y ≠ 0 → dist y (c j) < 2 * r j := by
    intro j y hy
    by_contra h
    push_neg at h
    apply hy
    have : 2 - dist y (c j) / r j ≤ 0 := by
      have : 2 ≤ dist y (c j) / r j := (le_div_iff₀ (hr j)).2 h
      linarith
    simp only [φ]
    exact max_eq_left (min_le_of_right_le this)
  let Pf : ℕ → X → ℝ := fun J y => ∏ l ∈ Finset.range J, (1 - φ l y)
  have hPc : ∀ J, Continuous (Pf J) := fun J =>
    continuous_finset_prod _ fun l _ => continuous_const.sub (hφc l)
  have hP0 : ∀ J y, 0 ≤ Pf J y := fun J y =>
    Finset.prod_nonneg fun l _ => by linarith [hφ1 l y]
  have hP1 : ∀ J y, Pf J y ≤ 1 := fun J y =>
    Finset.prod_le_one (fun l _ => by linarith [hφ1 l y]) (fun l _ => by linarith [hφ0 l y])
  let ρ : ℕ → X → ℝ := fun j y => Pf j y * φ j y
  have hρc : ∀ j, Continuous (ρ j) := fun j => (hPc j).mul (hφc j)
  have hρ0 : ∀ j y, 0 ≤ ρ j y := fun j y => mul_nonneg (hP0 j y) (hφ0 j y)
  have htel : ∀ J y, ∑ j ∈ Finset.range J, ρ j y = 1 - Pf J y := by
    intro J y
    induction J with
    | zero => simp [Pf]
    | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Pf, ρ, Finset.prod_range_succ]
      ring
  have hPlim : ∀ y, Tendsto (fun J => Pf J y) atTop (𝓝 0) := by
    intro y
    obtain ⟨k, hk⟩ := hcov y
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop k] with J hJ
    symm
    apply Finset.prod_eq_zero (Finset.mem_range.2 hJ)
    rw [hφone k y hk]
    ring
  let bP : ℕ → X →ᵇ ℝ := fun J => bcfOf (Pf J) (hPc J) 1
    (fun y => by rw [abs_of_nonneg (hP0 J y)]; exact hP1 J y)
  let bρ : ℕ → X →ᵇ ℝ := fun j => bcfOf (ρ j) (hρc j) 1
    (fun y => by rw [abs_of_nonneg (hρ0 j y)]; exact mul_le_one₀ (hP1 j y) (hφ0 j y) (hφ1 j y))
  let bF : ι → X →ᵇ ℝ := fun i => bcfOf (F i) (hcont i) M₀ (hM₀ i)
  have hE : ∀ (ν : ProbabilityMeasure X) J i,
      |∫ x, F i x ∂(ν : Measure X) -
        ∑ j ∈ Finset.range J, F i (c j) * ∫ x, ρ j x ∂(ν : Measure X)|
        ≤ η + M₀ * ∫ x, Pf J x ∂(ν : Measure X) := by
    intro ν J i
    have hint : ∀ j, Integrable (ρ j) (ν : Measure X) := fun j => (bρ j).integrable _
    have hFint : Integrable (F i) (ν : Measure X) := (bF i).integrable _
    have hPint : Integrable (Pf J) (ν : Measure X) := (bP J).integrable _
    have e1 : ∫ x, F i x ∂(ν : Measure X) -
        ∑ j ∈ Finset.range J, F i (c j) * ∫ x, ρ j x ∂(ν : Measure X) =
        ∫ x, (F i x - ∑ j ∈ Finset.range J, F i (c j) * ρ j x) ∂(ν : Measure X) := by
      rw [integral_sub hFint (integrable_finset_sum _ fun j _ => (hint j).const_mul _),
        integral_finset_sum _ fun j _ => (hint j).const_mul _]
      simp_rw [integral_const_mul]
    rw [e1]
    have hpt : ∀ x, |F i x - ∑ j ∈ Finset.range J, F i (c j) * ρ j x| ≤ η + M₀ * Pf J x := by
      intro x
      have hsplit : F i x - ∑ j ∈ Finset.range J, F i (c j) * ρ j x =
          ∑ j ∈ Finset.range J, ρ j x * (F i x - F i (c j)) + Pf J x * F i x := by
        have ht := htel J x
        have : ∑ j ∈ Finset.range J, ρ j x * (F i x - F i (c j)) =
            F i x * ∑ j ∈ Finset.range J, ρ j x - ∑ j ∈ Finset.range J, F i (c j) * ρ j x := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [this, ht]
        ring
      rw [hsplit]
      have h1 : |∑ j ∈ Finset.range J, ρ j x * (F i x - F i (c j))| ≤ η := by
        calc _ ≤ ∑ j ∈ Finset.range J, |ρ j x * (F i x - F i (c j))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ Finset.range J, ρ j x * η := by
            apply Finset.sum_le_sum
            intro j _
            rw [abs_mul, abs_of_nonneg (hρ0 j x)]
            by_cases hφj : φ j x = 0
            · simp [ρ, hφj]
            · exact mul_le_mul_of_nonneg_left (hclose j x (hφsupp j x hφj) i).le (hρ0 j x)
          _ = (1 - Pf J x) * η := by rw [← Finset.sum_mul, htel]
          _ ≤ η := by nlinarith [hP0 J x, hη]
      have h2 : |Pf J x * F i x| ≤ M₀ * Pf J x := by
        rw [abs_mul, abs_of_nonneg (hP0 J x), mul_comm]
        exact mul_le_mul_of_nonneg_right (hM₀ i x) (hP0 J x)
      calc _ ≤ |∑ j ∈ Finset.range J, ρ j x * (F i x - F i (c j))| + |Pf J x * F i x| :=
            abs_add_le _ _
        _ ≤ _ := add_le_add h1 h2
    calc |∫ x, (F i x - ∑ j ∈ Finset.range J, F i (c j) * ρ j x) ∂(ν : Measure X)|
        ≤ ∫ x, (η + M₀ * Pf J x) ∂(ν : Measure X) := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_of_norm_le ((integrable_const _).add (hPint.const_mul _))
            (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hpt x)
      _ = η + M₀ * ∫ x, Pf J x ∂(ν : Measure X) := by
          rw [integral_add (integrable_const _) (hPint.const_mul _), integral_const,
            integral_const_mul, probReal_univ, one_smul]
  have hPint_lim : Tendsto (fun J => ∫ x, Pf J x ∂(μ : Measure X)) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := (μ : Measure X))
      (F := fun J x => Pf J x) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun J => (hPc J).aestronglyMeasurable) (integrable_const _)
      (fun J => Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hP0 J x)]; exact hP1 J x)
      (Filter.Eventually.of_forall hPlim)
    simpa using this
  obtain ⟨J, hJ⟩ := (hPint_lim.eventually (gt_mem_nhds hη)).exists
  have hwk : ∀ f : X →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂(μs n : Measure X)) atTop
      (𝓝 (∫ x, f x ∂(μ : Measure X))) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hμ
  have hPn : ∀ᶠ n in atTop, ∫ x, Pf J x ∂(μs n : Measure X) < 2 * η := by
    have h := hwk (bP J)
    simp only [bP, bcfOf_apply] at h
    exact h.eventually (gt_mem_nhds (by linarith))
  have hΔ : ∀ᶠ n in atTop, ∑ j ∈ Finset.range J,
      |∫ x, ρ j x ∂(μs n : Measure X) - ∫ x, ρ j x ∂(μ : Measure X)| < η := by
    have h : Tendsto (fun n => ∑ j ∈ Finset.range J,
        |∫ x, ρ j x ∂(μs n : Measure X) - ∫ x, ρ j x ∂(μ : Measure X)|) atTop
        (𝓝 (∑ j ∈ Finset.range J,
          |∫ x, ρ j x ∂(μ : Measure X) - ∫ x, ρ j x ∂(μ : Measure X)|)) :=
      tendsto_finset_sum _ fun j _ => ((hwk (bρ j)).sub tendsto_const_nhds).abs
    simp only [sub_self, abs_zero, Finset.sum_const_zero] at h
    exact h.eventually (gt_mem_nhds hη)
  obtain ⟨N, hN⟩ := (hPn.and hΔ).exists_forall_of_atTop
  refine ⟨N, fun n hn i => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  have e1 := hE (μs n) J i
  have e2 := hE μ J i
  have hsum : |∑ j ∈ Finset.range J, F i (c j) * ∫ x, ρ j x ∂(μs n : Measure X) -
      ∑ j ∈ Finset.range J, F i (c j) * ∫ x, ρ j x ∂(μ : Measure X)| ≤ M₀ * η := by
    rw [← Finset.sum_sub_distrib]
    calc _ ≤ ∑ j ∈ Finset.range J, |F i (c j) * ∫ x, ρ j x ∂(μs n : Measure X) -
          F i (c j) * ∫ x, ρ j x ∂(μ : Measure X)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range J,
          M₀ * |∫ x, ρ j x ∂(μs n : Measure X) - ∫ x, ρ j x ∂(μ : Measure X)| := by
          apply Finset.sum_le_sum
          intro j _
          rw [← mul_sub, abs_mul]
          exact mul_le_mul_of_nonneg_right (hM₀ i (c j)) (abs_nonneg _)
      _ = M₀ * ∑ j ∈ Finset.range J,
          |∫ x, ρ j x ∂(μs n : Measure X) - ∫ x, ρ j x ∂(μ : Measure X)| := by
          rw [Finset.mul_sum]
      _ ≤ M₀ * η := mul_le_mul_of_nonneg_left h2.le hM₀0
  have k1 : M₀ * ∫ x, Pf J x ∂(μs n : Measure X) ≤ M₀ * (2 * η) :=
    mul_le_mul_of_nonneg_left h1.le hM₀0
  have k2 : M₀ * ∫ x, Pf J x ∂(μ : Measure X) ≤ M₀ * η := mul_le_mul_of_nonneg_left hJ.le hM₀0
  rw [abs_le] at e1 e2 hsum ⊢
  constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2, hsum.1, hsum.2]

theorem rangaRao_of (X : Type*) [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] : RangaRao X := by
  intro ι F hEq hM μs μ hμ ε hε
  let _ := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨M, hM⟩ := hM
  exact rr_core F hEq M hM μs μ hμ ε hε

/-! ### Child 1: total-variation continuity of `R'` (corollary_5_4). -/

theorem abs_int_le {β : Type*} [MeasurableSpace β] (μ : Measure β) [IsProbabilityMeasure μ]
    (f : β → ℝ) (C : ℝ) (hC : ∀ x, |f x| ≤ C) : |∫ x, f x ∂μ| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := C)
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  simpa [Real.norm_eq_abs] using this

theorem integral_bind_markov {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] (μ : Measure α) [IsProbabilityMeasure μ]
    (g : β → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) :
    ∫ x, g x ∂(κ ∘ₘ μ) = ∫ a, ∫ x, g x ∂(κ a) ∂μ := by
  rw [← Measure.snd_compProd, Measure.snd, integral_map measurable_snd.aemeasurable
    hg.aestronglyMeasurable]
  rw [Measure.integral_compProd]
  exact Integrable.of_bound (hg.comp measurable_snd).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hC p.2)

/-- Augmented kernel `(x, b) ↦ P(x, b) ⊗ δ_b`. -/
noncomputable def augK {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] : Kernel (X × A) (X × A) :=
  P ×ₖ Kernel.deterministic Prod.snd measurable_snd

theorem augK_apply {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (p : X × A) :
    augK P p = (P p).prod (Measure.dirac p.2) := by
  rw [augK, Kernel.prod_apply, Kernel.deterministic_apply]

theorem augK_isMarkov {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] : IsMarkovKernel (augK P) := by
  unfold augK; infer_instance

attribute [local instance] augK_isMarkov

/-- `ν(z, a)`: law of `(x', a)` with `x ~ z`, `x' ~ P(·|x, a)`. -/
noncomputable def nuM {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (z : ProbabilityMeasure X) (a : A) :
    ProbabilityMeasure (X × A) :=
  ⟨augK P ∘ₘ (z : Measure X).prod (Measure.dirac a), inferInstance⟩

theorem integral_nuM {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (z : ProbabilityMeasure X) (a : A)
    (F : X × A → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ p, |F p| ≤ C) :
    ∫ p, F p ∂(nuM P z a : Measure (X × A)) =
      ∫ x, ∫ x', F (x', a) ∂(P (x, a)) ∂(z : Measure X) := by
  show ∫ p, F p ∂(augK P ∘ₘ (z : Measure X).prod (Measure.dirac a)) = _
  rw [integral_bind_markov (augK P) _ F hF C hC, Measure.prod_dirac,
    integral_map measurable_prodMk_right.aemeasurable
      ((hF.stronglyMeasurable.integral_kernel (κ := augK P)).measurable).aestronglyMeasurable]
  congr 1
  funext x
  rw [augK_apply, Measure.prod_dirac,
    integral_map measurable_prodMk_right.aemeasurable hF.aestronglyMeasurable]

theorem integral_obsLaw {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (f : Y → ℝ) (hf : Measurable f) (hfb : ∀ y, |f y| ≤ 1) (z : ProbabilityMeasure X) (a : A) :
    ∫ y, f y ∂(obsLaw P Q z a : Measure Y) =
      ∫ x, ∫ x', (∫ y, f y ∂(Q (a, x'))) ∂(P (x, a)) ∂(z : Measure X) := by
  have hG : Measurable (fun x' : X => ∫ y, f y ∂(Q (a, x'))) :=
    (hf.stronglyMeasurable.integral_kernel (κ := Q)).measurable.comp measurable_prodMk_left
  rw [obsLaw, ProbabilityMeasure.toMeasure_map,
    integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable]
  show ∫ p, f p.2 ∂(((P.comap (fun x => (x, a)) measurable_prodMk_right) ∘ₘ (z : Measure X)) ⊗ₘ
      (Q.comap (fun x' => (a, x')) measurable_prodMk_left)) = _
  rw [Measure.integral_compProd (f := fun p : X × Y => f p.2) (Integrable.of_bound (hf.comp measurable_snd).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hfb p.2))]
  simp only [Kernel.comap_apply]
  rw [integral_bind_markov _ _ _ hG 1 (fun x' => abs_int_le _ _ 1 hfb)]
  simp only [Kernel.comap_apply]

theorem obs_eq_nu {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (f : Y → ℝ) (hf : Measurable f) (hfb : ∀ y, |f y| ≤ 1) (z : ProbabilityMeasure X) (a : A) :
    ∫ y, f y ∂(obsLaw P Q z a : Measure Y) =
      ∫ q, (∫ y, f y ∂(Q q.swap)) ∂(nuM P z a : Measure (X × A)) := by
  rw [integral_nuM P z a (fun q => ∫ y, f y ∂(Q q.swap))
    ((hf.stronglyMeasurable.integral_kernel (κ := Q)).measurable.comp measurable_swap) 1
    (fun q => abs_int_le _ _ 1 hfb), integral_obsLaw P Q f hf hfb z a]
  rfl

theorem tendsto_nuM {X A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (hP : IsWeaklyContinuous (kernelPM P))
    (z : ProbabilityMeasure X) (a : A) (zs : ℕ → ProbabilityMeasure X) (as : ℕ → A)
    (hz : Tendsto zs atTop (𝓝 z)) (ha : Tendsto as atTop (𝓝 a)) :
    Tendsto (fun n => nuM P (zs n) (as n)) atTop (𝓝 (nuM P z a)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro h
  have hPc : Continuous (kernelPM P) :=
    continuous_iff_seqContinuous.2 (fun {ss} {s} hs => hP s ss hs)
  have hAug : Continuous (fun p : X × A => (kernelPM P p).prod (diracProba p.2)) :=
    ProbabilityMeasure.continuous_prod.comp (hPc.prodMk (continuous_diracProba.comp continuous_snd))
  have hk : Continuous (fun p : X × A => ∫ q, h q ∂(augK P p)) := by
    refine ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction h).comp
      hAug).congr (fun p => ?_)
    simp only [Function.comp_apply]
    rw [augK_apply]
    rfl
  have hb : ∀ q, |h q| ≤ ‖h‖ := fun q => by
    simpa [Real.norm_eq_abs] using h.norm_coe_le_norm q
  let K : X × A →ᵇ ℝ := bcfOf _ hk ‖h‖ (fun p => abs_int_le _ _ _ hb)
  have hm : Tendsto (fun n => (zs n).prod (diracProba (as n))) atTop
      (𝓝 (z.prod (diracProba a))) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
      (hz.prodMk_nhds ((continuous_diracProba.tendsto a).comp ha))
  have e : ∀ (w : ProbabilityMeasure X) (b : A),
      ∫ q, h q ∂(nuM P w b : Measure (X × A)) =
        ∫ p, K p ∂((w.prod (diracProba b) : ProbabilityMeasure (X × A)) : Measure (X × A)) := by
    intro w b
    show ∫ q, h q ∂(augK P ∘ₘ (w : Measure X).prod (Measure.dirac b)) = _
    rw [integral_bind_markov (augK P) _ h h.continuous.measurable ‖h‖ hb]
    rfl
  simp only [e]
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hm K

theorem equi_Q {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [MeasurableSpace X]
    [MeasurableSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [MeasurableSpace A]
    (Q : Kernel (A × X) Y) [IsMarkovKernel Q] (hQ : IsTVContinuous (kernelPM Q)) (p : X × A) :
    EquicontinuousAt (fun (i : {f : Y → ℝ // Measurable f ∧ ∀ t, |f t| ≤ 1}) (q : X × A) =>
      ∫ y, i.1 y ∂(Q q.swap)) p := by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨qs, hqs, hbad⟩ := Filter.frequently_iff_seq_forall.1 hcon
  have ht : Tendsto (fun n => (qs n).swap) atTop (𝓝 p.swap) :=
    (continuous_swap.tendsto p).comp hqs
  obtain ⟨N, hN⟩ := hQ p.swap (fun n => (qs n).swap) ht (ε / 2) (by positivity)
  push_neg at hbad
  obtain ⟨i, hi⟩ := hbad N
  have h1 := hN N le_rfl i.1 i.2.1 i.2.2
  change |∫ t, i.1 t ∂(Q (qs N).swap) - ∫ t, i.1 t ∂(Q p.swap)| ≤ ε / 2 at h1
  rw [Real.dist_eq, abs_sub_comm] at hi
  linarith

/-- CHILD 1 (corollary_5_4): `R'` is continuous in total variation. -/
theorem tv_obsLaw {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hP : IsWeaklyContinuous (kernelPM P)) (hQ : IsTVContinuous (kernelPM Q)) :
    IsTVContinuous (fun p : ProbabilityMeasure X × A => obsLaw P Q p.1 p.2) := by
  intro s ss hs ε hε
  let _ : PseudoMetricSpace (X × A) := TopologicalSpace.pseudoMetrizableSpacePseudoMetric (X × A)
  have hs1 : Tendsto (fun n => (ss n).1) atTop (𝓝 s.1) := (continuous_fst.tendsto s).comp hs
  have hs2 : Tendsto (fun n => (ss n).2) atTop (𝓝 s.2) := (continuous_snd.tendsto s).comp hs
  have hν := tendsto_nuM P hP s.1 s.2 _ _ hs1 hs2
  obtain ⟨N, hN⟩ := rr_core
    (fun (i : {f : Y → ℝ // Measurable f ∧ ∀ t, |f t| ≤ 1}) (q : X × A) => ∫ y, i.1 y ∂(Q q.swap))
    (equi_Q Q hQ) 1 (fun i q => abs_int_le _ _ 1 i.2.2) _ _ hν ε hε
  refine ⟨N, fun n hn f hf hfb => ?_⟩
  have h1 := hN n hn ⟨f, hf, hfb⟩
  rw [obs_eq_nu P Q f hf hfb, obs_eq_nu P Q f hf hfb]
  exact h1

/-! ### Child 4 groundwork: the filter disintegrates the joint law. -/

/-- The posterior `y ↦ H z a y` as a Markov kernel. -/
noncomputable def kH {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X)
    (hm : ∀ z a, Measurable (H z a)) (z : ProbabilityMeasure X) (a : A) : Kernel Y X :=
  ⟨fun y => (H z a y : Measure X), measurable_subtype_coe.comp (hm z a)⟩

theorem kH_isMarkov {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X)
    (hm : ∀ z a, Measurable (H z a)) (z : ProbabilityMeasure X) (a : A) :
    IsMarkovKernel (kH H hm z a) :=
  ⟨fun y => by show IsProbabilityMeasure (H z a y : Measure X); infer_instance⟩

attribute [local instance] kH_isMarkov

theorem joint_eq {X Y A : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X) (hH : IsFilter P Q H)
    (z : ProbabilityMeasure X) (a : A) :
    (jointLaw P Q z a : Measure (X × Y)) =
      (((obsLaw P Q z a : Measure Y) ⊗ₘ kH H hH.measurable z a).map Prod.swap) := by
  have key : ∀ s ∈ Set.image2 (· ×ˢ ·) {B : Set X | MeasurableSet B} {C : Set Y | MeasurableSet C},
      (jointLaw P Q z a : Measure (X × Y)) s =
        (((obsLaw P Q z a : Measure Y) ⊗ₘ kH H hH.measurable z a).map Prod.swap) s := by
    rintro _ ⟨B, hB, C, hC, rfl⟩
    rw [Measure.map_apply measurable_swap (hB.prod hC), Set.preimage_swap_prod,
      Measure.compProd_apply_prod hC hB, hH.disintegration z a B C hB hC]
    rfl
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod key ?_
  rw [← Set.univ_prod_univ]
  exact key _ ⟨_, MeasurableSet.univ, _, MeasurableSet.univ, rfl⟩

theorem integral_joint_H {X Y A : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X) (hH : IsFilter P Q H)
    (z : ProbabilityMeasure X) (a : A) (φ : X × Y → ℝ) (hφ : Measurable φ) (C : ℝ)
    (hC : ∀ p, |φ p| ≤ C) :
    ∫ p, φ p ∂(jointLaw P Q z a : Measure (X × Y)) =
      ∫ y, ∫ x, φ (x, y) ∂(H z a y : Measure X) ∂(obsLaw P Q z a : Measure Y) := by
  rw [joint_eq P Q H hH z a, integral_map measurable_swap.aemeasurable hφ.aestronglyMeasurable,
    Measure.integral_compProd (f := fun q : Y × X => φ q.swap)]
  · rfl
  · exact Integrable.of_bound (hφ.comp measurable_swap).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun q => by simpa [Real.norm_eq_abs] using hC q.swap)

theorem mul_bound_one {f g : ℝ} (hf : |f| ≤ 1) (hg : |g| ≤ 1) : |f * g| ≤ 1 := by
  rw [abs_mul]; exact mul_le_one₀ hf (abs_nonneg _) hg

theorem integral_joint_nu {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (f : X → ℝ) (hf : Measurable f) (hfb : ∀ x, |f x| ≤ 1)
    (g : Y → ℝ) (hg : Measurable g) (hgb : ∀ y, |g y| ≤ 1) (z : ProbabilityMeasure X) (a : A) :
    ∫ p, f p.1 * g p.2 ∂(jointLaw P Q z a : Measure (X × Y)) =
      ∫ q, f q.1 * (∫ y, g y ∂(Q q.swap)) ∂(nuM P z a : Measure (X × A)) := by
  have hGq : Measurable (fun q : X × A => ∫ y, g y ∂(Q q.swap)) :=
    (hg.stronglyMeasurable.integral_kernel (κ := Q)).measurable.comp measurable_swap
  have hG : Measurable (fun x' : X => f x' * ∫ y, g y ∂(Q (a, x'))) :=
    hf.mul ((hg.stronglyMeasurable.integral_kernel (κ := Q)).measurable.comp measurable_prodMk_left)
  rw [integral_nuM P z a (fun q => f q.1 * (∫ y, g y ∂(Q q.swap)))
    ((hf.comp measurable_fst).mul hGq) 1
    (fun q => mul_bound_one (hfb _) (abs_int_le _ _ 1 hgb))]
  show ∫ p, f p.1 * g p.2 ∂(((P.comap (fun x => (x, a)) measurable_prodMk_right) ∘ₘ (z : Measure X)) ⊗ₘ
      (Q.comap (fun x' => (a, x')) measurable_prodMk_left)) = _
  rw [Measure.integral_compProd (f := fun p : X × Y => f p.1 * g p.2)
    (Integrable.of_bound ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun p => by
        simpa [Real.norm_eq_abs] using mul_bound_one (hfb p.1) (hgb p.2)))]
  simp only [Kernel.comap_apply, integral_const_mul]
  rw [integral_bind_markov _ _ (fun x' => f x' * ∫ y, g y ∂(Q (a, x'))) hG 1
    (fun x' => mul_bound_one (hfb _) (abs_int_le _ _ 1 hgb))]
  simp only [Kernel.comap_apply]
  rfl

/-! ### Child 4 (PosteriorL1). -/

/-- The posterior integral `y ↦ ∫ f d(H z a y)`. -/
noncomputable def postF {X Y A : Type*} [MeasurableSpace X]
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X) (f : X → ℝ)
    (z : ProbabilityMeasure X) (a : A) (y : Y) : ℝ :=
  ∫ x, f x ∂(H z a y : Measure X)

theorem measurable_postF {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X)
    (hm : ∀ z a, Measurable (H z a)) (f : X → ℝ) (hf : Measurable f)
    (z : ProbabilityMeasure X) (a : A) : Measurable (postF H f z a) :=
  (hf.stronglyMeasurable.integral_kernel (κ := kH H hm z a)).measurable

theorem post_nu {X Y A : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [MeasurableSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X) (hH : IsFilter P Q H)
    (f : X → ℝ) (hf : Measurable f) (hfb : ∀ x, |f x| ≤ 1)
    (g : Y → ℝ) (hg : Measurable g) (hgb : ∀ y, |g y| ≤ 1) (z : ProbabilityMeasure X) (a : A) :
    ∫ y, postF H f z a y * g y ∂(obsLaw P Q z a : Measure Y) =
      ∫ q, f q.1 * (∫ y, g y ∂(Q q.swap)) ∂(nuM P z a : Measure (X × A)) := by
  rw [← integral_joint_nu P Q f hf hfb g hg hgb z a,
    integral_joint_H P Q H hH z a (fun p => f p.1 * g p.2)
      ((hf.comp measurable_fst).mul (hg.comp measurable_snd)) 1
      (fun p => mul_bound_one (hfb _) (hgb _))]
  simp only [postF, integral_mul_const]

theorem equi_fQ {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [MeasurableSpace X]
    [MeasurableSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [MeasurableSpace A]
    (Q : Kernel (A × X) Y) [IsMarkovKernel Q] (hQ : IsTVContinuous (kernelPM Q))
    (f : X → ℝ) (hfc : Continuous f) (hfb : ∀ x, |f x| ≤ 1) (p : X × A) :
    EquicontinuousAt (fun (i : {g : Y → ℝ // Measurable g ∧ ∀ t, |g t| ≤ 1}) (q : X × A) =>
      f q.1 * ∫ y, i.1 y ∂(Q q.swap)) p := by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have h1 := Metric.equicontinuousAt_iff_right.1 (equi_Q Q hQ p) (ε / 2) (by positivity)
  have h2 : ∀ᶠ q in 𝓝 p, dist (f p.1) (f q.1) < ε / 2 := by
    have := (hfc.comp continuous_fst).continuousAt (x := p)
    exact (Metric.tendsto_nhds.1 this (ε / 2) (by positivity)).mono fun q hq => by
      rw [dist_comm]; exact hq
  filter_upwards [h1, h2] with q hq1 hq2 i
  have hi : |(∫ y, i.1 y ∂(Q p.swap)) - ∫ y, i.1 y ∂(Q q.swap)| < ε / 2 := by
    have := hq1 i
    rwa [Real.dist_eq] at this
  rw [Real.dist_eq] at hq2 ⊢
  have hGq : |∫ y, i.1 y ∂(Q q.swap)| ≤ 1 := abs_int_le _ _ 1 i.2.2
  have hfp := hfb p.1
  have e : f p.1 * (∫ y, i.1 y ∂(Q p.swap)) - f q.1 * ∫ y, i.1 y ∂(Q q.swap) =
      (f p.1 - f q.1) * (∫ y, i.1 y ∂(Q q.swap)) +
        f p.1 * ((∫ y, i.1 y ∂(Q p.swap)) - ∫ y, i.1 y ∂(Q q.swap)) := by ring
  rw [e]
  calc _ ≤ |(f p.1 - f q.1) * (∫ y, i.1 y ∂(Q q.swap))| +
        |f p.1 * ((∫ y, i.1 y ∂(Q p.swap)) - ∫ y, i.1 y ∂(Q q.swap))| := abs_add_le _ _
    _ ≤ |f p.1 - f q.1| * 1 + 1 * |(∫ y, i.1 y ∂(Q p.swap)) - ∫ y, i.1 y ∂(Q q.swap)| := by
        rw [abs_mul, abs_mul]; gcongr
    _ < ε := by linarith

set_option maxHeartbeats 1000000 in
theorem post_core {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hP : IsWeaklyContinuous (kernelPM P)) (hQ : IsTVContinuous (kernelPM Q))
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X) (hH : IsFilter P Q H)
    (z : ProbabilityMeasure X) (a : A) (zs : ℕ → ProbabilityMeasure X) (as : ℕ → A)
    (hz : Tendsto zs atTop (𝓝 z)) (ha : Tendsto as atTop (𝓝 a))
    (f : X → ℝ) (hfc : Continuous f) (hfb : ∀ x, |f x| ≤ 1) :
    Tendsto (fun n => ∫ y, |postF H f (zs n) (as n) y - postF H f z a y|
      ∂(obsLaw P Q z a : Measure Y)) atTop (𝓝 0) := by
  have hmF := measurable_postF H hH.measurable f hfc.measurable
  have hbF : ∀ w b y, |postF H f w b y| ≤ 1 := fun w b y => abs_int_le _ _ 1 hfb
  have hint : ∀ (w : ProbabilityMeasure X) (b : A) (φ : Y → ℝ), Measurable φ →
      (∀ y, |φ y| ≤ 1) → Integrable φ (obsLaw P Q w b : Measure Y) := fun w b φ hφ hb =>
    Integrable.of_bound hφ.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hb y)
  have hTV := tv_obsLaw P Q hP hQ
  have hs : Tendsto (fun n => (zs n, as n)) atTop (𝓝 (z, a)) := hz.prodMk_nhds ha
  let _ : PseudoMetricSpace (X × A) := TopologicalSpace.pseudoMetrizableSpacePseudoMetric (X × A)
  have hν := tendsto_nuM P hP z a zs as hz ha
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N1, hN1⟩ := hTV (z, a) (fun n => (zs n, as n)) hs (ε / 3) (by positivity)
  obtain ⟨N2, hN2⟩ := rr_core
    (fun (i : {g : Y → ℝ // Measurable g ∧ ∀ t, |g t| ≤ 1}) (q : X × A) =>
      f q.1 * ∫ y, i.1 y ∂(Q q.swap)) (equi_fQ Q hQ f hfc hfb) 1
    (fun i q => mul_bound_one (hfb _) (abs_int_le _ _ 1 i.2.2)) _ _ hν (ε / 3) (by positivity)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  obtain ⟨g, hg_def⟩ : ∃ g : Y → ℝ, ∀ y,
      g y = if 0 ≤ postF H f (zs n) (as n) y - postF H f z a y then 1 else -1 :=
    ⟨fun y => if 0 ≤ postF H f (zs n) (as n) y - postF H f z a y then 1 else -1, fun y => rfl⟩
  have hg : Measurable g := by
    rw [funext hg_def]
    exact Measurable.ite (measurableSet_le measurable_const ((hmF _ _).sub (hmF _ _)))
      measurable_const measurable_const
  have hgb : ∀ y, |g y| ≤ 1 := fun y => by rw [hg_def]; split_ifs <;> norm_num
  have habs : ∀ y, |postF H f (zs n) (as n) y - postF H f z a y| =
      postF H f (zs n) (as n) y * g y - postF H f z a y * g y := fun y => by
    rw [hg_def]
    split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · rw [abs_of_neg (not_le.1 h)]; ring
  have e1 : ∫ y, |postF H f (zs n) (as n) y - postF H f z a y| ∂(obsLaw P Q z a : Measure Y) =
      ∫ y, postF H f (zs n) (as n) y * g y ∂(obsLaw P Q z a : Measure Y) -
        ∫ y, postF H f z a y * g y ∂(obsLaw P Q z a : Measure Y) := by
    rw [← integral_sub (hint z a (fun y => postF H f (zs n) (as n) y * g y) ((hmF _ _).mul hg)
        fun y => mul_bound_one (hbF _ _ _) (hgb y))
      (hint z a (fun y => postF H f z a y * g y) ((hmF _ _).mul hg)
        fun y => mul_bound_one (hbF _ _ _) (hgb y))]
    congr 1
    funext y
    exact habs y
  have t1 : |∫ y, postF H f (zs n) (as n) y * g y ∂(obsLaw P Q (zs n) (as n) : Measure Y) -
      ∫ y, postF H f (zs n) (as n) y * g y ∂(obsLaw P Q z a : Measure Y)| ≤ ε / 3 :=
    hN1 n (le_of_max_le_left hn) (fun y => postF H f (zs n) (as n) y * g y)
      ((hmF _ _).mul hg) (fun y => mul_bound_one (hbF _ _ _) (hgb y))
  have t2 : |∫ q, f q.1 * (∫ y, g y ∂(Q q.swap)) ∂(nuM P (zs n) (as n) : Measure (X × A)) -
      ∫ q, f q.1 * (∫ y, g y ∂(Q q.swap)) ∂(nuM P z a : Measure (X × A))| ≤ ε / 3 :=
    hN2 n (le_of_max_le_right hn) ⟨g, hg, hgb⟩
  have p1 := post_nu P Q H hH f hfc.measurable hfb g hg hgb (zs n) (as n)
  have p2 := post_nu P Q H hH f hfc.measurable hfb g hg hgb z a
  have hnn : 0 ≤ ∫ y, |postF H f (zs n) (as n) y - postF H f z a y| ∂(obsLaw P Q z a : Measure Y) :=
    integral_nonneg fun y => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn, e1]
  rw [abs_le] at t1 t2
  linarith [t1.1, t1.2, t2.1, t2.2]

/-- CHILD 4 (PosteriorL1) from TV continuity of `Q` and weak continuity of `P`. -/
theorem posteriorL1_of {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hP : IsWeaklyContinuous (kernelPM P)) (hQ : IsTVContinuous (kernelPM Q)) :
    PosteriorL1 P Q := by
  intro H hH z a zs as hz ha f
  set c : ℝ := ‖f‖ + 1 with hc_def
  have hc : 0 < c := by positivity
  let f' : X → ℝ := fun x => f x / c
  have hf'c : Continuous f' := f.continuous.div_const c
  have hf'b : ∀ x, |f' x| ≤ 1 := fun x => by
    have := f.norm_coe_le_norm x
    rw [Real.norm_eq_abs] at this
    show |f x / c| ≤ 1
    rw [abs_div, abs_of_pos hc, div_le_one hc]
    linarith
  have hT := post_core P Q hP hQ H hH z a zs as hz ha f' hf'c hf'b
  have key : ∀ μ : Measure X, ∫ x, f x ∂μ = c * ∫ x, f' x ∂μ := fun μ => by
    rw [← integral_const_mul]
    congr 1
    funext x
    show f x = c * (f x / c)
    field_simp
  have hmF := measurable_postF H hH.measurable f' hf'c.measurable
  have hlin : ∀ n, ∫⁻ y, ENNReal.ofReal |∫ x, f x ∂(H (zs n) (as n) y : Measure X) -
      ∫ x, f x ∂(H z a y : Measure X)| ∂(obsLaw P Q z a : Measure Y) =
      ENNReal.ofReal (c * ∫ y, |postF H f' (zs n) (as n) y - postF H f' z a y|
        ∂(obsLaw P Q z a : Measure Y)) := by
    intro n
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      funext y
      rw [key, key, ← mul_sub, abs_mul, abs_of_pos hc]
      rfl
    · refine Integrable.of_bound
        (measurable_const.mul ((hmF _ _).sub (hmF _ _)).abs).aestronglyMeasurable (c * 2)
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hc, abs_abs]
      have h1 : |postF H f' (zs n) (as n) y| ≤ 1 := abs_int_le _ _ 1 hf'b
      have h2 : |postF H f' z a y| ≤ 1 := abs_int_le _ _ 1 hf'b
      have h3 := abs_sub (postF H f' (zs n) (as n) y) (postF H f' z a y)
      gcongr
      linarith
    · exact Filter.Eventually.of_forall fun y => mul_nonneg hc.le (abs_nonneg _)
  simp only [hlin]
  rw [← ENNReal.ofReal_zero]
  have := hT.const_mul c
  rw [mul_zero] at this
  exact ENNReal.tendsto_ofReal this

end FeinbergPOMDP.WStar.Draft7bcc

open FeinbergPOMDP.WStar FeinbergPOMDP.WStar.Draft7bcc in
/-- Glue: the target from its children (taken as hypotheses here; the reduction uses theorems). -/
theorem glue_7bcc {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hTV : IsTVContinuous (fun p : ProbabilityMeasure X × A => obsLaw P Q p.1 p.2))
    (hH : AssumptionH P Q)
    (h35 : (IsSetwiseContinuous (fun p : ProbabilityMeasure X × A => obsLaw P Q p.1 p.2) ∧
            AssumptionH P Q) →
          ∀ H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X, IsFilter P Q H →
            BeliefTransitionWeaklyContinuous P Q H) :
    IsSetwiseContinuous (fun p : ProbabilityMeasure X × A => obsLaw P Q p.1 p.2) ∧
    AssumptionH P Q ∧
    ∀ H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X,
      IsFilter P Q H → BeliefTransitionWeaklyContinuous P Q H := by
  have p1 := setwise_of_tv _ hTV
  exact ⟨p1, hH, h35 ⟨p1, hH⟩⟩

open FeinbergPOMDP.WStar FeinbergPOMDP.WStar.Draft7bcc in
theorem solution {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    [StandardBorelSpace X] [Nonempty X]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hP : IsWeaklyContinuous (kernelPM P)) (hQ : IsTVContinuous (kernelPM Q)) :
    IsSetwiseContinuous (fun p : ProbabilityMeasure X × A => obsLaw P Q p.1 p.2) ∧
    AssumptionH P Q ∧
    ∀ H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X,
      IsFilter P Q H → BeliefTransitionWeaklyContinuous P Q H := by
  exact glue_7bcc P Q (tv_obsLaw P Q hP hQ)
    (assumptionH_of P Q (FeinbergPOMDP.WStar.filter_exists P Q) (posteriorL1_of P Q hP hQ)
      (countableDetermining_of X))
    (fun h H hH => FeinbergPOMDP.WStar.theorem_3_5 P Q (Or.inl h) H hH)
