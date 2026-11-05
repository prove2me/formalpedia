-- Prove2me | solution 1 for FeinbergPOMDP.WStar.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T18:22:52.456204+00:00
-- url     : https://prove2.me/submissions/c2e75ae1-9ccb-42af-94d2-37d5ba152e95

import Mathlib
import Definitions.Def_FeinbergPOMDP_WStar_Model
import Theorems.Thm_SchalAvg_AvgOpt_lemma_2_3_i
import Theorems.Thm_SchalAvg_AvgOpt_lemma_2_3_ii
import Theorems.Thm_FeinbergPOMDP_WStar_obsLaw_weaklyContinuous

open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter FeinbergPOMDP.WStar

/-- Two one-sided Fatou bounds give convergence of a bounded real sequence. -/
lemma fpw35_tendsto_of_fatou (b : ℕ → ℝ) (L M : ℝ) (hb : ∀ k, |b k| ≤ M) (hL : |L| ≤ M)
    (hplus : ENNReal.ofReal (M + L) ≤ liminf (fun k => ENNReal.ofReal (M + b k)) atTop)
    (hminus : ENNReal.ofReal (M - L) ≤ liminf (fun k => ENNReal.ofReal (M - b k)) atTop) :
    Tendsto b atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have lo : ∀ᶠ k in atTop, L - ε < b k := by
    by_cases h0 : M + L - ε < 0
    · exact Eventually.of_forall fun k => by
        have := (abs_le.1 (hb k)).1; linarith
    · push Not at h0
      have hlt : ENNReal.ofReal (M + L - ε) < ENNReal.ofReal (M + L) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      filter_upwards [eventually_lt_of_lt_liminf (hlt.trans_le hplus)] with k hk
      have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h0).1 hk
      linarith
  have hi : ∀ᶠ k in atTop, b k < L + ε := by
    by_cases h0 : M - L - ε < 0
    · exact Eventually.of_forall fun k => by
        have := (abs_le.1 (hb k)).2; linarith
    · push Not at h0
      have hlt : ENNReal.ofReal (M - L - ε) < ENNReal.ofReal (M - L) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
      filter_upwards [eventually_lt_of_lt_liminf (hlt.trans_le hminus)] with k hk
      have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h0).1 hk
      linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (lo.and hi)
  exact ⟨N, fun k hk => by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [(hN k hk).1, (hN k hk).2]⟩

/-- `∫⁻ ofReal (M + f) = ofReal (M + ∫ f)` for bounded measurable `f` and a probability measure. -/
lemma fpw35_lintegral_shift {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] (f : Y → ℝ) (hf : Measurable f) (M : ℝ) (hM : ∀ y, |f y| ≤ M) :
    ∫⁻ y, ENNReal.ofReal (M + f y) ∂μ = ENNReal.ofReal (M + ∫ y, f y ∂μ) := by
  have hint : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable M
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM y)
  have hi2 : Integrable (fun y => M + f y) μ := (integrable_const M).add hint
  rw [← ofReal_integral_eq_lintegral_ofReal hi2
    (Eventually.of_forall fun y => by
      have := (abs_le.1 (hM y)).1; simp only [Pi.zero_apply]; linarith)]
  rw [integral_add (integrable_const M) hint]
  simp

lemma fpw35_abs_integral_le {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] (f : Y → ℝ) (M : ℝ) (hM : ∀ y, |f y| ≤ M) :
    |∫ y, f y ∂μ| ≤ M := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := M)
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM y)
  simpa using this

/-- Dominated convergence for setwise converging probability measures (from Lemma 5.1(i)). -/
lemma fpw35_setwise_dct {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (μs : ℕ → Measure Y) [∀ k, IsProbabilityMeasure (μs k)]
    (hμ : ∀ B : Set Y, MeasurableSet B → Tendsto (fun k => μs k B) atTop (𝓝 (μ B)))
    (f : ℕ → Y → ℝ) (g : Y → ℝ) (hf : ∀ k, Measurable (f k)) (hg : Measurable g) (M : ℝ)
    (hfM : ∀ k y, |f k y| ≤ M) (hgM : ∀ y, |g y| ≤ M)
    (hconv : ∀ᵐ y ∂μ, Tendsto (fun k => f k y) atTop (𝓝 (g y))) :
    Tendsto (fun k => ∫ y, f k y ∂(μs k)) atTop (𝓝 (∫ y, g y ∂μ)) := by
  have hfM' : ∀ k y, |-f k y| ≤ M := fun k y => by rw [abs_neg]; exact hfM k y
  have hgM' : ∀ y, |-g y| ≤ M := fun y => by rw [abs_neg]; exact hgM y
  refine fpw35_tendsto_of_fatou _ _ M (fun k => fpw35_abs_integral_le _ _ M (hfM k))
    (fpw35_abs_integral_le _ _ M hgM) ?_ ?_
  · have F := SchalAvg.AvgOpt.lemma_2_3_i μ μs hμ (fun k y => ENNReal.ofReal (M + f k y))
      (fun k => ENNReal.measurable_ofReal.comp (measurable_const.add (hf k)))
    calc ENNReal.ofReal (M + ∫ y, g y ∂μ) = ∫⁻ y, ENNReal.ofReal (M + g y) ∂μ :=
          (fpw35_lintegral_shift μ g hg M hgM).symm
      _ = ∫⁻ y, liminf (fun k => ENNReal.ofReal (M + f k y)) atTop ∂μ :=
          lintegral_congr_ae (hconv.mono fun y hy =>
            (((ENNReal.continuous_ofReal.tendsto _).comp
              (tendsto_const_nhds.add hy)).liminf_eq).symm)
      _ ≤ _ := F
      _ = _ := by
          congr 1; funext k; exact fpw35_lintegral_shift _ (f k) (hf k) M (hfM k)
  · have F := SchalAvg.AvgOpt.lemma_2_3_i μ μs hμ (fun k y => ENNReal.ofReal (M + -f k y))
      (fun k => ENNReal.measurable_ofReal.comp (measurable_const.add (hf k).neg))
    calc ENNReal.ofReal (M - ∫ y, g y ∂μ) = ∫⁻ y, ENNReal.ofReal (M + -g y) ∂μ := by
          rw [fpw35_lintegral_shift μ (fun y => -g y) hg.neg M hgM', integral_neg, sub_eq_add_neg]
      _ = ∫⁻ y, liminf (fun k => ENNReal.ofReal (M + -f k y)) atTop ∂μ :=
          lintegral_congr_ae (hconv.mono fun y hy =>
            (((ENNReal.continuous_ofReal.tendsto _).comp
              (tendsto_const_nhds.add hy.neg)).liminf_eq).symm)
      _ ≤ _ := F
      _ = _ := by
          congr 1; funext k
          rw [fpw35_lintegral_shift _ (fun y => -f k y) (hf k).neg M (hfM' k), integral_neg,
            sub_eq_add_neg]

/-- Dominated convergence for weakly converging probability measures and continuously
converging integrands (from Lemma 5.1(ii)). -/
lemma fpw35_weak_dct {Y : Type*} [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : ProbabilityMeasure Y) (μs : ℕ → ProbabilityMeasure Y) (hμ : Tendsto μs atTop (𝓝 μ))
    (f : ℕ → Y → ℝ) (g : Y → ℝ) (hf : ∀ k, Measurable (f k)) (hg : Measurable g) (M : ℝ)
    (hfM : ∀ k y, |f k y| ≤ M) (hgM : ∀ y, |g y| ≤ M)
    (hcc : ∀ y, Tendsto (fun p : ℕ × Y => f p.1 p.2) (atTop ×ˢ 𝓝 y) (𝓝 (g y))) :
    Tendsto (fun k => ∫ y, f k y ∂(μs k : Measure Y)) atTop (𝓝 (∫ y, g y ∂(μ : Measure Y))) := by
  let _ : MetricSpace Y := TopologicalSpace.metrizableSpaceMetric Y
  have hfM' : ∀ k y, |-f k y| ≤ M := fun k y => by rw [abs_neg]; exact hfM k y
  have hgM' : ∀ y, |-g y| ≤ M := fun y => by rw [abs_neg]; exact hgM y
  refine fpw35_tendsto_of_fatou _ _ M (fun k => fpw35_abs_integral_le _ _ M (hfM k))
    (fpw35_abs_integral_le _ _ M hgM) ?_ ?_
  · have F := SchalAvg.AvgOpt.lemma_2_3_ii μ μs hμ (fun k y => ENNReal.ofReal (M + f k y))
      (fun k => ENNReal.measurable_ofReal.comp (measurable_const.add (hf k)))
    calc ENNReal.ofReal (M + ∫ y, g y ∂(μ : Measure Y))
        = ∫⁻ y, ENNReal.ofReal (M + g y) ∂(μ : Measure Y) :=
          (fpw35_lintegral_shift _ g hg M hgM).symm
      _ = ∫⁻ y, liminf (fun p : ℕ × Y => ENNReal.ofReal (M + f p.1 p.2)) (atTop ×ˢ 𝓝 y)
            ∂(μ : Measure Y) := by
          congr 1; funext y
          exact (((ENNReal.continuous_ofReal.tendsto _).comp
            (tendsto_const_nhds.add (hcc y))).liminf_eq).symm
      _ ≤ _ := F
      _ = _ := by
          congr 1; funext k; exact fpw35_lintegral_shift _ (f k) (hf k) M (hfM k)
  · have F := SchalAvg.AvgOpt.lemma_2_3_ii μ μs hμ (fun k y => ENNReal.ofReal (M + -f k y))
      (fun k => ENNReal.measurable_ofReal.comp (measurable_const.add (hf k).neg))
    calc ENNReal.ofReal (M - ∫ y, g y ∂(μ : Measure Y))
        = ∫⁻ y, ENNReal.ofReal (M + -g y) ∂(μ : Measure Y) := by
          rw [fpw35_lintegral_shift _ (fun y => -g y) hg.neg M hgM', integral_neg, sub_eq_add_neg]
      _ = ∫⁻ y, liminf (fun p : ℕ × Y => ENNReal.ofReal (M + -f p.1 p.2)) (atTop ×ˢ 𝓝 y)
            ∂(μ : Measure Y) := by
          congr 1; funext y
          exact (((ENNReal.continuous_ofReal.tendsto _).comp
            (tendsto_const_nhds.add (hcc y).neg)).liminf_eq).symm
      _ ≤ _ := F
      _ = _ := by
          congr 1; funext k
          rw [fpw35_lintegral_shift _ (fun y => -f k y) (hf k).neg M (hfM' k), integral_neg,
            sub_eq_add_neg]

section POMDP

variable {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]

/-- Borel measurability of `y ↦ H(z, a, y)` (from the joint Borel measurability of a filter). -/
lemma fpw35_meas_borel (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y)
    [IsMarkovKernel Q] (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X)
    (hH : IsFilter P Q H) (z : ProbabilityMeasure X) (a : A) :
    @Measurable Y (ProbabilityMeasure X) _ (borel (ProbabilityMeasure X)) (H z a) := by
  have h := hH.measurable_joint_borel
  have hm : @Measurable Y ((ProbabilityMeasure X × A) × Y) _
      (((borel (ProbabilityMeasure X)).prod (inferInstance : MeasurableSpace A)).prod
        (inferInstance : MeasurableSpace Y)) (fun y => ((z, a), y)) :=
    @measurable_prodMk_left _ _ ((borel (ProbabilityMeasure X)).prod
      (inferInstance : MeasurableSpace A)) _ (z, a)
  exact h.comp hm

/-- (3.5): integrals against `q(·|z,a)` are integrals of `g(H(z,a,y))` against `R′(dy|z,a)`. -/
lemma fpw35_integral_rep (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y)
    [IsMarkovKernel Q] (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X)
    (hH : IsFilter P Q H) (z : ProbabilityMeasure X) (a : A) (g : ProbabilityMeasure X →ᵇ ℝ) :
    ∫ p, g p ∂(beliefTransition P Q H z a) =
      ∫ y, g (H z a y) ∂(obsLaw P Q z a : Measure Y) := by
  let _ : MeasurableSpace (ProbabilityMeasure X) := borel _
  have : BorelSpace (ProbabilityMeasure X) := ⟨rfl⟩
  have hm : Measurable (H z a) := fpw35_meas_borel P Q H hH z a
  unfold beliefTransition
  rw [integral_map hm.aemeasurable g.continuous.aestronglyMeasurable]

/-- The posterior is `R′`-a.s. unique (p. 8; Bertsekas–Shreve Cor. 7.27.1). -/
lemma fpw35_filter_ae_unique (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y)
    [IsMarkovKernel Q] (H H₀ : ProbabilityMeasure X → A → Y → ProbabilityMeasure X)
    (hH : IsFilter P Q H) (hH₀ : IsFilter P Q H₀) (z : ProbabilityMeasure X) (a : A) :
    ∀ᵐ y ∂(obsLaw P Q z a : Measure Y), H z a y = H₀ z a y := by
  let κ : Kernel Y X := ⟨fun y => (H z a y : Measure X),
    measurable_subtype_coe.comp (hH.measurable z a)⟩
  let κ₀ : Kernel Y X := ⟨fun y => (H₀ z a y : Measure X),
    measurable_subtype_coe.comp (hH₀.measurable z a)⟩
  have : IsMarkovKernel κ := ⟨fun y => by exact (H z a y).prop⟩
  have : IsMarkovKernel κ₀ := ⟨fun y => by exact (H₀ z a y).prop⟩
  have heq : (obsLaw P Q z a : Measure Y) ⊗ₘ κ = (obsLaw P Q z a : Measure Y) ⊗ₘ κ₀ := by
    refine Measure.ext_prod fun {C B} hC hB => ?_
    rw [Measure.compProd_apply_prod hC hB, Measure.compProd_apply_prod hC hB]
    change ∫⁻ y in C, (H z a y : Measure X) B ∂(obsLaw P Q z a : Measure Y) =
      ∫⁻ y in C, (H₀ z a y : Measure X) B ∂(obsLaw P Q z a : Measure Y)
    rw [← hH.disintegration z a B C hB hC, hH₀.disintegration z a B C hB hC]
  filter_upwards [Kernel.ae_eq_of_compProd_eq heq] with y hy
  exact Subtype.ext hy

end POMDP

theorem solution {X Y A : Type*}
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A]
    (P : Kernel (X × A) X) [IsMarkovKernel P] (Q : Kernel (A × X) Y) [IsMarkovKernel Q]
    (hc : (IsSetwiseContinuous (fun p : ProbabilityMeasure X × A => obsLaw P Q p.1 p.2) ∧
            AssumptionH P Q) ∨
          (IsWeaklyContinuous (kernelPM P) ∧ IsWeaklyContinuous (kernelPM Q) ∧
            ∃ H₀ : ProbabilityMeasure X → A → Y → ProbabilityMeasure X, IsFilter P Q H₀ ∧
              IsWeaklyContinuous (fun p : ProbabilityMeasure X × A × Y => H₀ p.1 p.2.1 p.2.2)))
    (H : ProbabilityMeasure X → A → Y → ProbabilityMeasure X) (hH : IsFilter P Q H) :
    BeliefTransitionWeaklyContinuous P Q H := by
  intro z a zs as hz ha g
  have hgb : ∀ p, |g p| ≤ ‖g‖ := fun p => by
    simpa [Real.norm_eq_abs] using g.norm_coe_le_norm p
  have hgm : ∀ (H' : ProbabilityMeasure X → A → Y → ProbabilityMeasure X), IsFilter P Q H' →
      ∀ z a, Measurable (fun y => g (H' z a y)) := by
    intro H' hH' z a
    let _ : MeasurableSpace (ProbabilityMeasure X) := borel _
    have : BorelSpace (ProbabilityMeasure X) := ⟨rfl⟩
    exact g.continuous.measurable.comp (fpw35_meas_borel P Q H' hH' z a)
  obtain ⟨H₀, hH₀, hcase⟩ : ∃ H₀ : ProbabilityMeasure X → A → Y → ProbabilityMeasure X,
      IsFilter P Q H₀ ∧
      ((IsSetwiseContinuous (fun p : ProbabilityMeasure X × A => obsLaw P Q p.1 p.2) ∧
        ∀ (z : ProbabilityMeasure X) (a : A) (zs : ℕ → ProbabilityMeasure X) (as : ℕ → A),
          Tendsto zs atTop (𝓝 z) → Tendsto as atTop (𝓝 a) →
          ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ C : Set Y, MeasurableSet C ∧
            (obsLaw P Q z a : Measure Y) C = 1 ∧
            ∀ y ∈ C, Tendsto (fun k => H₀ (zs (φ k)) (as (φ k)) y) atTop (𝓝 (H₀ z a y))) ∨
       (IsWeaklyContinuous (kernelPM P) ∧ IsWeaklyContinuous (kernelPM Q) ∧
        IsWeaklyContinuous (fun p : ProbabilityMeasure X × A × Y => H₀ p.1 p.2.1 p.2.2))) := by
    rcases hc with ⟨hSW, H₀, hH₀, hconv⟩ | ⟨hPw, hQw, H₀, hH₀, hH₀c⟩
    · exact ⟨H₀, hH₀, Or.inl ⟨hSW, hconv⟩⟩
    · exact ⟨H₀, hH₀, Or.inr ⟨hPw, hQw, hH₀c⟩⟩
  have hrep : ∀ z a, ∫ p, g p ∂(beliefTransition P Q H z a) =
      ∫ y, g (H₀ z a y) ∂(obsLaw P Q z a : Measure Y) := by
    intro z a
    rw [fpw35_integral_rep P Q H hH z a g]
    exact integral_congr_ae ((fpw35_filter_ae_unique P Q H H₀ hH hH₀ z a).mono
      fun y hy => by simp only [hy])
  simp only [hrep]
  rcases hcase with ⟨hSW, hconv⟩ | ⟨hPw, hQw, hH₀c⟩
  · -- condition (i): a further subsequence along which `H₀` converges `R′`-a.s.
    apply tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨φ, hφ, C, hC, hC1, hCconv⟩ :=
      hconv z a (fun n => zs (ns n)) (fun n => as (ns n)) (hz.comp hns) (ha.comp hns)
    refine ⟨φ, ?_⟩
    have hpair : Tendsto (fun k => (zs (ns (φ k)), as (ns (φ k)))) atTop (𝓝 (z, a)) :=
      ((hz.comp hns).comp hφ.tendsto_atTop).prodMk_nhds ((ha.comp hns).comp hφ.tendsto_atTop)
    have hset := hSW (z, a) _ hpair
    have hCc : ∀ᵐ y ∂(obsLaw P Q z a : Measure Y), y ∈ C := by
      rw [ae_iff]
      have h0 : (obsLaw P Q z a : Measure Y) Cᶜ = 0 := by
        rw [measure_compl hC (measure_ne_top _ _), hC1]; simp
      exact h0
    exact fpw35_setwise_dct (obsLaw P Q z a : Measure Y)
      (fun k => (obsLaw P Q (zs (ns (φ k))) (as (ns (φ k))) : Measure Y))
      (fun B hB => hset B hB)
      (fun k y => g (H₀ (zs (ns (φ k))) (as (ns (φ k))) y)) (fun y => g (H₀ z a y))
      (fun k => hgm H₀ hH₀ (zs (ns (φ k))) (as (ns (φ k)))) (hgm H₀ hH₀ z a) ‖g‖
      (fun k y => hgb _) (fun y => hgb _)
      (hCc.mono fun y hy => (g.continuous.tendsto _).comp (hCconv y hy))
  · -- condition (ii): weak continuity of `R′` and continuous convergence of the integrands.
    have hW := obsLaw_weaklyContinuous P Q hPw hQw
    refine fpw35_weak_dct (obsLaw P Q z a) (fun n => obsLaw P Q (zs n) (as n))
      (hW (z, a) (fun n => (zs n, as n)) (hz.prodMk_nhds ha))
      (fun k y => g (H₀ (zs k) (as k) y)) (fun y => g (H₀ z a y))
      (fun k => hgm H₀ hH₀ (zs k) (as k)) (hgm H₀ hH₀ z a) ‖g‖ (fun k y => hgb _) (fun y => hgb _) ?_
    intro y
    refine (g.continuous.tendsto _).comp ?_
    rw [tendsto_iff_seq_tendsto]
    intro ps hps
    have h1 : Tendsto (fun k => (ps k).1) atTop atTop := tendsto_fst.comp hps
    have h2 : Tendsto (fun k => (ps k).2) atTop (𝓝 y) := tendsto_snd.comp hps
    exact hH₀c (z, a, y) (fun k => (zs (ps k).1, as (ps k).1, (ps k).2))
      ((hz.comp h1).prodMk_nhds ((ha.comp h1).prodMk_nhds h2))
