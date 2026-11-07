-- Prove2me | solution 1 for GenEmpLik.Consistency.example_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:27:23.865365+00:00
-- url     : https://prove2.me/submissions/94a06357-24c1-484c-babb-e9ef912832ad

import Mathlib
import Definitions.Def_GenEmpLik_Consistency_IsGlivenkoCantelli

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace GEL3Ex5

variable {E Ξ : Type*} [MetricSpace E] [MeasurableSpace Ξ]

/-- Upper bracket: supremum of `ψ(·, s)` over a countable dense set of `X ∩ B(x, r)`. -/
noncomputable def U {X : Set E} (D : Set X) (ψ : E → Ξ → ℝ) (Z : Ξ → ℝ) (x : E) (r : ℝ)
    (s : Ξ) : ℝ :=
  ⨆ d : D, if dist ((d : X) : E) x < r then ψ ((d : X) : E) s else -Z s

section
variable {X : Set E} (D : Set X) (ψ : E → Ξ → ℝ) (Z : Ξ → ℝ)

lemma term_le (hZ : ∀ x ∈ X, ∀ s, |ψ x s| ≤ Z s) (hZ0 : ∀ s, 0 ≤ Z s) (x : E) (r : ℝ) (s : Ξ)
    (d : D) : (if dist ((d : X) : E) x < r then ψ ((d : X) : E) s else -Z s) ≤ Z s := by
  split_ifs
  · exact (le_abs_self _).trans (hZ _ (d : X).2 s)
  · linarith [hZ0 s]

lemma term_ge (hZ : ∀ x ∈ X, ∀ s, |ψ x s| ≤ Z s) (hZ0 : ∀ s, 0 ≤ Z s) (x : E) (r : ℝ) (s : Ξ)
    (d : D) : -Z s ≤ (if dist ((d : X) : E) x < r then ψ ((d : X) : E) s else -Z s) := by
  split_ifs
  · exact (abs_le.1 (hZ _ (d : X).2 s)).1
  · exact le_rfl

lemma bdd (hZ : ∀ x ∈ X, ∀ s, |ψ x s| ≤ Z s) (hZ0 : ∀ s, 0 ≤ Z s) (x : E) (r : ℝ) (s : Ξ) :
    BddAbove (Set.range fun d : D =>
      if dist ((d : X) : E) x < r then ψ ((d : X) : E) s else -Z s) :=
  ⟨Z s, by rintro _ ⟨d, rfl⟩; exact term_le D ψ Z hZ hZ0 x r s d⟩

lemma U_abs [Nonempty D] (hZ : ∀ x ∈ X, ∀ s, |ψ x s| ≤ Z s) (hZ0 : ∀ s, 0 ≤ Z s) (x : E)
    (r : ℝ) (s : Ξ) : |U D ψ Z x r s| ≤ Z s := by
  rw [abs_le]; constructor
  · obtain ⟨d0⟩ := ‹Nonempty D›
    exact (term_ge D ψ Z hZ hZ0 x r s d0).trans (le_ciSup (bdd D ψ Z hZ hZ0 x r s) d0)
  · exact ciSup_le (term_le D ψ Z hZ hZ0 x r s)

lemma U_meas (hDc : D.Countable) (hψm : ∀ x ∈ X, Measurable (ψ x)) (hZm : Measurable Z)
    (x : E) (r : ℝ) : Measurable (U D ψ Z x r) := by
  haveI := hDc.to_subtype
  refine Measurable.iSup fun d => ?_
  by_cases h : dist ((d : X) : E) x < r
  · simp only [h, if_true]; exact hψm _ (d : X).2
  · simp only [h, if_false]; exact hZm.neg

lemma U_upper (hDd : Dense D) (hZ : ∀ x ∈ X, ∀ s, |ψ x s| ≤ Z s) (hZ0 : ∀ s, 0 ≤ Z s)
    (s : Ξ) (hgood : ContinuousOn (fun z => ψ z s) X) (x : E) (r : ℝ) (y : E) (hy : y ∈ X)
    (hyx : dist y x < r) : ψ y s ≤ U D ψ Z x r s := by
  by_contra hlt
  push_neg at hlt
  have hφ : Continuous (fun z : X => ψ (z : E) s) := hgood.restrict
  set O : Set X := {z | U D ψ Z x r s < ψ (z : E) s} ∩ {z | dist (z : E) x < r}
  have hO : IsOpen O := (isOpen_lt continuous_const hφ).inter
    (isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const)
  obtain ⟨d, ⟨hd1, hd2⟩, hdD⟩ := hDd.inter_open_nonempty O hO ⟨⟨y, hy⟩, hlt, hyx⟩
  have hd1' : U D ψ Z x r s < ψ ((d : X) : E) s := hd1
  have hd2' : dist ((d : X) : E) x < r := hd2
  have := le_ciSup (bdd D ψ Z hZ hZ0 x r s) ⟨d, hdD⟩
  rw [if_pos hd2'] at this
  exact absurd hd1' (not_lt.2 this)

lemma U_near [Nonempty D] (hZ : ∀ x ∈ X, ∀ s, |ψ x s| ≤ Z s) (hZ0 : ∀ s, 0 ≤ Z s) (s : Ξ)
    (hgood : ContinuousOn (fun z => ψ z s) X) (x : E) (hx : x ∈ X) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ r, r ≤ δ → U D ψ Z x r s ≤ ψ x s + ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.continuousWithinAt_iff.1 (hgood x hx) ε hε
  refine ⟨δ, hδ, fun r hr => ciSup_le fun d => ?_⟩
  split_ifs with hd
  · have := h (d : X).2 (lt_of_lt_of_le hd hr)
    rw [Real.dist_eq] at this
    linarith [(abs_lt.1 this).2]
  · linarith [(abs_le.1 (hZ x hx s)).1]

end

lemma slln_emp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Ξ) (hξm : ∀ i, Measurable (ξ i)) (hξind : iIndepFun ξ μ)
    (hξid : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ) (g : Ξ → ℝ) (hg : Measurable g)
    (hgi : Integrable g (μ.map (ξ 0))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => VarianceRegularization.Expansion.empMean
      (fun i : Fin n => g (ξ i ω))) atTop (𝓝 (∫ s, g s ∂(μ.map (ξ 0)))) := by
  have hint : Integrable (fun ω => g (ξ 0 ω)) μ :=
    (integrable_map_measure hgi.aestronglyMeasurable (hξm 0).aemeasurable).1 hgi
  have hS := strong_law_ae (fun i ω => g (ξ i ω)) hint
    (fun i j hij => (hξind.comp (fun _ s => g s) (fun _ => hg)).indepFun hij)
    (fun i => (hξid i).comp hg)
  rw [integral_map (hξm 0).aemeasurable hgi.aestronglyMeasurable]
  filter_upwards [hS] with ω hω
  refine hω.congr fun n => ?_
  simp only [VarianceRegularization.Expansion.empMean, smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => g (ξ i ω)) n]


lemma bracket_step {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} (ξ : ℕ → Ω → Ξ) (hξm : ∀ i, Measurable (ξ i)) (hξind : iIndepFun ξ μ)
    (hξid : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ)
    (X : Set (EuclideanSpace ℝ (Fin d))) (hX : IsCompact X) (hXne : X.Nonempty)
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (hℓm : ∀ x ∈ X, Measurable (ℓ x))
    (hcont : ∀ᵐ s ∂(μ.map (ξ 0)), ContinuousOn (fun x => ℓ x s) X)
    (Z : Ξ → ℝ) (hZm : Measurable Z) (hZ0 : ∀ s, 0 ≤ Z s)
    (hZ : ∀ x ∈ X, ∀ s, |ℓ x s| ≤ Z s) (hZint : Integrable Z (μ.map (ξ 0)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, (⨆ h ∈ (fun x => ℓ x) '' X, ENNReal.ofReal
      |VarianceRegularization.Expansion.empMean (fun i : Fin n => h (ξ i ω))
        - ∫ s, h s ∂(μ.map (ξ 0))|) ≤ ENNReal.ofReal (2 * ε) := by
  have : IsProbabilityMeasure (μ.map (ξ 0)) :=
    Measure.isProbabilityMeasure_map (hξm 0).aemeasurable
  have : Nonempty X := hXne.to_subtype
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  have : Nonempty D := (hDd.nonempty).to_subtype
  set nℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ := fun z s => -ℓ z s with hnℓ
  have hnZ : ∀ x ∈ X, ∀ s, |nℓ x s| ≤ Z s := fun x hx s => by
    simp only [hnℓ, abs_neg]; exact hZ x hx s
  have hnm : ∀ x ∈ X, Measurable (nℓ x) := fun x hx => (hℓm x hx).neg
  have hUint : ∀ ψ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ, (∀ x ∈ X, ∀ s, |ψ x s| ≤ Z s) →
      (∀ x ∈ X, Measurable (ψ x)) → ∀ x r, Integrable (U D ψ Z x r) (μ.map (ξ 0)) :=
    fun ψ hb hm x r => Integrable.mono' hZint (U_meas D ψ Z hDc hm hZm x r).aestronglyMeasurable
      (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact U_abs D ψ Z hb hZ0 x r s)
  have hℓint : ∀ y ∈ X, Integrable (ℓ y) (μ.map (ξ 0)) := fun y hy =>
    Integrable.mono' hZint (hℓm y hy).aestronglyMeasurable
      (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact hZ y hy s)
  have hrad : ∀ x : X, ∃ r > 0,
      ∫ s, (U D ℓ Z x r s + U D nℓ Z x r s) ∂(μ.map (ξ 0)) < ε := by
    intro x
    have hlim : Tendsto (fun k : ℕ => ∫ s, (U D ℓ Z x (1 / ((k : ℝ) + 1)) s
        + U D nℓ Z x (1 / ((k : ℝ) + 1)) s) ∂(μ.map (ξ 0))) atTop
        (𝓝 (∫ _s, (0 : ℝ) ∂(μ.map (ξ 0)))) := by
      refine tendsto_integral_of_dominated_convergence (fun s => 2 * Z s)
        (fun k => ((U_meas D ℓ Z hDc hℓm hZm _ _).add
          (U_meas D nℓ Z hDc hnm hZm _ _)).aestronglyMeasurable)
        (hZint.const_mul 2) (fun k => ae_of_all _ fun s => ?_) ?_
      · rw [Real.norm_eq_abs]
        have h1 := abs_le.1 (U_abs D ℓ Z hZ hZ0 x (1 / ((k : ℝ) + 1)) s)
        have h2 := abs_le.1 (U_abs D nℓ Z hnZ hZ0 x (1 / ((k : ℝ) + 1)) s)
        rw [abs_le]; constructor <;> linarith
      · filter_upwards [hcont] with s hs
        rw [Metric.tendsto_atTop]
        intro e he
        obtain ⟨δ1, hδ1, h1⟩ := U_near D ℓ Z hZ hZ0 s hs x x.2 (e / 4) (by positivity)
        obtain ⟨δ2, hδ2, h2⟩ := U_near D nℓ Z hnZ hZ0 s hs.neg x x.2 (e / 4) (by positivity)
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt (lt_min hδ1 hδ2)
        refine ⟨N, fun k hk => ?_⟩
        have hrk : 1 / ((k : ℝ) + 1) ≤ min δ1 δ2 := (Nat.one_div_le_one_div hk).trans hN.le
        have a1 := h1 _ (hrk.trans (min_le_left _ _))
        have a2 := h2 _ (hrk.trans (min_le_right _ _))
        have hpos : dist (x : EuclideanSpace ℝ (Fin d)) x < 1 / ((k : ℝ) + 1) := by
          rw [dist_self]; positivity
        have b1 := U_upper D ℓ Z hDd hZ hZ0 s hs x (1 / ((k : ℝ) + 1)) x x.2 hpos
        have b2 := U_upper D nℓ Z hDd hnZ hZ0 s hs.neg x (1 / ((k : ℝ) + 1)) x x.2 hpos
        simp only [hnℓ] at a2 b2
        rw [Real.dist_eq, sub_zero, abs_lt]; constructor <;> linarith
    rw [integral_zero] at hlim
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 ε hε)
    exact ⟨1 / ((N : ℝ) + 1), by positivity, hN N le_rfl⟩
  choose r hr0 hrint using hrad
  obtain ⟨t, ht⟩ := hX.elim_finite_subcover (fun x : X => Metric.ball (x : EuclideanSpace ℝ (Fin d)) (r x))
    (fun _ => Metric.isOpen_ball)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball_self (hr0 _)⟩)
  have hgoodω : ∀ᵐ ω ∂μ, ∀ i, ContinuousOn (fun z => ℓ z (ξ i ω)) X :=
    ae_all_iff.2 fun i => ae_of_ae_map (hξm i).aemeasurable (by rw [(hξid i).map_eq]; exact hcont)
  have hSu : ∀ᵐ ω ∂μ, ∀ j ∈ t, Tendsto (fun n : ℕ => VarianceRegularization.Expansion.empMean
      (fun i : Fin n => U D ℓ Z j (r j) (ξ i ω))) atTop
      (𝓝 (∫ s, U D ℓ Z j (r j) s ∂(μ.map (ξ 0)))) :=
    (eventually_all_finset t).2 fun j _ => slln_emp ξ hξm hξind hξid _
      (U_meas D ℓ Z hDc hℓm hZm _ _) (hUint ℓ hZ hℓm _ _)
  have hSl : ∀ᵐ ω ∂μ, ∀ j ∈ t, Tendsto (fun n : ℕ => VarianceRegularization.Expansion.empMean
      (fun i : Fin n => U D nℓ Z j (r j) (ξ i ω))) atTop
      (𝓝 (∫ s, U D nℓ Z j (r j) s ∂(μ.map (ξ 0)))) :=
    (eventually_all_finset t).2 fun j _ => slln_emp ξ hξm hξind hξid _
      (U_meas D nℓ Z hDc hnm hZm _ _) (hUint nℓ hnZ hnm _ _)
  filter_upwards [hgoodω, hSu, hSl] with ω hg hu hl
  have hev : ∀ᶠ n in atTop, ∀ j ∈ t,
      |VarianceRegularization.Expansion.empMean (fun i : Fin n => U D ℓ Z j (r j) (ξ i ω))
        - ∫ s, U D ℓ Z j (r j) s ∂(μ.map (ξ 0))| < ε ∧
      |VarianceRegularization.Expansion.empMean (fun i : Fin n => U D nℓ Z j (r j) (ξ i ω))
        - ∫ s, U D nℓ Z j (r j) s ∂(μ.map (ξ 0))| < ε :=
    (eventually_all_finset t).2 fun j hj =>
      ((Metric.tendsto_nhds.1 (hu j hj) ε hε).and (Metric.tendsto_nhds.1 (hl j hj) ε hε)).mono
        fun n hn => ⟨by rw [← Real.dist_eq]; exact hn.1, by rw [← Real.dist_eq]; exact hn.2⟩
  filter_upwards [hev] with n hn
  refine iSup₂_le ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨j, hj, hyj⟩ : ∃ j ∈ t, y ∈ Metric.ball (j : EuclideanSpace ℝ (Fin d)) (r j) := by
    have := ht hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨j, hj, h⟩ := this
    exact ⟨j, hj, h⟩
  rw [Metric.mem_ball] at hyj
  obtain ⟨hnu, hnl⟩ := hn j hj
  -- sample bounds
  have hs1 : VarianceRegularization.Expansion.empMean (fun i : Fin n => ℓ y (ξ i ω)) ≤
      VarianceRegularization.Expansion.empMean (fun i : Fin n => U D ℓ Z j (r j) (ξ i ω)) := by
    unfold VarianceRegularization.Expansion.empMean
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
      U_upper D ℓ Z hDd hZ hZ0 _ (hg i) j (r j) y hy hyj) (by positivity)
  have hs2 : -VarianceRegularization.Expansion.empMean (fun i : Fin n => U D nℓ Z j (r j) (ξ i ω))
      ≤ VarianceRegularization.Expansion.empMean (fun i : Fin n => ℓ y (ξ i ω)) := by
    unfold VarianceRegularization.Expansion.empMean
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
    have := U_upper D nℓ Z hDd hnZ hZ0 _ (hg i).neg j (r j) y hy hyj
    simp only [hnℓ] at this ⊢; linarith
  have hp1 : ∫ s, ℓ y s ∂(μ.map (ξ 0)) ≤ ∫ s, U D ℓ Z j (r j) s ∂(μ.map (ξ 0)) :=
    integral_mono_ae (hℓint y hy) (hUint ℓ hZ hℓm _ _) (by
      filter_upwards [hcont] with s hs
      exact U_upper D ℓ Z hDd hZ hZ0 s hs j (r j) y hy hyj)
  have hp2 : -∫ s, U D nℓ Z j (r j) s ∂(μ.map (ξ 0)) ≤ ∫ s, ℓ y s ∂(μ.map (ξ 0)) := by
    rw [← integral_neg]
    exact integral_mono_ae (hUint nℓ hnZ hnm _ _).neg (hℓint y hy) (by
      filter_upwards [hcont] with s hs
      have := U_upper D nℓ Z hDd hnZ hZ0 s hs.neg j (r j) y hy hyj
      simp only [hnℓ] at this ⊢; linarith)
  have hsum : ∫ s, U D ℓ Z j (r j) s ∂(μ.map (ξ 0)) + ∫ s, U D nℓ Z j (r j) s ∂(μ.map (ξ 0))
      < ε := by
    rw [← integral_add (hUint ℓ hZ hℓm _ _) (hUint nℓ hnZ hnm _ _)]; exact hrint j
  have h1 := abs_lt.1 hnu
  have h2 := abs_lt.1 hnl
  apply ENNReal.ofReal_le_ofReal
  rw [abs_le]; constructor <;> linarith

end GEL3Ex5

open GEL3Ex5 in
theorem solution {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {d : ℕ}
    (ξ : ℕ → Ω → Ξ) (hξm : ∀ i, Measurable (ξ i)) (hξind : iIndepFun ξ μ)
    (hξid : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ)
    (X : Set (EuclideanSpace ℝ (Fin d))) (hX : IsCompact X)
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (hℓm : ∀ x ∈ X, Measurable (ℓ x))
    (hcont : ∀ᵐ s ∂(μ.map (ξ 0)), ContinuousOn (fun x => ℓ x s) X)
    (Z : Ξ → ℝ) (hZm : Measurable Z) (hZ0 : ∀ s, 0 ≤ Z s)
    (hZ : ∀ x ∈ X, ∀ s, |ℓ x s| ≤ Z s) (hZint : Integrable Z (μ.map (ξ 0))) :
    GenEmpLik.Consistency.IsGlivenkoCantelli μ ξ ((fun x => ℓ x) '' X) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Integrable.mono' hZint (hℓm x hx).aestronglyMeasurable
      (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact hZ x hx s)
  rcases X.eq_empty_or_nonempty with hXe | hXne
  · refine ae_of_all _ fun ω => ?_
    simp [hXe]
  have hall := ae_all_iff.2 fun k : ℕ => bracket_step ξ hξm hξind hξid X hX hXne ℓ hℓm hcont
    Z hZm hZ0 hZ hZint (1 / ((k : ℝ) + 1)) (by positivity)
  filter_upwards [hall] with ω hω
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  by_cases htop : e = ⊤
  · exact Eventually.of_forall fun _ => htop ▸ le_top
  have he' : 0 < e.toReal := ENNReal.toReal_pos he.ne' htop
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos he')
  have hle : ENNReal.ofReal (2 * (1 / ((k : ℝ) + 1))) ≤ e := by
    rw [ENNReal.ofReal_le_iff_le_toReal htop]; linarith
  exact (hω k).mono fun n hn => hn.trans hle
