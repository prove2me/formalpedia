-- Prove2me | solution 1 for GenEmpLik.Consistency.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:09:53.350065+00:00
-- url     : https://prove2.me/submissions/ec9a1292-3d46-47d4-aa63-f6a85c90312b

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_AssumptionA
import Definitions.Def_GenEmpLik_Consistency_AssumptionE
import Definitions.Def_GenEmpLik_Expansion_robustMean
import Definitions.Def_GenEmpLik_Consistency_argminSet
import Definitions.Def_GenEmpLik_Consistency_inclDist
import Theorems.Thm_GenEmpLik_Consistency_theorem_7
import Theorems.Thm_GenEmpLik_Consistency_example_5

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace GEL3Aux

lemma wsum_le_norm {n : ℕ} (p w : Fin n → ℝ) (hp0 : 0 ≤ p) (hp1 : ∑ i, p i = 1) :
    ∑ i, p i * w i ≤ ‖w‖ := by
  calc ∑ i, p i * w i ≤ ∑ i, p i * ‖w‖ := by
        apply Finset.sum_le_sum; intro i _
        apply mul_le_mul_of_nonneg_left _ (hp0 i)
        exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm w i)
    _ = ‖w‖ := by rw [← Finset.sum_mul, hp1, one_mul]

lemma bdd_image {n : ℕ} (f : ℝ → EReal) (ρ : ℝ) (z : Fin n → ℝ) :
    BddAbove ((fun p : Fin n → ℝ => ∑ i, p i * z i) ''
      PhiDivRobust.Counterpart.probUncertaintySet f (fun _ => (1 : ℝ) / n) (ρ / n)) := by
  refine ⟨‖z‖, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact wsum_le_norm p z hp.1 hp.2.1

lemma uniform_mem {n : ℕ} (hn : 0 < n) (f : ℝ → EReal) (hf1 : f 1 = 0) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (fun _ : Fin n => (1 : ℝ) / n) ∈
      PhiDivRobust.Counterpart.probUncertaintySet f (fun _ => (1 : ℝ) / n) (ρ / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨fun i => by positivity, ?_, ?_⟩
  · simp [Finset.sum_const, Finset.card_univ]; field_simp
  · unfold PhiDivRobust.Counterpart.phiDiv
    have : ((1 : ℝ) / n) / ((1 : ℝ) / n) = 1 := div_self (by positivity)
    simp only [this, hf1, mul_zero, Finset.sum_const_zero]
    exact_mod_cast (by positivity : (0 : ℝ) ≤ ρ / n)

lemma robustMean_le {n : ℕ} (f : ℝ → EReal) (ρ : ℝ) (z z' : Fin n → ℝ) :
    GenEmpLik.Expansion.robustMean f ρ z ≤ GenEmpLik.Expansion.robustMean f ρ z' + dist z z' := by
  unfold GenEmpLik.Expansion.robustMean
  set S := PhiDivRobust.Counterpart.probUncertaintySet f (fun _ : Fin n => (1 : ℝ) / n) (ρ / n)
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h, dist_nonneg]
  · apply csSup_le (h.image _)
    rintro _ ⟨p, hp, rfl⟩
    have h1 : ∑ i, p i * z' i ≤ sSup ((fun p : Fin n → ℝ => ∑ i, p i * z' i) '' S) :=
      le_csSup (bdd_image f ρ z') ⟨p, hp, rfl⟩
    have h2 := wsum_le_norm p (z - z') hp.1 hp.2.1
    rw [dist_eq_norm]
    have h3 : ∑ i, p i * (z - z') i = ∑ i, p i * z i - ∑ i, p i * z' i := by
      rw [← Finset.sum_sub_distrib]; congr 1; ext i; simp [mul_sub]
    linarith

lemma robustMean_continuous {n : ℕ} (f : ℝ → EReal) (ρ : ℝ) :
    Continuous (fun z : Fin n → ℝ => GenEmpLik.Expansion.robustMean f ρ z) :=
  (LipschitzWith.of_le_add (fun z z' => robustMean_le f ρ z z')).continuous

lemma sSup_abs_le {A : Set ℝ} (hne : A.Nonempty) (hbdd : BddAbove A) (c : ℝ) :
    ENNReal.ofReal |sSup A - c| ≤ ⨆ a ∈ A, ENNReal.ofReal |a - c| := by
  set T := ⨆ a ∈ A, ENNReal.ofReal |a - c|
  by_cases hT : T = ⊤
  · rw [hT]; exact le_top
  have ha : ∀ a ∈ A, |a - c| ≤ T.toReal := fun a haA =>
    (ENNReal.ofReal_le_iff_le_toReal hT).1 (le_iSup₂ (f := fun a _ => ENNReal.ofReal |a - c|) a haA)
  have : |sSup A - c| ≤ T.toReal := by
    rw [abs_le]; constructor
    · obtain ⟨a, haA⟩ := hne
      have := le_csSup hbdd haA
      have := (abs_le.1 (ha a haA)).1
      linarith
    · have : sSup A ≤ c + T.toReal := csSup_le hne (fun a haA => by
        have := (abs_le.1 (ha a haA)).2; linarith)
      linarith
  calc ENNReal.ofReal |sSup A - c| ≤ ENNReal.ofReal T.toReal := ENNReal.ofReal_le_ofReal this
    _ = T := ENNReal.ofReal_toReal hT

lemma tendsto_measure_of_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (G : ℕ → Ω → ℝ≥0∞) (hG : ∀ n, Measurable (G n))
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => G n ω) atTop (𝓝 0)) (ε : ℝ≥0∞) (hε : 0 < ε) :
    Tendsto (fun n => μ {ω | ε ≤ G n ω}) atTop (𝓝 0) := by
  set B : ℕ → Set Ω := fun N => ⋃ n ≥ N, {ω | ε ≤ G n ω}
  have hBm : ∀ N, MeasurableSet (B N) := fun N =>
    MeasurableSet.biUnion (Set.to_countable _) (fun n _ => measurableSet_le measurable_const (hG n))
  have hanti : Antitone B := by
    intro N M hNM ω hω
    simp only [B, Set.mem_iUnion] at hω ⊢
    obtain ⟨n, hn, h⟩ := hω
    exact ⟨n, le_trans hNM hn, h⟩
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (fun N => (hBm N).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have hzero : μ (⋂ N, B N) = 0 := by
    apply measure_mono_null _ (ae_iff.1 hae)
    intro ω hω
    intro ht
    have hev := (tendsto_order.1 ht).2 ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    have := Set.mem_iInter.1 hω N
    simp only [B, Set.mem_iUnion] at this
    obtain ⟨n, hn, h⟩ := this
    exact absurd h (not_le.2 (hN n hn))
  rw [hzero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) ?_
  intro N
  apply measure_mono
  intro ω hω
  simp only [B, Set.mem_iUnion]
  exact ⟨N, le_rfl, hω⟩


lemma det1 {ι : Type*} [Nonempty ι] (R F : ι → ℝ) (t c : ℝ) (hF : ∀ x, |F x| ≤ c)
    (h : ∀ x, |R x - F x| ≤ t) : |(⨅ x, R x) - ⨅ x, F x| ≤ t := by
  have hFb : BddBelow (Set.range F) := ⟨-c, by
    rintro _ ⟨x, rfl⟩; have := abs_le.1 (hF x); linarith⟩
  have hRb : BddBelow (Set.range R) := ⟨-c - t, by
    rintro _ ⟨x, rfl⟩; have := abs_le.1 (hF x); have := abs_le.1 (h x); linarith⟩
  have h1 : (⨅ x, R x) - t ≤ ⨅ x, F x := le_ciInf fun x => by
    have := ciInf_le hRb x; have := abs_le.1 (h x); linarith
  have h2 : (⨅ x, F x) - t ≤ ⨅ x, R x := le_ciInf fun x => by
    have := ciInf_le hFb x; have := abs_le.1 (h x); linarith
  rw [abs_le]; constructor <;> linarith

lemma det2 {E : Type*} [MetricSpace E] (X : Set E) (hX : IsCompact X) (hXne : X.Nonempty)
    (F : E → ℝ) (hFc : ContinuousOn F X) (δ : ℝ) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ (R : E → ℝ) (t : ℝ), (∀ x ∈ X, |R x - F x| ≤ t) →
      ENNReal.ofReal δ < GenEmpLik.Consistency.inclDist
        (GenEmpLik.Consistency.argminSet X R) (GenEmpLik.Consistency.argminSet X F) → η ≤ t := by
  obtain ⟨x0, hx0X, hx0min⟩ := hX.exists_isMinOn hXne hFc
  set S := GenEmpLik.Consistency.argminSet X F
  set K := X ∩ {x | ENNReal.ofReal δ ≤ Metric.infEDist x S}
  by_cases hK : K.Nonempty
  · have hKc : IsCompact K :=
      hX.inter_right (isClosed_le continuous_const Metric.continuous_infEDist)
    obtain ⟨k0, hk0K, hk0min⟩ := hKc.exists_isMinOn hK (hFc.mono Set.inter_subset_left)
    have hgap : F x0 < F k0 := by
      by_contra hcon
      push_neg at hcon
      have hk0S : k0 ∈ S := ⟨hk0K.1, fun y hy => le_trans hcon (hx0min hy)⟩
      have := hk0K.2
      simp only [Set.mem_setOf_eq, Metric.infEDist_zero_of_mem hk0S] at this
      exact absurd this (not_le.2 (ENNReal.ofReal_pos.2 hδ))
    refine ⟨(F k0 - F x0) / 2, by linarith, fun R t hRt hlt => ?_⟩
    unfold GenEmpLik.Consistency.inclDist at hlt
    simp only [lt_iSup_iff] at hlt
    obtain ⟨x, hxSn, hx⟩ := hlt
    have hxK : x ∈ K := ⟨hxSn.1, hx.le⟩
    have h1 : F k0 ≤ F x := hk0min hxK
    have h2 : R x ≤ R x0 := hxSn.2 x0 hx0X
    have h3 := abs_le.1 (hRt x hxSn.1)
    have h4 := abs_le.1 (hRt x0 hx0X)
    linarith
  · refine ⟨1, one_pos, fun R t _ hlt => ?_⟩
    unfold GenEmpLik.Consistency.inclDist at hlt
    simp only [lt_iSup_iff] at hlt
    obtain ⟨x, hxSn, hx⟩ := hlt
    exact absurd ⟨x, hxSn.1, hx.le⟩ hK

end GEL3Aux

open GEL3Aux in
theorem solution {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MetricSpace Ξ]
    [SecondCountableTopology Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {d : ℕ}
    (f : ℝ → EReal) (hf : GenEmpLik.Coverage.AssumptionA f) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (ξ : ℕ → Ω → Ξ) (hξm : ∀ i, Measurable (ξ i)) (hξind : iIndepFun ξ μ)
    (hξid : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ)
    (X : Set (EuclideanSpace ℝ (Fin d))) (hX : IsCompact X) (hXne : X.Nonempty)
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ) (hℓm : ∀ x ∈ X, Measurable (ℓ x))
    (hℓlsc : LowerSemicontinuous (fun xs : X × Ξ => ℓ xs.1 xs.2))
    (hcont : ∀ s, ContinuousOn (fun x => ℓ x s) X)
    (hE : GenEmpLik.Consistency.AssumptionE (μ.map (ξ 0)) X ℓ) :
    (∀ δ : ℝ, 0 < δ → Tendsto (fun n : ℕ => μ {ω |
        δ < |(⨅ x : X, GenEmpLik.Expansion.robustMean f ρ (fun i : Fin n => ℓ x (ξ i ω)))
          - ⨅ x : X, ∫ s, ℓ x s ∂(μ.map (ξ 0))|}) atTop (𝓝 0)) ∧
    (∀ δ : ℝ, 0 < δ → Tendsto (fun n : ℕ => μ {ω |
        ENNReal.ofReal δ < GenEmpLik.Consistency.inclDist
          (GenEmpLik.Consistency.argminSet X
            (fun x => GenEmpLik.Expansion.robustMean f ρ (fun i : Fin n => ℓ x (ξ i ω))))
          (GenEmpLik.Consistency.argminSet X (fun x => ∫ s, ℓ x s ∂(μ.map (ξ 0))))}) atTop (𝓝 0)) := by
  classical
  haveI : IsProbabilityMeasure (μ.map (ξ 0)) := Measure.isProbabilityMeasure_map (hξm 0).aemeasurable
  obtain ⟨Z, hZm, hZ0, hZb, ε, hε, hZint⟩ := hE
  have hZi : Integrable Z (μ.map (ξ 0)) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hZint) hZm.aestronglyMeasurable
      (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hZ0 s)]
    rcases le_total (Z s) 1 with h | h
    · have := Real.rpow_nonneg (hZ0 s) (1 + ε); simp only [Pi.add_apply]; linarith
    · have : Z s ≤ Z s ^ (1 + ε) := Real.self_le_rpow_of_one_le h (by linarith)
      simp only [Pi.add_apply]; linarith
  have hFcont : ContinuousOn (fun x => ∫ s, ℓ x s ∂(μ.map (ξ 0))) X :=
    continuousOn_of_dominated (fun x hx => (hℓm x hx).aestronglyMeasurable)
      (fun x hx => ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact hZb x hx s) hZi
      (ae_of_all _ hcont)
  have hFb : ∀ x ∈ X, |∫ s, ℓ x s ∂(μ.map (ξ 0))| ≤ ∫ s, Z s ∂(μ.map (ξ 0)) := fun x hx => by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hZi (ae_of_all _ fun s => by
      rw [Real.norm_eq_abs]; exact hZb x hx s)
  have hGC := GenEmpLik.Consistency.example_5 ξ hξm hξind hξid X hX ℓ hℓm (ae_of_all _ hcont)
    Z hZm hZ0 hZb hZi
  have hT7 := GenEmpLik.Consistency.theorem_7 f hf ρ hρ ξ hξm hξind hξid X hXne hX.isClosed ℓ
    hℓlsc hℓm ⟨Z, hZm, hZ0, hZb, ε, hε, hZint⟩ hGC
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → Ω → ℝ≥0∞, G = fun n ω => ⨆ x ∈ D, ENNReal.ofReal
    |GenEmpLik.Expansion.robustMean f ρ (fun i : Fin n => ℓ (x : EuclideanSpace ℝ (Fin d)) (ξ i ω))
      - ∫ s, ℓ x s ∂(μ.map (ξ 0))| := ⟨_, rfl⟩
  have hGm : ∀ n, Measurable (G n) := fun n => hGdef ▸ Measurable.biSup D hDc (fun x _ =>
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      (((robustMean_continuous f ρ).measurable.comp
        (measurable_pi_lambda _ fun i => (hℓm x x.2).comp (hξm i))).sub_const _)))
  have hle : ∀ n ω, ∀ x ∈ X, ENNReal.ofReal
      |GenEmpLik.Expansion.robustMean f ρ (fun i : Fin n => ℓ x (ξ i ω))
        - ∫ s, ℓ x s ∂(μ.map (ξ 0))| ≤ G n ω := by
    intro n ω x hx
    have hgc : Continuous (fun y : X => ENNReal.ofReal
        |GenEmpLik.Expansion.robustMean f ρ (fun i : Fin n => ℓ (y : EuclideanSpace ℝ (Fin d)) (ξ i ω))
          - ∫ s, ℓ y s ∂(μ.map (ξ 0))|) := by
      refine ENNReal.continuous_ofReal.comp (continuous_abs.comp (Continuous.sub ?_ ?_))
      · exact (robustMean_continuous f ρ).comp (continuous_pi fun i =>
          (hcont (ξ i ω)).comp_continuous continuous_subtype_val Subtype.prop)
      · exact hFcont.comp_continuous continuous_subtype_val Subtype.prop
    have hcl := isClosed_le hgc (continuous_const (y := G n ω))
    have hsub : D ⊆ {y : X | ENNReal.ofReal
        |GenEmpLik.Expansion.robustMean f ρ (fun i : Fin n => ℓ (y : EuclideanSpace ℝ (Fin d)) (ξ i ω))
          - ∫ s, ℓ y s ∂(μ.map (ξ 0))| ≤ G n ω} := fun y hy => by
      rw [hGdef]
      exact le_iSup₂ (f := fun (y : X) (_ : y ∈ D) => ENNReal.ofReal
        |GenEmpLik.Expansion.robustMean f ρ (fun i : Fin n => ℓ (y : EuclideanSpace ℝ (Fin d)) (ξ i ω))
          - ∫ s, ℓ y s ∂(μ.map (ξ 0))|) y hy
    have := closure_minimal hsub hcl
    rw [hDd.closure_eq] at this
    have hmem := this (Set.mem_univ (⟨x, hx⟩ : X))
    exact hmem
  have hGH : ∀ n, 0 < n → ∀ ω, G n ω ≤ ⨆ x ∈ X,
      ⨆ p ∈ PhiDivRobust.Counterpart.probUncertaintySet f (fun _ : Fin n => (1 : ℝ) / n) (ρ / n),
        ENNReal.ofReal |∑ i, p i * ℓ x (ξ i ω) - ∫ s, ℓ x s ∂(μ.map (ξ 0))| := by
    intro n hn ω
    rw [hGdef]
    refine iSup₂_le fun x _ => ?_
    unfold GenEmpLik.Expansion.robustMean
    refine (sSup_abs_le ((Set.nonempty_of_mem (uniform_mem hn f hf.1.map_one ρ hρ)).image _)
      (bdd_image f ρ _) _).trans ?_
    rw [iSup_image]
    exact le_iSup₂ (f := fun (x : EuclideanSpace ℝ (Fin d)) (_ : x ∈ X) =>
      ⨆ p ∈ PhiDivRobust.Counterpart.probUncertaintySet f (fun _ : Fin n => (1 : ℝ) / n) (ρ / n),
        ENNReal.ofReal |∑ i, p i * ℓ x (ξ i ω) - ∫ s, ℓ x s ∂(μ.map (ξ 0))|) x.1 x.2
  have hGae : ∀ᵐ ω ∂μ, Tendsto (fun n => G n ω) atTop (𝓝 0) := hT7.mono fun ω hω =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hω
      (Eventually.of_forall fun _ => zero_le) (eventually_atTop.2 ⟨1, fun n hn => hGH n hn ω⟩)
  have key : ∀ a : ℝ, 0 < a → Tendsto (fun n => μ {ω | ENNReal.ofReal a ≤ G n ω}) atTop (𝓝 0) :=
    fun a ha => tendsto_measure_of_ae G hGm hGae _ (ENNReal.ofReal_pos.2 ha)
  have htoReal : ∀ n ω a, G n ω < ENNReal.ofReal a → ∀ x ∈ X,
      |GenEmpLik.Expansion.robustMean f ρ (fun i : Fin n => ℓ x (ξ i ω))
        - ∫ s, ℓ x s ∂(μ.map (ξ 0))| ≤ (G n ω).toReal := fun n ω a hlt x hx =>
    (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_lt hlt)).1 (hle n ω x hx)
  haveI := hXne.to_subtype
  constructor
  · intro δ hδ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (key δ hδ)
      (fun _ => zero_le) (fun n => measure_mono fun ω hω => ?_)
    simp only [Set.mem_setOf_eq] at hω ⊢
    by_contra hcon
    push_neg at hcon
    have ht := ENNReal.toReal_lt_of_lt_ofReal hcon
    have := det1 (fun x : X => GenEmpLik.Expansion.robustMean f ρ
        (fun i : Fin n => ℓ (x : EuclideanSpace ℝ (Fin d)) (ξ i ω)))
      (fun x : X => ∫ s, ℓ x s ∂(μ.map (ξ 0))) (G n ω).toReal _ (fun x => hFb x x.2)
      (fun x => htoReal n ω δ hcon x x.2)
    linarith
  · intro δ hδ
    obtain ⟨η, hη, hdet⟩ := det2 X hX hXne _ hFcont δ hδ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (key η hη)
      (fun _ => zero_le) (fun n => measure_mono fun ω hω => ?_)
    simp only [Set.mem_setOf_eq] at hω ⊢
    by_contra hcon
    push_neg at hcon
    have ht := ENNReal.toReal_lt_of_lt_ofReal hcon
    have := hdet _ _ (htoReal n ω η hcon) hω
    linarith
