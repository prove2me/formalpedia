-- Prove2me | solution 1 for EkelandVP.Pontryagin.lemma_7_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:37:49.793929+00:00
-- url     : https://prove2.me/submissions/35783bbc-b826-45b1-8db2-d969ab22b663

import Mathlib
import Definitions.Def_EkelandVP_Pontryagin_ctrlDist

set_option autoImplicit false
open MeasureTheory Filter Topology EkelandVP.Pontryagin

section ekv
variable {K : Type*}

lemma ekv_fin (T : ℝ) (u₁ u₂ : ℝ → K) :
    volume (Set.Icc 0 T ∩ {t | u₁ t ≠ u₂ t}) ≠ ⊤ :=
  ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono Set.inter_subset_left)

lemma ekv_ofReal (T : ℝ) (u₁ u₂ : ℝ → K) :
    ENNReal.ofReal (ctrlDist T u₁ u₂) = volume (Set.Icc 0 T ∩ {t | u₁ t ≠ u₂ t}) := by
  unfold ctrlDist
  rw [ENNReal.ofReal_toReal (ekv_fin T u₁ u₂)]

lemma ekv_nonneg (T : ℝ) (u₁ u₂ : ℝ → K) : 0 ≤ ctrlDist T u₁ u₂ := ENNReal.toReal_nonneg

lemma ekv_tri (T : ℝ) (u₁ u₂ u₃ : ℝ → K) :
    ctrlDist T u₁ u₂ ≤ ctrlDist T u₁ u₃ + ctrlDist T u₃ u₂ := by
  unfold ctrlDist
  have hsub : Set.Icc 0 T ∩ {t | u₁ t ≠ u₂ t} ⊆
      (Set.Icc 0 T ∩ {t | u₁ t ≠ u₃ t}) ∪ (Set.Icc 0 T ∩ {t | u₃ t ≠ u₂ t}) := by
    intro t ⟨ht, h⟩
    by_cases h13 : u₁ t = u₃ t
    · right; exact ⟨ht, fun h32 => h (h13.trans h32)⟩
    · left; exact ⟨ht, h13⟩
  have h1 := (measure_mono (μ := volume) hsub).trans (measure_union_le _ _)
  have h2 : volume (Set.Icc 0 T ∩ {t | u₁ t ≠ u₃ t}) +
      volume (Set.Icc 0 T ∩ {t | u₃ t ≠ u₂ t}) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ekv_fin T _ _, ekv_fin T _ _⟩
  calc _ ≤ (volume (Set.Icc 0 T ∩ {t | u₁ t ≠ u₃ t}) +
      volume (Set.Icc 0 T ∩ {t | u₃ t ≠ u₂ t})).toReal := ENNReal.toReal_mono h2 h1
    _ = _ := ENNReal.toReal_add (ekv_fin T _ _) (ekv_fin T _ _)

lemma ekv_zero_iff (T : ℝ) (u₁ u₂ : ℝ → K) :
    ctrlDist T u₁ u₂ = 0 ↔ u₁ =ᵐ[volume.restrict (Set.Icc 0 T)] u₂ := by
  unfold ctrlDist
  rw [ENNReal.toReal_eq_zero_iff]
  simp only [ekv_fin T u₁ u₂, or_false]
  have : (u₁ =ᵐ[volume.restrict (Set.Icc 0 T)] u₂) ↔
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), u₁ t = u₂ t := Iff.rfl
  rw [this, ae_restrict_iff' measurableSet_Icc, ae_iff]
  have hset : {a | ¬ (a ∈ Set.Icc 0 T → u₁ a = u₂ a)} = Set.Icc 0 T ∩ {t | u₁ t ≠ u₂ t} := by
    ext t; simp [Set.mem_inter_iff, and_assoc]
  rw [hset]

end ekv

theorem solution {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K]
    (T : ℝ) (hT : 0 < T) :
    (∀ u₁ u₂ u₃ : ℝ → K, Measurable u₁ → Measurable u₂ → Measurable u₃ →
      ctrlDist T u₁ u₂ ≤ ctrlDist T u₁ u₃ + ctrlDist T u₃ u₂) ∧
    (∀ u₁ u₂ : ℝ → K, Measurable u₁ → Measurable u₂ →
      (ctrlDist T u₁ u₂ = 0 ↔ u₁ =ᵐ[volume.restrict (Set.Icc 0 T)] u₂)) ∧
    (∀ us : ℕ → ℝ → K, (∀ k, Measurable (us k)) →
      (∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N, ctrlDist T (us j) (us k) < η) →
      ∃ ubar : ℝ → K, Measurable ubar ∧
        Tendsto (fun k => ctrlDist T (us k) ubar) atTop (𝓝 0)) := by
  refine ⟨fun u₁ u₂ u₃ _ _ _ => ekv_tri T u₁ u₂ u₃, fun u₁ u₂ _ _ => ekv_zero_iff T u₁ u₂, ?_⟩
  intro us hmeas hCauchy
  haveI : Nonempty K := ⟨us 0 0⟩
  have hchoose : ∀ j : ℕ, ∃ N : ℕ, ∀ a ≥ N, ∀ b ≥ N,
      ctrlDist T (us a) (us b) < (1 / 2 : ℝ) ^ j := fun j => hCauchy _ (by positivity)
  choose N hN using hchoose
  set κ : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (j + 1), N i with hκ
  have hκN : ∀ j, N j ≤ κ j := fun j =>
    Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_self j))
  have hκmono : ∀ j, κ j ≤ κ (j + 1) := fun j => by
    simp only [hκ]
    rw [Finset.sum_range_succ _ (j + 1)]
    exact Nat.le_add_right _ _
  set v : ℕ → ℝ → K := fun j => us (κ j) with hv
  set μ : Measure ℝ := volume.restrict (Set.Icc 0 T) with hμ
  set E : ℕ → Set ℝ := fun j => {t | v j t ≠ v (j + 1) t} with hE
  have hμE : ∀ j, μ (E j) = ENNReal.ofReal (ctrlDist T (v j) (v (j + 1))) := by
    intro j
    rw [hμ, Measure.restrict_apply' measurableSet_Icc, ekv_ofReal, Set.inter_comm]
  have hEj : ∀ j, ctrlDist T (v j) (v (j + 1)) < (1 / 2 : ℝ) ^ j := fun j =>
    hN j _ (hκN j) _ ((hκN j).trans (hκmono j))
  have hsum : ∑' j, μ (E j) ≠ ⊤ := by
    have h1 : ∀ j, μ (E j) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := fun j => by
      rw [hμE]; exact ENNReal.ofReal_le_ofReal (hEj j).le
    have h2 : ∑' j, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
        (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top h2 (ENNReal.tsum_le_tsum h1)
  have hae : ∀ᵐ t ∂μ, ∀ᶠ j in atTop, t ∉ E j := ae_eventually_notMem hsum
  have hlim : ∀ᵐ t ∂μ, ∃ x, Tendsto (fun j => v j t) atTop (𝓝 x) := by
    filter_upwards [hae] with t ht
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 ht
    refine ⟨v N0 t, tendsto_atTop_of_eventually_const (i₀ := N0) fun j hj => ?_⟩
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih =>
      have := hN0 j hj
      simp only [hE, Set.mem_setOf_eq, not_not] at this
      rw [← this, ih]
  set g : ℝ → K := fun t => limUnder atTop (fun j => v j t) with hg
  have htend : ∀ᵐ t ∂μ, Tendsto (fun j => v j t) atTop (𝓝 (g t)) := by
    filter_upwards [hlim] with t ⟨x, hx⟩
    rw [hg]; simp only
    rw [hx.limUnder_eq]; exact hx
  have hgm : AEMeasurable g μ :=
    aemeasurable_of_tendsto_metrizable_ae' (fun j => (hmeas _).aemeasurable) htend
  refine ⟨hgm.mk g, hgm.measurable_mk, ?_⟩
  set ubar := hgm.mk g with hubar
  have htend' : ∀ᵐ t ∂μ, Tendsto (fun j => v j t) atTop (𝓝 (ubar t)) := by
    filter_upwards [htend, hgm.ae_eq_mk] with t h1 h2
    rwa [h2] at h1
  -- tail estimate
  have htail : ∀ J, μ {t | v J t ≠ ubar t} ≤ ∑' i, μ (E (i + J)) := by
    intro J
    calc μ {t | v J t ≠ ubar t} ≤ μ (⋃ i, E (i + J)) := by
          apply measure_mono_ae
          filter_upwards [htend'] with t ht hs
          by_contra hcon
          have hcon' : ∀ i, t ∉ E (i + J) := fun i hi => hcon (Set.mem_iUnion.2 ⟨i, hi⟩)
          have hconst : ∀ i, v (i + J) t = v J t := by
            intro i
            induction i with
            | zero => simp
            | succ i ih =>
              have := hcon' i
              simp only [hE, Set.mem_setOf_eq, not_not] at this
              rw [show i + 1 + J = (i + J) + 1 by ring, ← this, ih]
          have h1 : Tendsto (fun i => v (i + J) t) atTop (𝓝 (ubar t)) :=
            (tendsto_add_atTop_iff_nat J).2 ht
          have h2 : Tendsto (fun i => v (i + J) t) atTop (𝓝 (v J t)) := by
            exact tendsto_const_nhds.congr (fun i => (hconst i).symm)
          exact hs (tendsto_nhds_unique h2 h1)
      _ ≤ _ := measure_iUnion_le _
  have htail0 : Tendsto (fun J => ∑' i, μ (E (i + J))) atTop (𝓝 0) :=
    ENNReal.tendsto_sum_nat_add (fun i => μ (E i)) hsum
  have hb0 : Tendsto (fun J => μ {t | v J t ≠ ubar t}) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail0 (fun _ => by simp) htail
  rw [Metric.tendsto_atTop]
  intro η hη
  have hη2 : 0 < η / 2 := by positivity
  have hA : ∀ᶠ J in atTop, μ {t | v J t ≠ ubar t} < ENNReal.ofReal (η / 2) :=
    hb0.eventually (gt_mem_nhds (by simpa using hη2))
  have hB : ∀ᶠ J in atTop, (1 / 2 : ℝ) ^ J < η / 2 :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
      (gt_mem_nhds hη2)
  obtain ⟨J, hJA, hJB⟩ := (hA.and hB).exists
  refine ⟨N J, fun k hk => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (ekv_nonneg _ _ _)]
  have h1 : ctrlDist T (us k) (v J) < (1 / 2 : ℝ) ^ J := hN J k hk _ (hκN J)
  have h2 : ctrlDist T (v J) ubar < η / 2 := by
    have : μ {t | v J t ≠ ubar t} = ENNReal.ofReal (ctrlDist T (v J) ubar) := by
      rw [hμ, Measure.restrict_apply' measurableSet_Icc, ekv_ofReal, Set.inter_comm]
    rw [this] at hJA
    exact (ENNReal.ofReal_lt_ofReal_iff hη2).1 hJA
  have := ekv_tri T (us k) ubar (v J)
  linarith
