-- Prove2me | solution 1 for DurrettProbability.series_converges_of_summable_variance
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T08:51:42.202515+00:00
-- url     : https://prove2.me/submissions/375014ea-da24-4342-a090-1f851e35f016

import Mathlib
import Definitions.Def_DurrettProbability_Series

open MeasureTheory ProbabilityTheory Filter


namespace DurrettProbability

/-- Partial sums read off the first `k` coordinates. -/
lemma km_psum {Ω : Type*} (X : ℕ → Ω → ℝ) (k j : ℕ) (hj : j ≤ k) (ω : Ω) :
    ∑ i : Finset.range k, (if (i : ℕ) < j then (1:ℝ) else 0) * X i ω = partialSum X j ω := by
  rw [Finset.sum_coe_sort (Finset.range k)
    (fun i => (if i < j then (1:ℝ) else 0) * X i ω)]
  have e : ∀ i, (if i < j then (1:ℝ) else 0) * X i ω = if i < j then X i ω else 0 := by
    intro i; split_ifs <;> simp
  simp_rw [e]
  rw [← Finset.sum_filter]
  have hf : (Finset.range k).filter (fun i => i < j) = Finset.range j := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hf]
  rfl

theorem km_main {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, μ[X i] = 0)
    (n : ℕ) (x : ℝ) (hx : 0 < x) :
    (μ {ω | ∃ k ∈ Finset.Icc 1 n, x ≤ |partialSum X k ω|}).toReal
      ≤ Var[partialSum X n; μ] / x ^ 2 := by
  classical
  have hSm : ∀ j, Measurable (partialSum X j) := fun j =>
    Finset.measurable_sum (Finset.range j) fun i _ => hmeas i
  have hint : ∀ i, Integrable (X i) μ := fun i => (hL2 i).integrable one_le_two
  have hSL2 : ∀ j, MemLp (partialSum X j) 2 μ := fun j =>
    memLp_finsetSum (Finset.range j) fun i _ => hL2 i
  set A : ℕ → Set Ω := fun k => {ω | x ≤ |partialSum X k ω|} ∩
    ⋂ j ∈ Finset.Ico 1 k, {ω | |partialSum X j ω| < x} with hA
  have hAm : ∀ k, MeasurableSet (A k) := by
    intro k
    refine (measurableSet_le measurable_const (hSm k).abs).inter ?_
    exact Finset.measurableSet_biInter _ fun j _ => measurableSet_lt (hSm j).abs measurable_const
  -- disjointness
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 n) : Set ℕ) A := by
    intro k hk k' hk' hne
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    simp only [Finset.coe_Icc, Set.mem_Icc] at hk hk'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h3 : |partialSum X k ω| < x := (Set.mem_iInter₂.mp h2.2) k (Finset.mem_Ico.mpr ⟨hk.1, hlt⟩)
      have h4 : x ≤ |partialSum X k ω| := h1.1
      linarith
    · have h3 : |partialSum X k' ω| < x := (Set.mem_iInter₂.mp h1.2) k' (Finset.mem_Ico.mpr ⟨hk'.1, hlt⟩)
      have h4 : x ≤ |partialSum X k' ω| := h2.1
      linarith
  -- the event is the disjoint union
  have hunion : {ω | ∃ k ∈ Finset.Icc 1 n, x ≤ |partialSum X k ω|} =
      ⋃ k ∈ Finset.Icc 1 n, A k := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk, hxk⟩
      have hex : ∃ m, m ∈ Finset.Icc 1 n ∧ x ≤ |partialSum X m ω| := ⟨k, hk, hxk⟩
      let m := Nat.find hex
      have hm := Nat.find_spec hex
      refine ⟨m, hm.1, hm.2, ?_⟩
      refine Set.mem_iInter₂.mpr fun j hj => ?_
      have hjm : j < m := (Finset.mem_Ico.mp hj).2
      have hmin := Nat.find_min hex hjm
      have hjI : j ∈ Finset.Icc 1 n := by
        have := Finset.mem_Icc.mp hm.1
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hj).1, by omega⟩
      simp only [Set.mem_setOf_eq]
      by_contra hc
      exact hmin ⟨hjI, not_lt.mp hc⟩
    · rintro ⟨k, hk, hAk⟩
      exact ⟨k, hk, hAk.1⟩
  -- the key estimate on each first-passage event
  have hkey : ∀ k ∈ Finset.Icc 1 n,
      x ^ 2 * μ.real (A k) ≤ ∫ ω in A k, partialSum X n ω ^ 2 ∂μ := by
    intro k hk
    have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
    set R : Ω → ℝ := fun ω => partialSum X n ω - partialSum X k ω with hR
    have hRL2 : MemLp R 2 μ := (hSL2 n).sub (hSL2 k)
    -- independence of the indicator part and the increment
    set U : Ω → (Finset.range k → ℝ) := fun ω i => X i ω with hU
    set V : Ω → (Finset.Ico k n → ℝ) := fun ω i => X i ω with hV
    have hUV : IndepFun U V μ :=
      hindep.indepFun_finset (Finset.range k) (Finset.Ico k n)
        (by rw [Finset.disjoint_left]; intro i h1 h2
            simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega) hmeas
    set psum : ℕ → (Finset.range k → ℝ) → ℝ := fun j u =>
      ∑ i : Finset.range k, (if (i : ℕ) < j then (1:ℝ) else 0) * u i with hpsum
    have hpm : ∀ j, Measurable (psum j) := by
      intro j
      exact Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
    set Cset : Set (Finset.range k → ℝ) := {u | x ≤ |psum k u|} ∩
      ⋂ j ∈ Finset.Ico 1 k, {u | |psum j u| < x} with hCset
    have hCm : MeasurableSet Cset :=
      (measurableSet_le measurable_const (hpm k).abs).inter
        (Finset.measurableSet_biInter _ fun j _ => measurableSet_lt (hpm j).abs measurable_const)
    set g : (Finset.range k → ℝ) → ℝ := Cset.indicator (psum k) with hg
    have hgm : Measurable g := (hpm k).indicator hCm
    set h : (Finset.Ico k n → ℝ) → ℝ := fun v => ∑ i : Finset.Ico k n, v i with hh
    have hhm : Measurable h := Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    have hYg : (A k).indicator (partialSum X k) = g ∘ U := by
      funext ω
      have hps : ∀ j, j ≤ k → psum j (U ω) = partialSum X j ω := fun j hj =>
        km_psum X k j hj ω
      have hmem : ω ∈ A k ↔ U ω ∈ Cset := by
        simp only [hA, hCset, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter]
        rw [hps k le_rfl]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun j hj => ?_⟩
          rw [hps j (Finset.mem_Ico.mp hj).2.le]; exact h2 j hj
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun j hj => ?_⟩
          have := h2 j hj
          rwa [hps j (Finset.mem_Ico.mp hj).2.le] at this
      simp only [Function.comp, hg, Set.indicator]
      by_cases hω : ω ∈ A k
      · rw [if_pos hω, if_pos (hmem.mp hω), hps k le_rfl]
      · rw [if_neg hω, if_neg (fun h' => hω (hmem.mpr h'))]
    have hRh : R = h ∘ V := by
      funext ω
      simp only [hR, Function.comp, hh, hV, partialSum]
      rw [Finset.sum_coe_sort (Finset.Ico k n) (fun i => X i ω), Finset.sum_Ico_eq_sub _ hkn]
    have hYR : IndepFun ((A k).indicator (partialSum X k)) R μ := by
      rw [hYg, hRh]; exact hUV.comp hgm hhm
    have hER : μ[R] = 0 := by
      have : R = fun ω => ∑ i ∈ Finset.Ico k n, X i ω := by
        funext ω; simp only [hR, partialSum]; rw [Finset.sum_Ico_eq_sub _ hkn]
      rw [this, integral_finset_sum _ fun i _ => hint i]
      exact Finset.sum_eq_zero fun i _ => hmean i
    have hYm : AEStronglyMeasurable ((A k).indicator (partialSum X k)) μ :=
      ((hSm k).indicator (hAm k)).aestronglyMeasurable
    have hRm : AEStronglyMeasurable R μ := ((hSm n).sub (hSm k)).aestronglyMeasurable
    have hcross : ∫ ω in A k, partialSum X k ω * R ω ∂μ = 0 := by
      rw [← integral_indicator (hAm k)]
      have e : (A k).indicator (fun ω => partialSum X k ω * R ω) =
          fun ω => (A k).indicator (partialSum X k) ω * R ω := by
        funext ω; simp only [Set.indicator]; split_ifs <;> simp
      rw [e, hYR.integral_fun_mul_eq_mul_integral hYm hRm, hER, mul_zero]
    -- integrability on the event
    have iS2 : Integrable (fun ω => partialSum X k ω ^ 2) μ := (hSL2 k).integrable_sq
    have iR2 : Integrable (fun ω => R ω ^ 2) μ := hRL2.integrable_sq
    have iSR : Integrable (fun ω => partialSum X k ω * R ω) μ := (hSL2 k).integrable_mul hRL2
    have hexp : ∫ ω in A k, partialSum X n ω ^ 2 ∂μ =
        ∫ ω in A k, partialSum X k ω ^ 2 ∂μ + 2 * ∫ ω in A k, partialSum X k ω * R ω ∂μ
          + ∫ ω in A k, R ω ^ 2 ∂μ := by
      have pw : ∀ ω, partialSum X n ω ^ 2 =
          partialSum X k ω ^ 2 + 2 * (partialSum X k ω * R ω) + R ω ^ 2 := by
        intro ω; simp only [hR]; ring
      simp_rw [pw]
      have i1 : Integrable (fun ω => partialSum X k ω ^ 2 + 2 * (partialSum X k ω * R ω))
          (μ.restrict (A k)) := (iS2.add (iSR.const_mul 2)).restrict
      have i2 : Integrable (fun ω => R ω ^ 2) (μ.restrict (A k)) := iR2.restrict
      have i3 : Integrable (fun ω => partialSum X k ω ^ 2) (μ.restrict (A k)) := iS2.restrict
      have i4 : Integrable (fun ω => 2 * (partialSum X k ω * R ω)) (μ.restrict (A k)) :=
        (iSR.const_mul 2).restrict
      rw [integral_add i1 i2, integral_add i3 i4, integral_const_mul]
    have hR2 : 0 ≤ ∫ ω in A k, R ω ^ 2 ∂μ := setIntegral_nonneg (hAm k) fun ω _ => sq_nonneg _
    have hlow : x ^ 2 * μ.real (A k) ≤ ∫ ω in A k, partialSum X k ω ^ 2 ∂μ := by
      refine setIntegral_ge_of_const_le_real (hAm k) (measure_ne_top _ _) (fun ω hω => ?_)
        iS2.integrableOn
      have h1 : x ≤ |partialSum X k ω| := hω.1
      rw [← sq_abs (partialSum X k ω)]
      exact pow_le_pow_left₀ hx.le h1 2
    rw [hexp, hcross]
    linarith
  -- summing over the disjoint events
  have hSn2 : Integrable (fun ω => partialSum X n ω ^ 2) μ := (hSL2 n).integrable_sq
  have hmeasB : μ.real (⋃ k ∈ Finset.Icc 1 n, A k) = ∑ k ∈ Finset.Icc 1 n, μ.real (A k) :=
    measureReal_biUnion_finset hdisj (fun k _ => hAm k)
  have hintB : ∫ ω in ⋃ k ∈ Finset.Icc 1 n, A k, partialSum X n ω ^ 2 ∂μ =
      ∑ k ∈ Finset.Icc 1 n, ∫ ω in A k, partialSum X n ω ^ 2 ∂μ :=
    integral_biUnion_finset _ (fun k _ => hAm k) hdisj (fun k _ => hSn2.integrableOn)
  have hle : ∫ ω in ⋃ k ∈ Finset.Icc 1 n, A k, partialSum X n ω ^ 2 ∂μ ≤
      ∫ ω, partialSum X n ω ^ 2 ∂μ :=
    setIntegral_le_integral hSn2 (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  have hmeanS : μ[partialSum X n] = 0 := by
    have : partialSum X n = fun ω => ∑ i ∈ Finset.range n, X i ω := rfl
    rw [this, integral_finset_sum _ fun i _ => hint i]
    exact Finset.sum_eq_zero fun i _ => hmean i
  have hvar : Var[partialSum X n; μ] = ∫ ω, partialSum X n ω ^ 2 ∂μ :=
    variance_of_integral_eq_zero (hSm n).aemeasurable hmeanS
  have hsum : x ^ 2 * ∑ k ∈ Finset.Icc 1 n, μ.real (A k) ≤
      ∑ k ∈ Finset.Icc 1 n, ∫ ω in A k, partialSum X n ω ^ 2 ∂μ := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum hkey
  have hfinal : x ^ 2 * μ.real {ω | ∃ k ∈ Finset.Icc 1 n, x ≤ |partialSum X k ω|}
      ≤ Var[partialSum X n; μ] := by
    rw [hunion, hmeasB, hvar]; linarith
  have hx2 : 0 < x ^ 2 := by positivity
  rw [le_div_iff₀ hx2]
  have : (μ {ω | ∃ k ∈ Finset.Icc 1 n, x ≤ |partialSum X k ω|}).toReal =
      μ.real {ω | ∃ k ∈ Finset.Icc 1 n, x ≤ |partialSum X k ω|} := rfl
  rw [this]; linarith


theorem sc_main {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, μ[X i] = 0)
    (hvar : Summable (fun n => Var[X n; μ])) :
    SeriesConvergesAE X μ := by
  classical
  set v : ℕ → ℝ := fun n => Var[X n; μ] with hv
  have hv0 : ∀ n, 0 ≤ v n := fun n => variance_nonneg _ _
  set T : ℕ → ℝ := fun M => ∑' k, v (k + M) with hT
  have hTlim : Tendsto T atTop (nhds 0) := tendsto_sum_nat_add v
  have hSm : ∀ j, Measurable (partialSum X j) := fun j =>
    Finset.measurable_sum (Finset.range j) fun i _ => hmeas i
  -- tail maximal inequality
  have htail : ∀ M (ε : ℝ), 0 < ε →
      μ {ω | ∃ k, ε ≤ |partialSum X (M + k) ω - partialSum X M ω|} ≤
        ENNReal.ofReal (T M / ε ^ 2) := by
    intro M ε hε
    set Y : ℕ → Ω → ℝ := fun i => X (M + i) with hY
    have hYind : iIndepFun Y μ := hindep.precomp (g := fun i => M + i) (add_right_injective M)
    have hYpart : ∀ k ω, partialSum Y k ω = partialSum X (M + k) ω - partialSum X M ω := by
      intro k ω
      simp only [partialSum, hY]
      rw [Finset.sum_range_add]; ring
    set E : ℕ → Set Ω := fun N => {ω | ∃ k ∈ Finset.Icc 1 N, ε ≤ |partialSum Y k ω|} with hE
    have hEle : ∀ N, μ (E N) ≤ ENNReal.ofReal (T M / ε ^ 2) := by
      intro N
      have h := km_main Y (fun i => hmeas _) hYind (fun i => hL2 _) (fun i => hmean _) N ε hε
      have hvarY : Var[partialSum Y N; μ] = ∑ i ∈ Finset.range N, v (M + i) := by
        have e : partialSum Y N = ∑ i ∈ Finset.range N, Y i := by
          funext ω; simp [partialSum, Finset.sum_apply]
        rw [e, IndepFun.variance_sum (fun i _ => hL2 _)
          (fun i _ j _ hij => hYind.indepFun hij)]
      have hsum_le : ∑ i ∈ Finset.range N, v (M + i) ≤ T M := by
        have hs : Summable (fun k => v (k + M)) := (summable_nat_add_iff M).mpr hvar
        calc ∑ i ∈ Finset.range N, v (M + i) = ∑ i ∈ Finset.range N, v (i + M) := by
              simp_rw [add_comm M]
          _ ≤ T M := hs.sum_le_tsum _ (fun i _ => hv0 _)
      rw [← ofReal_measureReal (measure_ne_top μ (E N))]
      apply ENNReal.ofReal_le_ofReal
      have : μ.real (E N) ≤ Var[partialSum Y N; μ] / ε ^ 2 := h
      rw [hvarY] at this
      exact this.trans (div_le_div_of_nonneg_right hsum_le (by positivity))
    have hmono : Monotone E := by
      intro a b hab ω hω
      obtain ⟨k, hk, hk'⟩ := hω
      exact ⟨k, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2.trans hab⟩, hk'⟩
    have hsub : {ω | ∃ k, ε ≤ |partialSum X (M + k) ω - partialSum X M ω|} ⊆ ⋃ N, E N := by
      rintro ω ⟨k, hk⟩
      rw [← hYpart] at hk
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp [partialSum] at hk; linarith
        · exact h0
      exact Set.mem_iUnion.mpr ⟨k, k, Finset.mem_Icc.mpr ⟨hk1, le_rfl⟩, hk⟩
    calc μ {ω | ∃ k, ε ≤ |partialSum X (M + k) ω - partialSum X M ω|} ≤ μ (⋃ N, E N) :=
          measure_mono hsub
      _ = ⨆ N, μ (E N) := hmono.measure_iUnion
      _ ≤ ENNReal.ofReal (T M / ε ^ 2) := iSup_le hEle
  -- non-Cauchy events are null
  set B : ℝ → Set Ω := fun ε => {ω | ∀ M, ∃ k, ε ≤ |partialSum X (M + k) ω - partialSum X M ω|}
    with hB
  have hBnull : ∀ ε : ℝ, 0 < ε → μ (B ε) = 0 := by
    intro ε hε
    have hle : ∀ M, μ (B ε) ≤ ENNReal.ofReal (T M / ε ^ 2) := fun M =>
      (measure_mono (fun ω (hω : ω ∈ B ε) => (hω M : ω ∈ {ω | ∃ k, ε ≤ |partialSum X (M + k) ω - partialSum X M ω|}))).trans (htail M ε hε)
    have hlim : Tendsto (fun M => ENNReal.ofReal (T M / ε ^ 2)) atTop (nhds 0) := by
      have := (hTlim.div_const (ε ^ 2))
      rw [zero_div] at this
      simpa using ENNReal.tendsto_ofReal this
    exact le_antisymm (ge_of_tendsto' hlim hle) zero_le
  have hnull : μ (⋃ j : ℕ, B (1 / ((j : ℝ) + 1))) = 0 :=
    measure_iUnion_null fun j => hBnull _ (by positivity)
  rw [SeriesConvergesAE, ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hnull
  simp only [Set.mem_setOf_eq, not_exists] at hω
  by_contra hc
  simp only [Set.mem_iUnion, not_exists] at hc
  have hcau : CauchySeq (fun N => partialSum X N ω) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    have hnot := hc j
    simp only [hB, Set.mem_setOf_eq, not_forall, not_exists, not_le] at hnot
    obtain ⟨M, hM⟩ := hnot
    refine ⟨M, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [Real.dist_eq]
    exact (hM k).trans hj
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  exact hω L hL

end DurrettProbability

open DurrettProbability

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) (hL2 : ∀ i, MemLp (X i) 2 μ) (hmean : ∀ i, μ[X i] = 0)
    (hvar : Summable (fun n => Var[X n; μ])) :
    SeriesConvergesAE X μ := by
  exact sc_main X hmeas hindep hL2 hmean hvar
