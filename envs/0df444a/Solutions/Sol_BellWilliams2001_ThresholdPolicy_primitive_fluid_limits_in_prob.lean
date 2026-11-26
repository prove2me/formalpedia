-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.primitive_fluid_limits_in_prob
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:29:14.305424+00:00
-- url     : https://prove2.me/submissions/9b91e42d-e432-4993-9e37-eb8bf4319c55

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_primitive_fluid_limits_ae
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal

open BellWilliams2001.ThresholdPolicy
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

private theorem count_right {e : ℕ → ℝ} (hm : StrictMono e) (h0 : e 0 = 0)
    (hUnbounded : Tendsto e atTop atTop) {t : ℝ} (ht : 0 ≤ t) :
    ∃ b : ℝ, t < b ∧ ∀ s ∈ Ico t b, renewalCount e s = renewalCount e t := by
  have hex : ∃ i, t < e i := (hUnbounded.eventually_gt_atTop t).exists
  let i := Nat.find hex
  have hi : t < e i := Nat.find_spec hex
  have hi0 : i ≠ 0 := fun he => by simpa [he, h0, not_lt.mpr ht] using hi
  let j := i - 1
  have hij : j + 1 = i := by dsimp [j]; omega
  have hj : e j ≤ t := le_of_not_gt (Nat.find_min hex (by omega : j < i))
  have count_eq (s : ℝ) (h₁ : t ≤ s) (h₂ : s < e i) : renewalCount e s = j := by
    unfold renewalCount
    refine le_antisymm (iSup_le fun k => iSup_le fun hk => ?_) ?_
    · have hk' : k ≤ j := by
        by_contra! h
        exact (h₂.trans_le (hm.monotone (by omega : i ≤ k))).not_ge hk
      exact_mod_cast hk'
    · exact le_iSup_of_le j (le_iSup_of_le (hj.trans h₁) le_rfl)
  exact ⟨e i, hi, fun s hs => (count_eq s hs.1 hs.2).trans (count_eq t le_rfl hi).symm⟩

private theorem count_comp_right {e : ℕ → ℝ} (hm : StrictMono e) (h0 : e 0 = 0)
    (hUnbounded : Tendsto e atTop atTop) {v : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ v t)
    (hc : ContinuousWithinAt v (Ici t) t) (hv : ∀ s ∈ Ici t, v t ≤ v s) :
    ContinuousWithinAt (fun s => ((renewalCount e (v s)).toNat : ℝ)) (Ici t) t := by
  obtain ⟨b,hb,hcount⟩ := count_right hm h0 hUnbounded ht
  have h : ∀ᶠ s in 𝓝[Ici t] t, v s < b := hc.eventually (gt_mem_nhds hb)
  have hs : ∀ᶠ s in 𝓝[Ici t] t, s ∈ Ici t := self_mem_nhdsWithin
  have he : (fun s => ((renewalCount e (v s)).toNat : ℝ)) =ᶠ[𝓝[Ici t] t]
      (fun _ => ((renewalCount e (v t)).toNat : ℝ)) := by
    filter_upwards [h,hs] with s hsb hst
    rw [hcount (v s) ⟨hv s hst,hsb⟩]
  exact tendsto_const_nhds.congr' he.symm

private theorem scaled_epochs {f : ℕ → ℝ} (hf : ∀ j, 1 ≤ j → 0 < f j)
    (hlim : Tendsto (partialSum f) atTop atTop) {a : ℝ} (ha : 0 < a) :
    let e := partialSum (fun j => f j / a)
    StrictMono e ∧ e 0 = 0 ∧ Tendsto e atTop atTop := by
  have hcongr (j : ℕ) : partialSum (fun i => f i / a) j = (partialSum f j) / a := by
    simp [partialSum, Finset.sum_div]
  have hMono : StrictMono (partialSum f) := strictMono_nat_of_lt_succ fun j => by
    have he : Finset.Icc 1 (j+1) = insert (j+1) (Finset.Icc 1 j) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [partialSum, partialSum, he, Finset.sum_insert (by simp)]
    linarith [hf (j+1) (by omega)]
  refine ⟨fun i j hij => ?_, by simp [partialSum], ?_⟩
  · simp only [hcongr]
    exact div_lt_div_of_pos_right (hMono hij) ha
  · exact (hlim.atTop_div_const ha).congr (fun j => (hcongr j).symm)


private theorem measurable_count {Ω : Type*} [MeasurableSpace Ω]
    (e : ℕ → Ω → ℝ) (he : ∀ j, Measurable (e j))
    (hfin : ∀ ω, Tendsto (fun j => e j ω) atTop atTop)
    (v : Ω → ℝ) (hv : Measurable v) :
    Measurable (fun ω => ((renewalCount (fun j => e j ω) (v ω)).toNat : ℝ)) := by
  let g (j : ℕ) (ω : Ω) : ℝ≥0∞ := if e j ω ≤ v ω then (j : ℝ≥0∞) else 0
  have hgm (j : ℕ) : Measurable (g j) :=
    Measurable.ite (measurableSet_le (he j) hv) measurable_const measurable_const
  have hcount (ω : Ω) : (((renewalCount (fun j => e j ω) (v ω)).toNat : ℕ) : ℝ≥0∞) =
      ⨆ j, g j ω := by
    let N := renewalCount (fun j => e j ω) (v ω)
    obtain ⟨m,hm⟩ := eventually_atTop.1 ((hfin ω).eventually_gt_atTop (v ω))
    have hN : N ≤ (m : ℕ∞) := by
      refine iSup_le fun j => iSup_le fun hj => ?_
      have h : j ≤ m := le_of_not_ge (fun h => (hm j h).not_ge hj)
      exact_mod_cast h
    have hNf : N ≠ ⊤ := ne_top_of_le_ne_top (by simp) hN
    have hNe : (N.toNat : ℕ∞) = N := ENat.natCast_toNat hNf
    change (N.toNat : ℝ≥0∞) = ⨆ j, g j ω
    refine le_antisymm ?_ (iSup_le fun j => ?_)
    · by_contra! h
      have hPos : 0 < N.toNat := by
        by_contra! h'
        simp [Nat.eq_zero_of_le_zero h'] at h
      have hle : N ≤ ((N.toNat - 1 : ℕ) : ℕ∞) := by
        refine iSup_le fun j => iSup_le fun hj => ?_
        have hjg : (j : ℝ≥0∞) ≤ ⨆ i, g i ω := by
          have hh := le_iSup (fun i => g i ω) j
          simpa only [g, if_pos hj] using hh
        have hj' : j < N.toNat := by exact_mod_cast hjg.trans_lt h
        exact_mod_cast (show j ≤ N.toNat-1 by omega)
      rw [← hNe] at hle
      exact (not_le_of_gt (Nat.sub_lt hPos Nat.one_pos)) (by exact_mod_cast hle)
    · by_cases h : e j ω ≤ v ω
      · have hh : (j : ℕ∞) ≤ N := le_iSup_of_le j (le_iSup_of_le h le_rfl)
        rw [← hNe] at hh
        have hj : j ≤ N.toNat := by exact_mod_cast hh
        simpa [g,h] using (show (j:ℝ≥0∞) ≤ (N.toNat:ℝ≥0∞) by exact_mod_cast hj)
      · simp [g,h]
  have hMeas := (Measurable.iSup hgm).ennreal_toReal
  convert hMeas using 1
  funext ω
  rw [← hcount]
  simp

private theorem uoc_of_ae_uoc {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℕ} (Z : ℕ → Ω → ℝ → Fin m → ℝ) (z : ℝ → Fin m → ℝ)
    (hMeas : ∀ n t i, Measurable (fun ω => Z n ω t i))
    (hRight : ∀ n ω t i, 0 ≤ t → ContinuousWithinAt (fun s => Z n ω s i) (Ici t) t)
    (hCont : ∀ i, Continuous (fun t => z t i))
    (hAe : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ s ∈ Icc 0 t, ∑ i, |Z n ω s i-z s i| < ε) : UocInProb P Z z := by
  intro T hT ε hε
  let F (n : ℕ) (ω : Ω) (t : ℝ) := ∑ i, |Z n ω t i-z t i|
  let ψ (n k : ℕ) : ℝ := min T ((k:ℝ)/(2:ℝ)^n)
  have hψ (n k : ℕ) : ψ n k ∈ Icc 0 T :=
    ⟨le_min hT (by positivity),min_le_left _ _⟩
  let E (n : ℕ) : Set Ω := ⋃ j : ℕ, ⋃ k : ℕ, {ω | ε/2 ≤ F n ω (ψ j k)}
  have hm (n : ℕ) : MeasurableSet (E n) := by
    refine MeasurableSet.iUnion (fun j => MeasurableSet.iUnion (fun k => measurableSet_le measurable_const ?_))
    exact Finset.measurable_sum _ (fun i _ => ((hMeas n (ψ j k) i).sub_const _).abs)
  have hE : Tendsto (fun n => P (E n)) atTop (𝓝 0) := by
    have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (μ := P) atTop
      (A := (∅ : Set Ω)) MeasurableSet.empty hm ?_
    · simpa using h
    · filter_upwards [hAe] with ω hω
      filter_upwards [hω T hT (ε/2) (by positivity)] with n hn
      simp only [notMem_empty,iff_false]
      intro he
      obtain ⟨j,hj⟩ := mem_iUnion.1 he
      obtain ⟨k,hk⟩ := mem_iUnion.1 hj
      exact (hn _ (hψ j k)).not_ge hk
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hE
    (Eventually.of_forall (fun _ => bot_le))
  apply Eventually.of_forall
  intro n
  apply measure_mono
  intro ω hω
  by_contra hNot
  have hAll (s : ℝ) (hs : s ∈ Icc 0 T) : F n ω s ≤ ε/2 := by
    let d (j : ℕ) : ℕ := ⌈s*(2:ℝ)^j⌉₊
    let u (j : ℕ) : ℝ := ψ j (d j)
    have hD (j : ℕ) : ((d j : ℕ) : ℝ) / (2:ℝ)^j =
        (((Nat.ceil ((s.toNNReal:ℝ)*(2:ℝ)^j) : ℝ≥0)/(2:ℝ≥0)^j):ℝ) := by
      simp [d,hs.1]
    have hU : Tendsto u atTop (𝓝 s) := by
      have h := (NNReal.continuous_coe.tendsto s.toNNReal).comp
        (AvramDividend.Classical.dyadic_ceiling_nnreal_tendsto s.toNNReal)
      have h' : Tendsto (fun j => ((d j : ℕ) : ℝ)/(2:ℝ)^j) atTop (𝓝 s) := by
        have ht := h.congr (fun j => (hD j).symm)
        simpa only [Real.coe_toNNReal _ hs.1] using ht
      simpa only [u,ψ,min_eq_right hs.2] using (tendsto_const_nhds (x := T)).min h'
    have hsU (j : ℕ) : s ≤ u j := by
      have h := AvramDividend.Classical.dyadic_ceiling_time_ge_nnreal s.toNNReal j
      have he : s ≤ ((d j : ℕ) : ℝ)/(2:ℝ)^j := by
        calc
          s = (s.toNNReal:ℝ) := (Real.coe_toNNReal _ hs.1).symm
          _ ≤ _ := NNReal.coe_le_coe.2 h
          _ = _ := (hD j).symm
      exact le_min hs.2 he
    have hR : ContinuousWithinAt (F n ω) (Ici s) s := by
      apply tendsto_finsetSum
      intro i _
      exact ((hRight n ω s i hs.1).sub ((hCont i).continuousWithinAt)).abs.tendsto
    have hlim := hR.tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hU,Eventually.of_forall (fun j => mem_Ici.mpr (hsU j))⟩)
    apply le_of_tendsto hlim
    exact Eventually.of_forall (fun j => (lt_of_not_ge (fun h => hNot
      (mem_iUnion.2 ⟨j,mem_iUnion.2 ⟨d j,h⟩⟩))).le)
  have hSup : supDist (Z n ω) z T ≤ ENNReal.ofReal (ε/2) :=
    iSup_le fun s => iSup_le fun hs => ENNReal.ofReal_le_ofReal (hAll s hs)
  exact ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)).not_ge (hω.trans hSup)

set_option maxHeartbeats 1250000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    UocInProb M.P (fun n ω t => M.Abar n ω t) (fun t k => M.lam k*t) ∧
    UocInProb M.P (fun n ω t => M.Sbar n ω t) (fun t j => M.mu j*t) := by
  letI : IsProbabilityMeasure M.P := M.isProb
  have aM (n : ℕ) (t : ℝ) (i : Fin 2) : Measurable (fun ω => M.Abar n ω t i) := by
    apply Measurable.div_const
    refine measurable_count (fun j ω => M.xi n i ω j) (fun j => ?_) (fun ω => ?_) _ measurable_const
    · unfold SystemSequence.xi partialSum
      exact Finset.measurable_sum _ (fun k _ => (M.uC_meas i k).div_const _)
    · exact (scaled_epochs (fun j => M.uC_pos i j ω) (M.uC_finite i ω) (M.lamR_pos n i)).2.2
  have sM (n : ℕ) (t : ℝ) (j : Fin 3) : Measurable (fun ω => M.Sbar n ω t j) := by
    apply Measurable.div_const
    refine measurable_count (fun i ω => M.eta n j ω i) (fun i => ?_) (fun ω => ?_) _ measurable_const
    · unfold SystemSequence.eta partialSum
      exact Finset.measurable_sum _ (fun k _ => (M.vC_meas j k).div_const _)
    · exact (scaled_epochs (fun i => M.vC_pos j i ω) (M.vC_finite j ω) (M.muR_pos n j)).2.2
  have rr (n : ℕ) : 0 ≤ M.r n^2 := sq_nonneg _
  have aR (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin 2) (ht : 0 ≤ t) :
      ContinuousWithinAt (fun s => M.Abar n ω s i) (Ici t) t := by
    obtain ⟨hm,h0,he⟩ := scaled_epochs (fun j => M.uC_pos i j ω) (M.uC_finite i ω) (M.lamR_pos n i)
    refine (count_comp_right hm h0 he (mul_nonneg (rr n) ht)
      ((continuous_const.mul continuous_id).continuousWithinAt) ?_).div_const _
    exact fun s hs => mul_le_mul_of_nonneg_left hs (rr n)
  have sR (n : ℕ) (ω : Ω) (t : ℝ) (j : Fin 3) (ht : 0 ≤ t) :
      ContinuousWithinAt (fun s => M.Sbar n ω s j) (Ici t) t := by
    obtain ⟨hm,h0,he⟩ := scaled_epochs (fun i => M.vC_pos j i ω) (M.vC_finite j ω) (M.muR_pos n j)
    refine (count_comp_right hm h0 he (mul_nonneg (rr n) ht)
      ((continuous_const.mul continuous_id).continuousWithinAt) ?_).div_const _
    exact fun s hs => mul_le_mul_of_nonneg_left hs (rr n)
  constructor
  · apply uoc_of_ae_uoc M.P _ _ aM aR (fun i => continuous_const.mul continuous_id)
    filter_upwards [primitive_fluid_limits_ae M] with ω hω H hH ε hε
    filter_upwards [hω H hH (ε/3) (by positivity)] with n hn t ht
    rw [Fin.sum_univ_two]
    simp only [Pi.mul_apply, id_eq]
    linarith [(hn t ht).1 0,(hn t ht).1 1]
  · apply uoc_of_ae_uoc M.P _ _ sM sR (fun j => continuous_const.mul continuous_id)
    filter_upwards [primitive_fluid_limits_ae M] with ω hω H hH ε hε
    filter_upwards [hω H hH (ε/4) (by positivity)] with n hn t ht
    rw [Fin.sum_univ_three]
    simp only [Pi.mul_apply, id_eq]
    linarith [(hn t ht).2 0,(hn t ht).2 1,(hn t ht).2 2]
