-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.admissible_queue_regularity
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:08:58.469804+00:00
-- url     : https://prove2.me/submissions/53327236-bdfc-4183-b49d-33888dd41129

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
open BellWilliams2001.ThresholdPolicy

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

private theorem queue_right {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hT : M.IsAdmissible n T) (ω : Ω) (k : Fin 2)
    (t : ℝ) (ht : 0 ≤ t) : ContinuousWithinAt (fun s => M.Qhat n T ω s k) (Ici t) t := by
  have aRight (i : Fin 2) (u : ℝ) (hu : 0 ≤ u) :
      ContinuousWithinAt (M.A n i ω) (Ici u) u := by
    obtain ⟨hm,h0,hUnbounded⟩ := scaled_epochs (fun j => M.uC_pos i j ω) (M.uC_finite i ω) (M.lamR_pos n i)
    exact count_comp_right hm h0 hUnbounded hu continuous_id.continuousWithinAt (fun _ hs => hs)
  have sRight (j : Fin 3) (u : ℝ) (hu : 0 ≤ u) :
      ContinuousWithinAt (fun v => M.S n j ω (T ω j v)) (Ici u) u := by
    obtain ⟨hm,h0,hUnbounded⟩ := scaled_epochs (fun i => M.vC_pos j i ω) (M.vC_finite j ω) (M.muR_pos n j)
    have hNon := hT.alloc_mono ω j (show (0 : ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl)
      (show u ∈ Ici 0 from hu) hu
    rw [hT.alloc_zero ω j] at hNon
    have hcont := (hT.alloc_cont ω j u hu).mono (fun s hs => hu.trans hs)
    exact count_comp_right hm h0 hUnbounded hNon hcont
      (fun v hv => hT.alloc_mono ω j hu (hu.trans hv) hv)
  let R := M.r n ^ 2
  have hR : 0 ≤ R := sq_nonneg _
  have hRt : 0 ≤ R*t := mul_nonneg hR ht
  have hq : ContinuousWithinAt (M.queue n T ω k) (Ici (R*t)) (R*t) := by
    change ContinuousWithinAt (fun u => M.queue n T ω k u) (Ici (R*t)) (R*t)
    by_cases hk : k = 0
    · simpa only [SystemSequence.queue, if_pos hk, Pi.sub_def] using
        ((aRight 0 _ hRt).sub (sRight 0 _ hRt)).sub (sRight 1 _ hRt)
    · simpa only [SystemSequence.queue, if_neg hk, Pi.sub_def] using
        (aRight 1 _ hRt).sub (sRight 2 _ hRt)
  have hRcont : ContinuousWithinAt (fun v : ℝ => R * v) (Ici t) t :=
    (continuous_const.mul continuous_id).continuousWithinAt
  have hMap : MapsTo (fun v : ℝ => R * v) (Ici t) (Ici (R*t)) :=
    fun v hv => mul_le_mul_of_nonneg_left hv hR
  exact (hq.comp hRcont hMap).div_const _

private theorem renewal_to_nat_mono {e : ℕ → ℝ} (he : Tendsto e atTop atTop) :
    Monotone (fun t => (renewalCount e t).toNat) := by
  intro s t hst
  have hf : renewalCount e t ≠ ⊤ := by
    obtain ⟨j,hj⟩ := eventually_atTop.1 (he.eventually_gt_atTop t)
    apply ne_top_of_le_ne_top (show (j : ℕ∞) ≠ ⊤ by simp)
    exact iSup_le fun i => iSup_le fun hi => by
      have h : i ≤ j := le_of_not_ge (fun h => (hj i h).not_ge hi)
      exact_mod_cast h
  have hLe : renewalCount e s ≤ renewalCount e t := by
    exact iSup_le fun i => iSup_le fun hi => le_iSup_of_le i (le_iSup_of_le (hi.trans hst) le_rfl)
  exact ENat.toNat_le_toNat hLe hf

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

private theorem aemeasurable_count {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (e : ℕ → Ω → ℝ) (he : ∀ j, Measurable (e j))
    (hfin : ∀ ω, Tendsto (fun j => e j ω) atTop atTop)
    (v : Ω → ℝ) (hv : AEMeasurable v P) :
    AEMeasurable (fun ω => ((renewalCount (fun j => e j ω) (v ω)).toNat : ℝ)) P := by
  refine (measurable_count e he hfin _ hv.measurable_mk).aemeasurable.congr ?_
  filter_upwards [hv.ae_eq_mk] with ω hω
  rw [hω]

set_option maxHeartbeats 1150000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hT : M.IsAdmissible n T) :
    (∀ ω k, IsCadlag (fun t => M.Qhat n T ω t k)) ∧
    (∀ t, 0 ≤ t → ∀ k, AEMeasurable (fun ω => M.Qhat n T ω t k) M.P) := by
  have hMeasA (i : Fin 2) (u : ℝ) : Measurable (fun ω => M.A n i ω u) := by
    refine measurable_count (fun j ω => M.xi n i ω j) (fun j => ?_) (fun ω => ?_) (fun _ => u) measurable_const
    · unfold SystemSequence.xi partialSum
      exact Finset.measurable_sum _ (fun k _ => (M.uC_meas i k).div_const _)
    · exact (scaled_epochs (fun j => M.uC_pos i j ω) (M.uC_finite i ω) (M.lamR_pos n i)).2.2
  have hMeasS (j : Fin 3) (u : ℝ) (hu : 0 ≤ u) :
      AEMeasurable (fun ω => M.S n j ω (T ω j u)) M.P := by
    refine aemeasurable_count (fun i ω => M.eta n j ω i) (fun i => ?_) (fun ω => ?_) _ (hT.meas j u hu)
    · unfold SystemSequence.eta partialSum
      exact Finset.measurable_sum _ (fun k _ => (M.vC_meas j k).div_const _)
    · exact (scaled_epochs (fun i => M.vC_pos j i ω) (M.vC_finite j ω) (M.muR_pos n j)).2.2
  refine ⟨?_,?_⟩
  · intro ω k
    refine ⟨fun t ht => queue_right M n T hT ω k t ht, ?_⟩
    intro t ht
    let R := M.r n ^ 2
    have hR : 0 ≤ R := sq_nonneg _
    let A (i : Fin 2) (s : ℝ) := M.A n i ω (R*s)
    let S (j : Fin 3) (s : ℝ) := M.S n j ω (T ω j (max (R*s) 0))
    have hmonoA (i : Fin 2) : Monotone (A i) := by
      intro s v hsv
      dsimp only [A, SystemSequence.A, SystemSequence.xi]
      exact_mod_cast renewal_to_nat_mono
        (scaled_epochs (fun j => M.uC_pos i j ω) (M.uC_finite i ω) (M.lamR_pos n i)).2.2
        (mul_le_mul_of_nonneg_left hsv hR)
    have hmonoS (j : Fin 3) : Monotone (S j) := by
      intro s v hsv
      have hm := hT.alloc_mono ω j (show max (R*s) 0 ∈ Ici (0:ℝ) from mem_Ici.mpr (le_max_right _ _))
        (show max (R*v) 0 ∈ Ici (0:ℝ) from mem_Ici.mpr (le_max_right _ _))
        (max_le_max (mul_le_mul_of_nonneg_left hsv hR) le_rfl)
      dsimp only [S, SystemSequence.S, SystemSequence.eta]
      exact_mod_cast renewal_to_nat_mono
        (scaled_epochs (fun i => M.vC_pos j i ω) (M.vC_finite j ω) (M.muR_pos n j)).2.2 hm
    have hplus : ∀ᶠ s in 𝓝[<] t, 0 ≤ s := mem_nhdsWithin_of_mem_nhds (le_mem_nhds ht)
    by_cases hk : k = 0
    · refine ⟨((A 0).leftLim t - (S 0).leftLim t - (S 1).leftLim t) / M.r n, ?_⟩
      have hh := (((hmonoA 0).tendsto_leftLim t).sub ((hmonoS 0).tendsto_leftLim t)).sub
        ((hmonoS 1).tendsto_leftLim t)
      refine (hh.div_const (M.r n)).congr' ?_
      filter_upwards [hplus] with s hs
      simp [A,S,R,SystemSequence.Qhat,SystemSequence.queue,hk,max_eq_left (mul_nonneg hR hs)]
    · refine ⟨((A 1).leftLim t - (S 2).leftLim t) / M.r n, ?_⟩
      have hh := ((hmonoA 1).tendsto_leftLim t).sub ((hmonoS 2).tendsto_leftLim t)
      refine (hh.div_const (M.r n)).congr' ?_
      filter_upwards [hplus] with s hs
      simp [A,S,R,SystemSequence.Qhat,SystemSequence.queue,hk,max_eq_left (mul_nonneg hR hs)]
  · intro t ht k
    have hu : 0 ≤ M.r n ^ 2 * t := mul_nonneg (sq_nonneg _) ht
    by_cases hk : k = 0
    · exact (((hMeasA 0 (M.r n ^ 2 * t)).aemeasurable.sub (hMeasS 0 _ hu)).sub (hMeasS 1 _ hu)).div_const (M.r n) |>.congr
        (ae_of_all _ fun _ => by simp [SystemSequence.Qhat,SystemSequence.queue,hk])
    · exact ((hMeasA 1 (M.r n ^ 2 * t)).aemeasurable.sub (hMeasS 2 _ hu)).div_const (M.r n) |>.congr
        (ae_of_all _ fun _ => by simp [SystemSequence.Qhat,SystemSequence.queue,hk])
