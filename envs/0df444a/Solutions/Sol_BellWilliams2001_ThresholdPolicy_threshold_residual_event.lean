-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.threshold_residual_event
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:08:59.491801+00:00
-- url     : https://prove2.me/submissions/97e0eb47-2830-4b31-b1b7-ca535ed84bf4

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_admissible_queue_regularity
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_class_one_primitive_increment_envelope
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_band_from_increment_bounds
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_queue_increment_from_renewal_bounds

open BellWilliams2001.ThresholdPolicy
open MeasureTheory Filter Topology Set
open scoped ENNReal

private theorem zero_count_partial_sum {f : ℕ → ℝ} (hf : ∀ i, 1 ≤ i → 0 < f i) :
    renewalCount (partialSum f) 0 = 0 := by
  apply le_antisymm _ bot_le
  refine iSup_le fun m => iSup_le fun hm => ?_
  have hz : m = 0 := by
    by_contra! h
    have he : m ∈ Finset.Icc 1 m := Finset.mem_Icc.2 ⟨by omega,le_rfl⟩
    have hh : f m ≤ partialSum f m := Finset.single_le_sum
      (fun i hi => (hf i (Finset.mem_Icc.1 hi).1).le) he
    exact ((hf m (by omega)).trans_le hh).not_ge hm
  simp [hz]

private theorem queue_zero {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T) (ω : Ω) :
    M.queue n T ω 0 0 = 0 := by
  have ha : renewalCount (M.xi n 0 ω) 0 = 0 :=
    zero_count_partial_sum (fun i hi => div_pos (M.uC_pos 0 i ω hi) (M.lamR_pos n 0))
  have hs (j : Fin 3) : renewalCount (M.eta n j ω) 0 = 0 :=
    zero_count_partial_sum (fun i hi => div_pos (M.vC_pos j i ω hi) (M.muR_pos n j))
  simp [SystemSequence.queue,SystemSequence.A,SystemSequence.S,hA.alloc_zero,ha,hs]

private theorem queue_raw_right {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T) (ω : Ω) (s : ℝ) (hs : 0 ≤ s) :
    ContinuousWithinAt (M.queue n T ω 0) (Ici s) s := by
  let R := M.r n^2
  have hR : 0 < R := pow_pos (zero_lt_one.trans_le (M.r_ge n)) _
  have hr : M.r n ≠ 0 := (zero_lt_one.trans_le (M.r_ge n)).ne'
  have h := ((admissible_queue_regularity M n T hA).1 ω 0).1 (s/R) (div_nonneg hs hR.le)
  have hc : ContinuousWithinAt (fun u : ℝ => u/R) (Ici s) s :=
    (continuous_id.div_const _).continuousWithinAt
  have hMaps : MapsTo (fun u : ℝ => u/R) (Ici s) (Ici (s/R)) :=
    fun u hu => div_le_div_of_nonneg_right hu hR.le
  have hC := (ContinuousWithinAt.comp (f := fun u : ℝ => u/R) h hc hMaps).mul_const (M.r n)
  have he : (fun u => M.Qhat n T ω (u/R) 0 * M.r n) = M.queue n T ω 0 := by
    funext u
    simp only [SystemSequence.Qhat, ← show R = M.r n^2 from rfl, mul_div_cancel₀ _ hR.ne', div_mul_cancel₀ _ hr]
  change ContinuousWithinAt (fun u => M.Qhat n T ω (u/R) 0 * M.r n) (Ici s) s at hC
  rwa [he] at hC

private theorem visit_of_threshold_time_le (q : ℝ → ℝ) (L s : ℝ) (hs : 0 ≤ s)
    (hRight : ContinuousWithinAt q (Ici s) s)
    (hτ : (⨅ (u : ℝ) (_ : 0 ≤ u) (_ : L ≤ q u), ENNReal.ofReal u) ≤ ENNReal.ofReal s) :
    ∃ u ∈ Icc 0 s, L ≤ q u := by
  by_contra! hn
  have hq := hn s ⟨hs,le_rfl⟩
  have hnear : ∀ᶠ u in 𝓝[Ici s] s, q u < L := hRight.eventually (gt_mem_nhds hq)
  obtain ⟨δ,hδ,hNear⟩ := Metric.mem_nhdsWithin_iff.1 hnear
  have hLow : ENNReal.ofReal (s+δ) ≤ ⨅ (u : ℝ) (_ : 0 ≤ u) (_ : L ≤ q u), ENNReal.ofReal u := by
    refine le_iInf fun u => le_iInf fun hu => le_iInf fun hqu => ENNReal.ofReal_le_ofReal ?_
    have hsu : s < u := by
      by_contra! hle
      exact (hn u ⟨hu,hle⟩).not_ge hqu
    by_contra! hclose
    have hdist : dist u s < δ := by rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hsu)]; linarith
    exact (hNear (show u ∈ Metric.ball s δ ∩ Ici s from ⟨hdist, mem_Ici.mpr hsu.le⟩)).not_ge hqu
  have he := (ENNReal.ofReal_le_ofReal_iff hs).1 (hLow.trans hτ)
  linarith

set_option maxHeartbeats 1400000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < c → ∃ D C : ℝ, 0 < D ∧ 0 ≤ C ∧
      ∀ T : ℕ → Allocation Ω,
      (∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (T n) ∧ M.IsThreshold c n (T n)) →
      ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → ∃ E : Set Ω, MeasurableSet E ∧
      M.P E ≤ ENNReal.ofReal (C*(2+t)/M.r n^6) ∧ ∀ ω ∉ E,
        let τ : ℝ≥0∞ := ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : (M.threshold c n : ℝ) ≤ M.queue n (T n) ω 0 s),
          ENNReal.ofReal s
        τ ≤ ENNReal.ofReal (D*Real.log (M.r n)) ∧
          ∀ s : ℝ, 0 ≤ s → τ ≤ ENNReal.ofReal s → s ≤ M.r n^2*t →
            |M.queue n (T n) ω 0 s - (M.threshold c n : ℝ)| < (M.threshold c n : ℝ)-1 := by
  obtain ⟨η,α,K,C,hη,hα,hK,hC,hE⟩ := class_one_primitive_increment_envelope M
  let c₀ := 6*K+3
  refine ⟨c₀,by dsimp [c₀]; positivity,fun c hc => ?_⟩
  have hc0 : 0 < c := lt_trans (by dsimp [c₀]; positivity) hc
  let D := (c+3*K+1)/α
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,C,hD,hC,fun T hT => ?_⟩
  have hLog : Tendsto (fun r : ℝ => Real.log r/r) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hDlim : Tendsto (fun n => D * (Real.log (M.r n)/M.r n)) atTop (𝓝 0) := by
    simpa using (hLog.comp M.r_tendsto).const_mul D
  filter_upwards [hE,(Real.tendsto_log_atTop.comp M.r_tendsto).eventually_ge_atTop 1,
    hDlim.eventually_lt_const (show (0:ℝ)<1 by norm_num)] with n hn hlog hDsmall
  let ℓ := Real.log (M.r n)
  let L : ℝ := M.threshold c n
  have hℓ₁ : 1 ≤ ℓ := hlog
  have hℓ : 0 < ℓ := zero_lt_one.trans_le hℓ₁
  have hprod : 0 ≤ c*ℓ := mul_nonneg hc0.le hℓ.le
  have hLu : L ≤ c*ℓ := Nat.floor_le hprod
  have hLl : c*ℓ < L+1 := Nat.lt_floor_add_one _
  have hBand : 6*K*ℓ < L-1 := by
    have h := mul_lt_mul_of_pos_right hc hℓ
    dsimp [c₀] at h
    nlinarith
  have hLn : 1 ≤ M.threshold c n := by
    have hh : 1 ≤ L := by nlinarith [mul_pos hK hℓ]
    dsimp [L] at hh
    exact_mod_cast hh
  obtain ⟨hA,hP⟩ := hT n hLn
  have hr : 0 < M.r n := zero_lt_one.trans_le (M.r_ge n)
  have hSmall : D*ℓ ≤ M.r n^2 := by
    rw [← mul_div_assoc,div_lt_iff₀ hr,one_mul] at hDsmall
    exact hDsmall.le.trans (by nlinarith [mul_nonneg hr.le (sub_nonneg.mpr (M.r_ge n))])
  intro t ht
  obtain ⟨E,hEm,hPE,hGood⟩ := hn.2.2 (t+1) (by positivity)
  refine ⟨E,hEm,by simpa only [show 1+(t+1)=2+t by ring] using hPE,?_⟩
  intro ω hω
  let q := M.queue n (T n) ω 0
  let H := M.r n^2*(t+1)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let K' := M.lamR n 0+M.muR n 0+M.muR n 1+3*η
  have hK' : 0 ≤ K' := by dsimp [K']; positivity [M.lamR_pos n 0,M.muR_pos n 0,M.muR_pos n 1]
  obtain ⟨hAny,hBelow,hAbove⟩ := threshold_queue_increment_from_renewal_bounds M c n (T n) hA hP
    hLn ω H η (K*ℓ) α hη.le (mul_nonneg hK.le hℓ.le) hn.1 hn.2.1 (hGood ω hω).1 (hGood ω hω).2
  have hB := threshold_band_from_increment_bounds q H L K' (3*(K*ℓ)) α hH (by positivity [L])
    hK' (by positivity) hα (queue_zero M n (T n) hA ω) hAny hBelow hAbove
  have hDIn : D*ℓ ∈ Icc 0 H := ⟨mul_nonneg hD.le hℓ.le,
    hSmall.trans (le_mul_of_one_le_right (sq_nonneg _) (by linarith))⟩
  have hReach : L+3*(K*ℓ) < α*(D*ℓ) := by
    have hEq : α*D = c+3*K+1 := by dsimp [D]; field_simp
    rw [← mul_assoc α D ℓ,hEq]
    nlinarith
  obtain ⟨u,hu,huQ⟩ := hB.2.2 _ hDIn hReach
  refine ⟨(iInf_le_of_le u (iInf_le_of_le hu.1 (iInf_le_of_le huQ le_rfl))).trans
    (ENNReal.ofReal_le_ofReal hu.2),?_⟩
  intro s hs hTime hsT
  have hsH : s ∈ Icc 0 H := ⟨hs,hsT.trans (by dsimp [H]; gcongr; linarith)⟩
  have hHit := visit_of_threshold_time_le q L s hs (queue_raw_right M n (T n) hA ω s hs) hTime
  have hUpper := hB.1 s hsH
  have hLower := hB.2.1 s hsH hHit
  exact abs_lt.2 ⟨by linarith,by linarith⟩
