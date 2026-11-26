-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.residual_process_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:08:59.697046+00:00
-- url     : https://prove2.me/submissions/80686d7f-891e-4f2d-92a6-8fe7ec1c0924

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_residual_event

open BellWilliams2001.ThresholdPolicy
open MeasureTheory Filter Topology Set
open scoped ENNReal

set_option maxHeartbeats 900000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < c → ∀ Tstar : ℕ → Allocation Ω,
      (∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (Tstar n) ∧ M.IsThreshold c n (Tstar n)) →
      ∀ t : ℝ, 0 ≤ t → ∀ ε : ℝ, 0 < ε →
        let τ₀ : ℕ → Ω → ℝ≥0∞ := fun n ω =>
          ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : (M.threshold c n : ℝ) ≤ M.queue n (Tstar n) ω 0 s),
            ENNReal.ofReal s
        Tendsto (fun n => M.P {ω | ENNReal.ofReal (M.r n * ε) ≤
            ⨆ (s : ℝ) (_ : 0 ≤ s) (_ : ENNReal.ofReal s ≤ τ₀ n ω),
              ENNReal.ofReal (SystemSequence.idle (Tstar n) ω 0 s)}) atTop (𝓝 0) ∧
        Tendsto (fun n => M.P {ω | ∃ s : ℝ, 0 ≤ s ∧ τ₀ n ω ≤ ENNReal.ofReal s ∧
            s ≤ M.r n ^ 2 * t ∧
            (M.threshold c n : ℝ) - 1 ≤ |M.queue n (Tstar n) ω 0 s - (M.threshold c n : ℝ)|})
          atTop (𝓝 0) := by
  obtain ⟨c₀,hc₀,h⟩ := threshold_residual_event M
  refine ⟨c₀,hc₀,fun c hc Tstar hT t ht ε hε => ?_⟩
  obtain ⟨D,C,hD,hC,hE⟩ := h c hc
  let τ (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : (M.threshold c n : ℝ) ≤ M.queue n (Tstar n) ω 0 s), ENNReal.ofReal s
  let E₁ (n : ℕ) : Set Ω := {ω | ENNReal.ofReal (M.r n * ε) ≤
    ⨆ (s : ℝ) (_ : 0 ≤ s) (_ : ENNReal.ofReal s ≤ τ n ω),
      ENNReal.ofReal (SystemSequence.idle (Tstar n) ω 0 s)}
  let E₂ (n : ℕ) : Set Ω := {ω | ∃ s : ℝ, 0 ≤ s ∧ τ n ω ≤ ENNReal.ofReal s ∧
      s ≤ M.r n ^ 2 * t ∧ (M.threshold c n : ℝ) - 1 ≤ |M.queue n (Tstar n) ω 0 s - (M.threshold c n : ℝ)|}
  change Tendsto (fun n => M.P (E₁ n)) atTop (𝓝 0) ∧ Tendsto (fun n => M.P (E₂ n)) atTop (𝓝 0)
  have hPow : Tendsto (fun n => M.r n ^ 6) atTop atTop := (tendsto_pow_atTop (by norm_num)).comp M.r_tendsto
  have hSmall : Tendsto (fun n => C*(2+t)/M.r n^6) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hPow
  have hBound : Tendsto (fun n => ENNReal.ofReal (C*(2+t)/M.r n^6)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hSmall
  have hLog : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hRatio : Tendsto (fun n => D*(Real.log (M.r n)/M.r n)) atTop (𝓝 0) := by
    simpa using (hLog.comp M.r_tendsto).const_mul D
  have hElig : ∀ᶠ n in atTop, 1 ≤ M.threshold c n := by
    have hp : 0 < c := hc₀.trans hc
    have h := (Real.tendsto_log_atTop.comp M.r_tendsto).const_mul_atTop hp
    exact (h.eventually_ge_atTop (1:ℝ)).mono (fun _ hn => (Nat.one_le_floor_iff _).mpr hn)
  have hBoth : ∀ᶠ n in atTop,
      M.P (E₁ n) ≤ ENNReal.ofReal (C*(2+t)/M.r n^6) ∧
      M.P (E₂ n) ≤ ENNReal.ofReal (C*(2+t)/M.r n^6) := by
    filter_upwards [hE Tstar hT,hRatio.eventually_lt_const hε,hElig] with n hn hSmall' hLn
    obtain ⟨E,_,hPE,hOff⟩ := hn t ht
    refine ⟨(measure_mono (fun ω hω => ?_)).trans hPE,(measure_mono (fun ω hω => ?_)).trans hPE⟩
    · by_contra hNot
      have hτ := (hOff ω hNot).1
      have hr : 0 < M.r n := zero_lt_one.trans_le (M.r_ge n)
      have hCut : D*Real.log (M.r n) < M.r n*ε := by
        rw [← mul_div_assoc,div_lt_iff₀ hr] at hSmall'
        simpa only [mul_comm ε] using hSmall'
      have hDom : (⨆ (s : ℝ) (_ : 0 ≤ s) (_ : ENNReal.ofReal s ≤ τ n ω),
          ENNReal.ofReal (SystemSequence.idle (Tstar n) ω 0 s)) ≤
          ENNReal.ofReal (D*Real.log (M.r n)) := by
        refine iSup_le fun s => iSup_le fun hs => iSup_le fun hst => ?_
        have hT0 := (hT n hLn).1.alloc_mono ω 0 (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl)
          (show s ∈ Ici 0 from hs) hs
        rw [(hT n hLn).1.alloc_zero] at hT0
        have hIdle : SystemSequence.idle (Tstar n) ω 0 s ≤ s := by
          simpa only [SystemSequence.idle,if_true,sub_le_self_iff] using hT0
        exact (ENNReal.ofReal_le_ofReal hIdle).trans (hst.trans hτ)
      exact ((ENNReal.ofReal_lt_ofReal_iff (mul_pos hr hε)).2 hCut).not_ge
        ((show ENNReal.ofReal (M.r n*ε) ≤ _ from hω).trans hDom)
    · by_contra hNot
      obtain ⟨s,hs,hτ,hsT,hbad⟩ := hω
      exact ((hOff ω hNot).2 s hs hτ hsT).not_ge hbad
  exact ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBound
      (Eventually.of_forall (fun _ => bot_le)) (hBoth.mono fun _ hn => hn.1),
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBound
      (Eventually.of_forall (fun _ => bot_le)) (hBoth.mono fun _ hn => hn.2)⟩
