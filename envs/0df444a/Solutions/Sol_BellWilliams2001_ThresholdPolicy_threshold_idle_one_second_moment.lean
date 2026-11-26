-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.threshold_idle_one_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:29:13.489989+00:00
-- url     : https://prove2.me/submissions/8ff9e49a-8b12-4840-89e6-8f46197e7cd0

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_residual_event

open BellWilliams2001.ThresholdPolicy
open MeasureTheory Filter Topology Set
open scoped ENNReal

private theorem idle_eq_of_busy_after {Ω : Type*} [MeasurableSpace Ω]
    (M : SystemSequence Ω) (c : ℝ) (n : ℕ) (T : Allocation Ω)
    (hT : M.IsThreshold c n T) (ω : Ω) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbusy : ∀ s ∈ Ioc a b, M.serverTwoHolds n T ω s < M.queue n T ω 0 s) :
    SystemSequence.idle T ω 0 b = SystemSequence.idle T ω 0 a := by
  let E (t : ℝ) := {s ∈ Ioc 0 t | M.serverTwoHolds n T ω s < M.queue n T ω 0 s}
  have hE : E b = E a ∪ Ioc a b := by
    ext s
    change (s ∈ Ioc 0 b ∧ _) ↔ (s ∈ Ioc 0 a ∧ _) ∨ s ∈ Ioc a b
    simp only [mem_Ioc]
    constructor
    · intro hs
      by_cases h : s ≤ a
      · exact Or.inl ⟨⟨hs.1.1, h⟩, hs.2⟩
      · exact Or.inr ⟨lt_of_not_ge h, hs.1.2⟩
    · rintro (hs | hs)
      · exact ⟨⟨hs.1.1, hs.1.2.trans hab⟩, hs.2⟩
      · exact ⟨⟨ha.trans_lt hs.1, hs.2⟩, hbusy s hs⟩
  have hd : Disjoint (E a) (Ioc a b) := by
    refine Set.disjoint_left.2 (fun s hs hs' => ?_)
    exact (not_lt_of_ge hs.1.2) hs'.1
  have hfin : volume (E a) ≠ ⊤ := ne_top_of_le_ne_top
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measure_mono (fun _ hx => hx.1 : E a ⊆ Ioc 0 a))
  have hTa : T ω 0 a = (volume (E a)).toReal := (hT ω a ha).1
  have hTb : T ω 0 b = (volume (E b)).toReal := (hT ω b (ha.trans hab)).1
  rw [hE, measure_union hd measurableSet_Ioc, Real.volume_Ioc,
    ENNReal.toReal_add hfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] at hTb
  simp only [SystemSequence.idle, ↓reduceIte]
  linarith

set_option maxHeartbeats 1100000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < c → ∀ T : ℕ → Allocation Ω,
      (∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (T n) ∧ M.IsThreshold c n (T n)) →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t →
        (∫⁻ ω, ENNReal.ofReal (M.Ihat n (T n) ω t 0)^2 ∂M.P) ≤ ENNReal.ofReal (A*(1+t)^3) := by
  obtain ⟨c₀,hc₀,h⟩ := threshold_residual_event M
  refine ⟨c₀,hc₀,fun c hc T hT => ?_⟩
  obtain ⟨D,C,hD,hC,hE⟩ := h c hc
  let A := D^2+2*C
  refine ⟨A,by dsimp [A]; positivity,?_⟩
  letI : IsProbabilityMeasure M.P := M.isProb
  have hElig : ∀ᶠ n in atTop, 1 ≤ M.threshold c n := by
    have hp : 0 < c := hc₀.trans hc
    have h := (Real.tendsto_log_atTop.comp M.r_tendsto).const_mul_atTop hp
    exact (h.eventually_ge_atTop (1:ℝ)).mono (fun _ hn => (Nat.one_le_floor_iff _).mpr hn)
  filter_upwards [hE T hT,hElig] with n hn hLn t ht
  obtain ⟨E,hEm,hPE,hGood⟩ := hn t ht
  obtain ⟨hAd,hPol⟩ := hT n hLn
  let R := M.r n
  let S := R^2*t
  have hr : 0 < R := zero_lt_one.trans_le (M.r_ge n)
  have hr1 : 1 ≤ R := M.r_ge n
  have hs : 0 ≤ S := by dsimp [S]; positivity
  have idle_le (ω : Ω) (u : ℝ) (hu : 0 ≤ u) : SystemSequence.idle (T n) ω 0 u ≤ u := by
    have h := hAd.alloc_mono ω 0 (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl)
      (show u ∈ Ici 0 from hu) hu
    rw [hAd.alloc_zero] at h
    exact (sub_le_self_iff _).2 h
  have hCrude (ω : Ω) : M.Ihat n (T n) ω t 0 ≤ R*t := by
    change SystemSequence.idle (T n) ω 0 S / R ≤ R*t
    rw [div_le_iff₀ hr,show (R*t)*R=S by dsimp [S]; ring]
    exact idle_le ω S hs
  have hBetter (ω : Ω) (hω : ω ∉ E) : M.Ihat n (T n) ω t 0 ≤ D := by
    obtain ⟨hHit,hBand⟩ := hGood ω hω
    let τ : ℝ≥0∞ := ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : (M.threshold c n : ℝ) ≤ M.queue n (T n) ω 0 s),
      ENNReal.ofReal s
    have hBdd : τ ≤ ENNReal.ofReal (D*Real.log R) := hHit
    have hτfin : τ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hBdd
    have hDR : D*Real.log R ≤ D*R := mul_le_mul_of_nonneg_left
      ((Real.log_le_sub_one_of_pos hr).trans (by linarith)) hD.le
    change SystemSequence.idle (T n) ω 0 S / R ≤ D
    rw [div_le_iff₀ hr]
    by_cases hS : ENNReal.ofReal S ≤ τ
    · have h0 : 0 ≤ D*Real.log R := mul_nonneg hD.le (Real.log_nonneg hr1)
      have hs' := (ENNReal.ofReal_le_ofReal_iff h0).1 (hS.trans hBdd)
      exact (idle_le ω S hs).trans (hs'.trans hDR)
    · let u := τ.toReal
      have hu : 0 ≤ u := ENNReal.toReal_nonneg
      have hEq : ENNReal.ofReal u = τ := ENNReal.ofReal_toReal hτfin
      have huS : u ≤ S := (ENNReal.ofReal_le_ofReal_iff hs).1 (hEq.trans_le (le_of_lt (lt_of_not_ge hS)))
      have hBusy (v : ℝ) (hv : v ∈ Ioc u S) :
          M.serverTwoHolds n (T n) ω v < M.queue n (T n) ω 0 v := by
        have hh := (abs_lt.1 (hBand v (hu.trans hv.1.le)
          (hEq.symm.trans_le (ENNReal.ofReal_le_ofReal hv.1.le)) hv.2)).1
        have hhold : M.serverTwoHolds n (T n) ω v ≤ 1 := by
          unfold SystemSequence.serverTwoHolds
          split <;> norm_num
        linarith
      rw [idle_eq_of_busy_after M c n (T n) hPol ω hu huS hBusy]
      have h0 : 0 ≤ D*Real.log R := mul_nonneg hD.le (Real.log_nonneg hr1)
      have hu' := (ENNReal.ofReal_le_ofReal_iff h0).1 (hEq.trans_le hBdd)
      exact (idle_le ω u hu).trans (hu'.trans hDR)
  let b := ENNReal.ofReal (R*t)^2
  let a := ENNReal.ofReal D^2
  have ha0 : a = ENNReal.ofReal (D^2) := (ENNReal.ofReal_pow hD.le 2).symm
  have hb0 : b = ENNReal.ofReal ((R*t)^2) := (ENNReal.ofReal_pow (show 0 ≤ R*t by positivity) 2).symm
  have hPoint (ω : Ω) : ENNReal.ofReal (M.Ihat n (T n) ω t 0)^2 ≤ a + E.indicator (fun _ => b) ω := by
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]
      exact (pow_le_pow_left' (ENNReal.ofReal_le_ofReal (hCrude ω)) 2).trans (le_add_of_nonneg_left bot_le)
    · rw [indicator_of_notMem hω,add_zero]
      exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (hBetter ω hω)) 2
  calc
    _ ≤ ∫⁻ ω, a + E.indicator (fun _ => b) ω ∂M.P := lintegral_mono hPoint
    _ = a + b*M.P E := by
      rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one,lintegral_indicator_const hEm]
    _ ≤ a+b*ENNReal.ofReal (C*(2+t)/R^6) := by gcongr
    _ ≤ _ := by
      rw [ha0,hb0,← ENNReal.ofReal_mul (sq_nonneg _),← ENNReal.ofReal_add (sq_nonneg _) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hpow : R^2 ≤ R^6 := by gcongr <;> norm_num
      have hrC : (R*t)^2 * (C*(2+t)/R^6) ≤ t^2*(C*(2+t)) := by
        rw [mul_pow, mul_comm (R^2) (t^2),mul_assoc, ← mul_div_assoc, mul_comm (R^2),mul_div_assoc]
        calc
          _ ≤ t^2 * (C*(2+t)*1) := by
            have hq := (div_le_one (pow_pos hr 6)).2 hpow
            gcongr
          _ = _ := by ring
      have htP : t^2*(2+t) ≤ 2*(1+t)^3 := by nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg t) ht]
      have hcP := mul_le_mul_of_nonneg_left htP hC
      have hOne : 1 ≤ (1+t)^3 := one_le_pow₀ (by linarith)
      have hDP := mul_le_mul_of_nonneg_left hOne (sq_nonneg D)
      dsimp [A]
      linarith
