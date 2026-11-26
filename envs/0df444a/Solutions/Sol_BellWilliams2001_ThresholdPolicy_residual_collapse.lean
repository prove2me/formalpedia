-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.residual_collapse
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:29:17.783469+00:00
-- url     : https://prove2.me/submissions/fdf40c1f-28d4-4649-9600-37e4ae3e2c78

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_residual_process_bounds

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

set_option maxHeartbeats 800000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < c → ∀ Tstar : ℕ → Allocation Ω,
      (∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (Tstar n) ∧ M.IsThreshold c n (Tstar n)) →
      UocInProb M.P
        (fun n ω t => ![M.Qhat n (Tstar n) ω t 0, M.Ihat n (Tstar n) ω t 0])
        (fun _ => 0) := by
  obtain ⟨c₀, hc₀, hres⟩ := residual_process_bounds M
  refine ⟨c₀, hc₀, fun c hc Tstar hT t ht ε hε => ?_⟩
  have hcpos : 0 < c := hc₀.trans hc
  let L (n : ℕ) : ℝ := M.threshold c n
  let τ (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : L n ≤ M.queue n (Tstar n) ω 0 s), ENNReal.ofReal s
  let E (n : ℕ) : Set Ω := {ω | ENNReal.ofReal (M.r n * (ε / 2)) ≤
    ⨆ (s : ℝ) (_ : 0 ≤ s) (_ : ENNReal.ofReal s ≤ τ n ω),
      ENNReal.ofReal (SystemSequence.idle (Tstar n) ω 0 s)}
  let F (n : ℕ) : Set Ω := {ω | ∃ s : ℝ, 0 ≤ s ∧ τ n ω ≤ ENNReal.ofReal s ∧
    s ≤ M.r n ^ 2 * t ∧ L n - 1 ≤ |M.queue n (Tstar n) ω 0 s - L n|}
  have hε2 : 0 < ε / 2 := by positivity
  have hEF := hres c hc Tstar hT t ht (ε / 2) hε2
  have hE : Tendsto (fun n => M.P (E n)) atTop (𝓝 0) := hEF.1
  have hF : Tendsto (fun n => M.P (F n)) atTop (𝓝 0) := hEF.2
  have hsum : Tendsto (fun n => M.P (E n) + M.P (F n)) atTop (𝓝 0) := by
    simpa using hE.add hF
  have hlarge : ∀ᶠ n in atTop, 1 ≤ M.threshold c n := by
    have h := (Real.tendsto_log_atTop.comp M.r_tendsto).const_mul_atTop hcpos
    filter_upwards [h.eventually_ge_atTop (1 : ℝ)] with n hn
    exact (Nat.one_le_floor_iff _).mpr hn
  have hsmall : ∀ᶠ n in atTop, 2 * L n / M.r n < ε / 2 := by
    have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have hlim : Tendsto (fun n => (2 * c) * (Real.log (M.r n) / M.r n)) atTop (𝓝 0) := by
      simpa using (hlog.comp M.r_tendsto).const_mul (2 * c)
    filter_upwards [hlim.eventually_lt_const hε2] with n hn
    have hr : 0 < M.r n := zero_lt_one.trans_le (M.r_ge n)
    have hL : L n ≤ c * Real.log (M.r n) :=
      Nat.floor_le (mul_nonneg hcpos.le (Real.log_nonneg (M.r_ge n)))
    calc
      _ ≤ (2 * c) * (Real.log (M.r n) / M.r n) := by
        rw [← mul_div_assoc, mul_assoc]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by norm_num)) hr.le
      _ < _ := hn
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · exact Eventually.of_forall (fun _ => bot_le)
  filter_upwards [hlarge, hsmall] with n hnL hnsmall
  apply le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  by_contra hnot
  have hnE : ω ∉ E n := fun h => hnot (Or.inl h)
  have hnF : ω ∉ F n := fun h => hnot (Or.inr h)
  have hL : 1 ≤ L n := by
    dsimp [L]
    exact_mod_cast hnL
  have hr : 0 < M.r n := zero_lt_one.trans_le (M.r_ge n)
  obtain ⟨hAdm, hPol⟩ := hT n hnL
  have hPost {s : ℝ} (hs : 0 ≤ s) (hst : s ≤ M.r n ^ 2 * t)
      (hτ : τ n ω ≤ ENNReal.ofReal s) :
      |M.queue n (Tstar n) ω 0 s - L n| < L n - 1 :=
    lt_of_not_ge (fun h => hnF ⟨s, hs, hτ, hst, h⟩)
  have hPre {s : ℝ} (hs : 0 ≤ s) (hτ : ENNReal.ofReal s ≤ τ n ω) :
      SystemSequence.idle (Tstar n) ω 0 s < M.r n * (ε / 2) := by
    have hle : ENNReal.ofReal (SystemSequence.idle (Tstar n) ω 0 s) ≤
        ⨆ (v : ℝ) (_ : 0 ≤ v) (_ : ENNReal.ofReal v ≤ τ n ω),
          ENNReal.ofReal (SystemSequence.idle (Tstar n) ω 0 v) :=
      le_iSup_of_le s (le_iSup_of_le hs (le_iSup_of_le hτ le_rfl))
    change ¬ ENNReal.ofReal (M.r n * (ε / 2)) ≤ _ at hnE
    have hlt := hle.trans_lt (lt_of_not_ge hnE)
    exact lt_of_not_ge (fun h => hlt.not_ge (ENNReal.ofReal_le_ofReal h))
  have hPath (u : ℝ) (hu : u ∈ Icc 0 t) :
      (∑ i : Fin 2, |(![M.Qhat n (Tstar n) ω u 0, M.Ihat n (Tstar n) ω u 0] : Fin 2 → ℝ) i -
        (0 : Fin 2 → ℝ) i|) ≤ 2 * L n / M.r n + ε / 2 := by
    let s := M.r n ^ 2 * u
    have hs : 0 ≤ s := mul_nonneg (sq_nonneg _) hu.1
    have hst : s ≤ M.r n ^ 2 * t := mul_le_mul_of_nonneg_left hu.2 (sq_nonneg _)
    have hq : M.queue n (Tstar n) ω 0 s ≤ 2 * L n := by
      by_cases hτ : τ n ω ≤ ENNReal.ofReal s
      · have ha := (abs_lt.1 (hPost hs hst hτ)).2
        linarith
      · have hq' : M.queue n (Tstar n) ω 0 s < L n := by
          by_contra! h
          exact hτ (iInf_le_of_le s (iInf_le_of_le hs (iInf_le_of_le h le_rfl)))
        linarith
    have hi : SystemSequence.idle (Tstar n) ω 0 s < M.r n * (ε / 2) := by
      by_cases hτ : ENNReal.ofReal s ≤ τ n ω
      · exact hPre hs hτ
      · have hτ' : τ n ω < ENNReal.ofReal s := lt_of_not_ge hτ
        have hfin : τ n ω ≠ ⊤ := ne_top_of_lt hτ'
        let a := (τ n ω).toReal
        have ha : 0 ≤ a := ENNReal.toReal_nonneg
        have hEq : ENNReal.ofReal a = τ n ω := ENNReal.ofReal_toReal hfin
        have has : a ≤ s := by
          exact (ENNReal.ofReal_le_ofReal_iff hs).1 (hEq.trans_le hτ'.le)
        have hb (v : ℝ) (hv : v ∈ Ioc a s) :
            M.serverTwoHolds n (Tstar n) ω v < M.queue n (Tstar n) ω 0 v := by
          have h := hPost (ha.trans hv.1.le) (hv.2.trans hst)
            (hEq.symm.trans_le (ENNReal.ofReal_le_ofReal hv.1.le))
          have hholds : M.serverTwoHolds n (Tstar n) ω v ≤ 1 := by
            unfold SystemSequence.serverTwoHolds
            split <;> norm_num
          have hq' := (abs_lt.1 h).1
          linarith
        rw [idle_eq_of_busy_after M c n (Tstar n) hPol ω ha has hb]
        exact hPre ha hEq.le
    have hQ0 : 0 ≤ M.Qhat n (Tstar n) ω u 0 :=
      div_nonneg (hAdm.queue_nonneg ω 0 s hs) hr.le
    have hI0 : 0 ≤ M.Ihat n (Tstar n) ω u 0 := by
      apply div_nonneg _ hr.le
      have h := hAdm.idle_mono ω 0 (show (0 : ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl)
        (show s ∈ Ici (0 : ℝ) from hs) hs
      rwa [hAdm.idle_zero ω 0] at h
    have hQ : M.Qhat n (Tstar n) ω u 0 ≤ 2 * L n / M.r n :=
      div_le_div_of_nonneg_right hq hr.le
    have hI : M.Ihat n (Tstar n) ω u 0 < ε / 2 := by
      apply (div_lt_iff₀ hr).2
      change SystemSequence.idle (Tstar n) ω 0 s < ε / 2 * M.r n
      rwa [mul_comm (ε / 2)]
    simpa [Fin.sum_univ_two, abs_of_nonneg hQ0, abs_of_nonneg hI0] using
      add_le_add hQ hI.le
  have hbound : supDist
      (fun u => ![M.Qhat n (Tstar n) ω u 0, M.Ihat n (Tstar n) ω u 0])
      (fun _ => 0) t ≤ ENNReal.ofReal (2 * L n / M.r n + ε / 2) := by
    unfold supDist
    exact iSup_le fun u => iSup_le fun hu => ENNReal.ofReal_le_ofReal (hPath u hu)
  have hlt : ENNReal.ofReal (2 * L n / M.r n + ε / 2) < ENNReal.ofReal ε :=
    (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
  exact (hbound.trans_lt hlt).not_ge hω
