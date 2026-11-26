-- Prove2me | solution 1 for AvramDividend.Classical.finite_barrier_exhaustion_preserves_exact_stopped_reward_data
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T07:46:32.471456+00:00
-- url     : https://prove2.me/submissions/f3d6f998-4aba-4693-9cc3-f778d3373d87

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_one_sided_limits_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_dividendPath_real_rightLim_eq_rightLimit
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

set_option maxHeartbeats 800000 in
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D) (n : ℕ) :
  let cap : ℕ → ℝ := fun k => x + (k : ℝ) + 1
  let clock : (ℝ≥0 → Ω → ℝ) → Ω → ℝ≥0 := fun L ω =>
    (min (ruinTime X x L ω) (n : ℝ≥0∞)).toNNReal
  let terminal : (ℝ≥0 → Ω → ℝ) → Ω → ℝ := fun L ω =>
    if clock L ω = 0 ∨ (clock L ω : ℝ≥0∞) < ruinTime X x L ω
    then x + X.X (clock L ω) ω - rightLimit L (clock L ω) ω
    else riskProcess X x L (clock L ω) ω
  let cashMeasure : (ℝ≥0 → Ω → ℝ) → Ω → Measure ℝ := fun L ω =>
    (dividendMeasure L ω).restrict
      (paymentTimes (ruinTime X x L ω) ∩ Iic (clock L ω : ℝ))
  ∃ E : ℕ → (ℝ≥0 → Ω → ℝ),
    (∀ k, IsAdmissibleLe X x (ENNReal.ofReal (cap k)) (E k)) ∧
    ∀ ω, ∀ᶠ k : ℕ in atTop,
      clock (E k) ω = clock D ω ∧
        terminal (E k) ω = terminal D ω ∧
        cashMeasure (E k) ω = cashMeasure D ω := by
  classical
  let cap : ℕ → ℝ := fun k => x + (k : ℝ) + 1
  let B : ℕ → ℝ≥0 → Ω → ℝ := fun k => barrierStrategy X x (cap k)
  let E : ℕ → ℝ≥0 → Ω → ℝ := fun k t ω => max (D t ω) (B k t ω)
  let clock (L : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 :=
    (min (ruinTime X x L ω) (n : ℝ≥0∞)).toNNReal
  let terminal (L : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
    if clock L ω = 0 ∨ (clock L ω : ℝ≥0∞) < ruinTime X x L ω then
      x + X.X (clock L ω) ω - rightLimit L (clock L ω) ω
    else riskProcess X x L (clock L ω) ω
  let times (L : ℝ≥0 → Ω → ℝ) (ω : Ω) : Set ℝ :=
    paymentTimes (ruinTime X x L ω) ∩ Iic (clock L ω : ℝ)
  let cashMeasure (L : ℝ≥0 → Ω → ℝ) (ω : Ω) : Measure ℝ :=
    (dividendMeasure L ω).restrict (times L ω)
  change ∃ E : ℕ → (ℝ≥0 → Ω → ℝ),
    (∀ k, IsAdmissibleLe X x (ENNReal.ofReal (cap k)) (E k)) ∧
    ∀ ω, ∀ᶠ k : ℕ in atTop, clock (E k) ω = clock D ω ∧
      terminal (E k) ω = terminal D ω ∧ cashMeasure (E k) ω = cashMeasure D ω
  have hB (k : ℕ) : IsAdmissibleLe X x (ENNReal.ofReal (cap k)) (B k) :=
    barrierStrategy_admissibleLe_nonnegative_barrier X x (cap k) hx (by dsimp [cap]; positivity)
  have hEstrat (k : ℕ) : IsDividendStrategy 𝓕 (E k) := by
    refine ⟨fun ω => ?_, fun ω s t hst => ?_, fun ω t => ?_, fun t => ?_⟩
    · simp [E, hD.1.1 ω, (hB k).1.1.1 ω]
    · exact max_le_max (hD.1.2.1 ω hst) ((hB k).1.1.2.1 ω hst)
    · exact (hD.1.2.2.1 ω t).max ((hB k).1.1.2.2.1 ω t)
    · exact (hD.1.2.2.2 t).max ((hB k).1.1.2.2.2 t)
  have hRlim (L : ℝ≥0 → Ω → ℝ) (hL : IsDividendStrategy 𝓕 L) (ω : Ω) (t : ℝ≥0) :
      rightLimit L t ω = Function.rightLim (fun s : ℝ≥0 => L s ω) t := by
    rw [(hL.2.1 ω).rightLim_eq_sInf]
    change sInf (Set.range fun s : Ioi t => L s ω) = sInf ((fun s : ℝ≥0 => L s ω) '' Ioi t)
    congr 1
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s.1, s.2, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
  have hMaxLim (k : ℕ) (ω : Ω) (t : ℝ≥0) :
      rightLimit (E k) t ω = max (rightLimit D t ω) (rightLimit (B k) t ω) := by
    rw [hRlim (E k) (hEstrat k), hRlim D hD.1, hRlim (B k) (hB k).1.1]
    exact tendsto_nhds_unique ((hEstrat k).2.1 ω |>.tendsto_rightLim t)
      ((hD.1.2.1 ω).tendsto_rightLim t |>.max ((hB k).1.1.2.1 ω |>.tendsto_rightLim t))
  have hRuinMono (L L' : ℝ≥0 → Ω → ℝ) (ω : Ω) (hle : ∀ t, L t ω ≤ L' t ω) :
      ruinTime X x L' ω ≤ ruinTime X x L ω := by
    unfold ruinTime
    refine le_iInf fun t => le_iInf fun ht => iInf_le_of_le t (iInf_le _ ?_)
    exact (sub_le_sub_left (hle t) _).trans_lt ht
  have hE (k : ℕ) : IsAdmissibleLe X x (ENNReal.ofReal (cap k)) (E k) := by
    refine ⟨⟨hEstrat k, ?_⟩, ?_⟩
    · intro ω t ht
      have hdR := hRuinMono D (E k) ω (fun s => le_max_left _ _)
      have hbR := hRuinMono (B k) (E k) ω (fun s => le_max_right _ _)
      have hdPay := hD.2 ω t (ht.imp_right fun h => h.trans_le hdR)
      have hbPay := (hB k).1.2 ω t (ht.imp_right fun h => h.trans_le hbR)
      have hd : rightLimit D t ω ≤ x + X.X t ω := by
        dsimp [riskProcess] at hdPay
        linarith
      have hb : rightLimit (B k) t ω ≤ x + X.X t ω := by
        dsimp [riskProcess] at hbPay
        linarith
      rw [hMaxLim]
      have hle : max (rightLimit D t ω) (rightLimit (B k) t ω) ≤ x + X.X t ω := max_le hd hb
      dsimp [riskProcess]
      linarith only [hle]
    · intro ω t ht
      exact (ENNReal.ofReal_le_ofReal (sub_le_sub_left (le_max_right (D t ω) (B k t ω)) _)).trans
        ((hB k).2 ω t ht)
  refine ⟨E, hE, ?_⟩
  intro ω
  let T : ℝ≥0 := (n : ℝ≥0) + 1
  have hnT : (n : ℝ≥0) < T := by simp [T]
  have hnT' : (n : ℝ≥0∞) < (T : ℝ≥0∞) := by exact_mod_cast hnT
  have hBound := one_sided_limits_bddAbove_Icc (fun t => X.X t ω)
    (fun t => X.rightCont ω t) (fun t => by
      by_cases ht : 0 < t
      · exact X.leftLim ω t ht
      · have ht0 : t = 0 := le_antisymm (le_of_not_gt ht) bot_le
        subst t
        exact ⟨0, by simp⟩) T
  obtain ⟨z, hz⟩ := hBound
  obtain ⟨j, hj⟩ := exists_nat_ge z
  filter_upwards [eventually_ge_atTop j] with k hk
  have hZero (t : ℝ≥0) (ht : t ≤ T) : B k t ω = 0 := by
    by_cases hz0 : t = 0
    · simp [B, barrierStrategy, hz0]
    · have hSup : (⨆ s : Icc (0 : ℝ≥0) t, X.X s ω) ≤ (k : ℝ) := by
        letI : Nonempty (Icc (0 : ℝ≥0) t) := ⟨⟨0, le_rfl, bot_le⟩⟩
        apply ciSup_le
        intro s
        exact (hz ⟨⟨s.1, s.2.1, s.2.2.trans ht⟩, rfl⟩).trans
          (hj.trans (by exact_mod_cast hk))
      have hd : x - cap k + (⨆ s : Icc (0 : ℝ≥0) t, X.X s ω) ≤ 0 := by
        dsimp [cap]
        linarith
      simp [B, barrierStrategy, hz0, max_eq_left hd]
  have hPrefix (t : ℝ≥0) (ht : t ≤ T) : E k t ω = D t ω := by
    have hDn : 0 ≤ D t ω := by
      simpa only [hD.1.1 ω] using hD.1.2.1 ω (show 0 ≤ t from bot_le)
    simp [E, hZero t ht, max_eq_left hDn]
  have hRuinLocal {L L' : ℝ≥0 → Ω → ℝ}
      (heq : ∀ t ≤ T, L t ω = L' t ω) :
      min (ruinTime X x L ω) (T : ℝ≥0∞) ≤ ruinTime X x L' ω := by
    unfold ruinTime
    refine le_iInf fun t => le_iInf fun hneg => ?_
    by_cases ht : t ≤ T
    · have hp : riskProcess X x L t ω < 0 := by
        simpa only [riskProcess, heq t ht] using hneg
      exact (min_le_left _ _).trans (iInf_le_of_le t (iInf_le _ hp))
    · exact (min_le_right _ _).trans (ENNReal.coe_le_coe.mpr (le_of_not_ge ht))
  have hRuinEq : min (ruinTime X x (E k) ω) (T : ℝ≥0∞) =
      min (ruinTime X x D ω) (T : ℝ≥0∞) :=
    le_antisymm (le_min (hRuinLocal hPrefix) (min_le_right _ _))
      (le_min (hRuinLocal (fun t ht => (hPrefix t ht).symm)) (min_le_right _ _))
  have hClock : clock (E k) ω = clock D ω := by
    dsimp [clock]
    congr 1
    calc
      _ = min (min (ruinTime X x (E k) ω) (T : ℝ≥0∞)) (n : ℝ≥0∞) := by
        rw [min_assoc, min_eq_right hnT'.le]
      _ = min (min (ruinTime X x D ω) (T : ℝ≥0∞)) (n : ℝ≥0∞) := by rw [hRuinEq]
      _ = _ := by rw [min_assoc, min_eq_right hnT'.le]
  have hBelow (s : ℝ≥0∞) (hs : s ≤ (n : ℝ≥0∞)) :
      (s < ruinTime X x (E k) ω) ↔ (s < ruinTime X x D ω) := by
    constructor
    · intro h
      have h' := lt_min h (hs.trans_lt hnT')
      rw [hRuinEq] at h'
      exact h'.trans_le (min_le_left _ _)
    · intro h
      have h' := lt_min h (hs.trans_lt hnT')
      rw [← hRuinEq] at h'
      exact h'.trans_le (min_le_left _ _)
  have hClkENN : (clock D ω : ℝ≥0∞) ≤ (n : ℝ≥0∞) :=
    ENNReal.coe_toNNReal_le_self.trans (min_le_right _ _)
  have hClkNN : clock D ω ≤ (n : ℝ≥0) := by exact_mod_cast hClkENN
  have hClkR : (clock D ω : ℝ) ≤ (n : ℝ) := by exact_mod_cast hClkNN
  have hMonoE : Monotone (fun t : ℝ => E k t.toNNReal ω) :=
    ((hEstrat k).2.1 ω).comp (fun _ _ h => Real.toNNReal_mono h)
  have hMonoD : Monotone (fun t : ℝ => D t.toNNReal ω) :=
    (hD.1.2.1 ω).comp (fun _ _ h => Real.toNNReal_mono h)
  have hRLReal (s : ℝ) (hs : s ≤ (n : ℝ)) :
      Function.rightLim (fun t : ℝ => E k t.toNNReal ω) s =
        Function.rightLim (fun t : ℝ => D t.toNNReal ω) s := by
    have hs' : s < (T : ℝ) := hs.trans_lt (by exact_mod_cast hnT)
    have heq : (fun t : ℝ => E k t.toNNReal ω) =ᶠ[𝓝[>] s] (fun t : ℝ => D t.toNNReal ω) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hs')] with y hy
      have hle : y.toNNReal ≤ T := by
        simpa only [Real.toNNReal_coe] using Real.toNNReal_mono (show y ≤ (T : ℝ) from hy.le)
      exact hPrefix _ hle
    exact tendsto_nhds_unique ((hMonoE.tendsto_rightLim s).congr' heq) (hMonoD.tendsto_rightLim s)
  have hRLT : rightLimit (E k) (clock D ω) ω = rightLimit D (clock D ω) ω := by
    simpa only [dividendPath_real_rightLim_eq_rightLimit (E k) ω ((hEstrat k).2.1 ω),
      dividendPath_real_rightLim_eq_rightLimit D ω (hD.1.2.1 ω)] using hRLReal (clock D ω : ℝ) hClkR
  have hTerm : terminal (E k) ω = terminal D ω := by
    simp only [terminal, hClock, hBelow _ hClkENN, hRLT, riskProcess,
      hPrefix _ (hClkNN.trans hnT.le)]
  have hTimes : times (E k) ω = times D ω := by
    ext s
    simp only [times, hClock, paymentTimes, mem_inter_iff, mem_setOf_eq, mem_Iic]
    by_cases hs : s ≤ (clock D ω : ℝ)
    · have hsN : ENNReal.ofReal s ≤ (n : ℝ≥0∞) :=
        (ENNReal.ofReal_le_ofReal (hs.trans hClkR)).trans_eq (by simp)
      simp only [hBelow _ hsN]
    · simp [hs]
  have hIntervalE (a b : ℝ) : dividendMeasure (E k) ω (Ioc a b) =
      ENNReal.ofReal (Function.rightLim (fun t : ℝ => E k t.toNNReal ω) b -
        Function.rightLim (fun t : ℝ => E k t.toNNReal ω) a) := by
    rw [dividendMeasure, dif_pos hMonoE, StieltjesFunction.measure_Ioc,
      Monotone.stieltjesFunction_eq, Monotone.stieltjesFunction_eq]
  have hIntervalD (a b : ℝ) : dividendMeasure D ω (Ioc a b) =
      ENNReal.ofReal (Function.rightLim (fun t : ℝ => D t.toNNReal ω) b -
        Function.rightLim (fun t : ℝ => D t.toNNReal ω) a) := by
    rw [dividendMeasure, dif_pos hMonoD, StieltjesFunction.measure_Ioc,
      Monotone.stieltjesFunction_eq, Monotone.stieltjesFunction_eq]
  have hIocInter (a b : ℝ) : Ioc a b ∩ Iic (n : ℝ) = Ioc a (min b (n : ℝ)) := by
    ext y
    simp [and_assoc]
  have hMeasure : (dividendMeasure (E k) ω).restrict (Iic (n : ℝ)) =
      (dividendMeasure D ω).restrict (Iic (n : ℝ)) := by
    apply Measure.ext_of_Ioc'
    · intro a b _
      rw [Measure.restrict_apply measurableSet_Ioc, hIocInter, hIntervalE]
      exact ENNReal.ofReal_ne_top
    · intro a b _
      rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc, hIocInter]
      by_cases hab : a < min b (n : ℝ)
      · rw [hIntervalE, hIntervalD, hRLReal _ (min_le_right _ _),
          hRLReal _ (hab.le.trans (min_le_right _ _))]
      · simp [Ioc_eq_empty hab]
  have hSet : times D ω ⊆ Iic (n : ℝ) :=
    fun s hs => hs.2.trans hClkR
  have hSetMeas : MeasurableSet (times D ω) :=
    (paymentTimes_measurable _).inter measurableSet_Iic
  refine ⟨hClock, hTerm, ?_⟩
  dsimp only [cashMeasure]
  rw [hTimes]
  have hh := congrArg (fun μ : Measure ℝ => μ.restrict (times D ω)) hMeasure
  simpa only [Measure.restrict_restrict hSetMeas, Set.inter_eq_left.mpr hSet] using hh
