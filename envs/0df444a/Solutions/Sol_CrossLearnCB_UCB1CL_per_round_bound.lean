-- Prove2me | solution 1 for CrossLearnCB.UCB1CL.per_round_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:37:32.982624+00:00
-- url     : https://prove2.me/submissions/e1cc0d13-0d2f-468a-b76d-bced5bb427f6

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model
import Theorems.Thm_CrossLearnCB_UCB1CL_hoeffding_step

open MeasureTheory ProbabilityTheory

namespace UCB1CLPRBAux
open CrossLearnCB.UCB1CL

lemma obsCount_le {K C : ℕ} (G : Fin K → Fin C → Fin C → Prop) (ctx : ℕ → Fin C)
    (J : ℕ → Fin K) (t : ℕ) (i : Fin K) (c : Fin C) : obsCount G ctx J t i c ≤ t := by
  classical
  unfold obsCount
  exact (Finset.card_filter_le _ _).trans (by simp)

open Classical in
lemma filter_mono {K C : ℕ} (G : Fin K → Fin C → Fin C → Prop) (ctx : ℕ → Fin C)
    (J : ℕ → Fin K) {a b : ℕ} (hab : a ≤ b) (i : Fin K) (c : Fin C) :
    (Finset.range a).filter (fun s => J s = i ∧ G i (ctx s) c) ⊆
      (Finset.range b).filter (fun s => J s = i ∧ G i (ctx s) c) := by
  classical
  intro s hs
  simp only [Finset.mem_filter, Finset.mem_range] at hs ⊢
  exact ⟨by omega, hs.2⟩

lemma obsCount_mono {K C : ℕ} (G : Fin K → Fin C → Fin C → Prop) (ctx : ℕ → Fin C)
    (J : ℕ → Fin K) {a b : ℕ} (hab : a ≤ b) (i : Fin K) (c : Fin C) :
    obsCount G ctx J a i c ≤ obsCount G ctx J b i c := by
  classical
  unfold obsCount
  exact Finset.card_le_card (filter_mono G ctx J hab i c)

open Classical in
/-- The empirical mean used by UCB1.CL at round `t` is the mean of the first `n` observations,
`n` being the current observation count. -/
lemma mean_eq_firstNMean {K C : ℕ} (G : Fin K → Fin C → Fin C → Prop) (ctx : ℕ → Fin C)
    (J : ℕ → Fin K) (r : ℕ → Fin K → Fin C → ℝ) (t : ℕ) (i : Fin K) (c : Fin C)
    (hn : 1 ≤ obsCount G ctx J t i c) :
    obsSum G ctx J r t i c / (obsCount G ctx J t i c : ℝ)
      = firstNMean G ctx J r i c (obsCount G ctx J t i c) := by
  classical
  set n := obsCount G ctx J t i c with hndef
  have ht : 1 ≤ t := by
    have := obsCount_le G ctx J t i c; omega
  have hmem : t - 1 ∈ {t' : ℕ | n ≤ obsCount G ctx J (t' + 1) i c} := by
    simp only [Set.mem_setOf_eq]
    rw [show t - 1 + 1 = t by omega]
  set τ0 := obsTime G ctx J i c n with hτ0
  have hτle : τ0 ≤ t - 1 := Nat.sInf_le hmem
  have hτmem : n ≤ obsCount G ctx J (τ0 + 1) i c := Nat.sInf_mem ⟨t - 1, hmem⟩
  have hsub := filter_mono G ctx J (show τ0 + 1 ≤ t by omega) i c
  have heq : (Finset.range (τ0 + 1)).filter (fun s => J s = i ∧ G i (ctx s) c) =
      (Finset.range t).filter (fun s => J s = i ∧ G i (ctx s) c) := by
    apply Finset.eq_of_subset_of_card_le hsub
    have : obsCount G ctx J t i c ≤ obsCount G ctx J (τ0 + 1) i c := by omega
    simpa [obsCount] using this
  unfold firstNMean
  rw [← hτ0]
  unfold obsSum
  rw [heq]

/-- Pathwise core of the per-round bound: if UCB1.CL pulls arm `i` at round `t` after more than
`m_i(c_t)` observations, then the optimal arm's mean is underestimated or arm `i`'s mean is
overestimated by at least the confidence width, for some sample size in `[1, t]`. -/
lemma pathwise {K C : ℕ} (G : Fin K → Fin C → Fin C → Prop) (ctx : ℕ → Fin C)
    (J : ℕ → Fin K) (r : ℕ → Fin K → Fin C → ℝ) (T : ℕ) (hT : 2 ≤ T)
    (hsel : IsUCB1CL T G ctx r J) (t : ℕ) (ht : t < T) (i istar : Fin K) (mi ms : ℝ)
    (hgap : 0 < ms - mi) (hJ : J t = i)
    (hobs : 8 * Real.log T / (ms - mi) ^ 2 < (obsCount G ctx J t i (ctx t) : ℝ)) :
    (∃ n' ∈ Finset.Icc 1 t, n' ≤ obsCount G ctx J T istar (ctx t) ∧
        firstNMean G ctx J r istar (ctx t) n' ≤ ms - Real.sqrt (2 * Real.log T / n')) ∨
    (∃ n ∈ Finset.Icc 1 t, n ≤ obsCount G ctx J T i (ctx t) ∧
        mi + Real.sqrt (2 * Real.log T / n) ≤ firstNMean G ctx J r i (ctx t) n) := by
  classical
  set L := Real.log T
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1 < T by omega))
  set n := obsCount G ctx J t i (ctx t) with hn
  set n' := obsCount G ctx J t istar (ctx t) with hn'
  have hnpos : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0] at hobs
    simp only [Nat.cast_zero] at hobs
    have : 0 ≤ 8 * L / (ms - mi) ^ 2 := by positivity
    linarith
  have hsel' := hsel t ht istar
  rw [hJ] at hsel'
  unfold ucbIndex at hsel'
  have hn0 : obsCount G ctx J t i (ctx t) ≠ 0 := by omega
  rw [if_neg hn0] at hsel'
  have hn'pos : 1 ≤ n' := by
    by_contra h
    have h0 : obsCount G ctx J t istar (ctx t) = 0 := by omega
    rw [if_pos h0] at hsel'
    exact absurd hsel' (not_le.2 (EReal.coe_lt_top _))
  have hn'0 : obsCount G ctx J t istar (ctx t) ≠ 0 := by omega
  rw [if_neg hn'0, EReal.coe_le_coe_iff] at hsel'
  rw [mean_eq_firstNMean G ctx J r t istar (ctx t) hn'pos,
    mean_eq_firstNMean G ctx J r t i (ctx t) hnpos] at hsel'
  have hnt : n ≤ t := obsCount_le G ctx J t i (ctx t)
  have hn't : n' ≤ t := obsCount_le G ctx J t istar (ctx t)
  have hnT : n ≤ obsCount G ctx J T i (ctx t) := obsCount_mono G ctx J ht.le i (ctx t)
  have hn'T : n' ≤ obsCount G ctx J T istar (ctx t) := obsCount_mono G ctx J ht.le istar (ctx t)
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB⟩ := hcon
  have hA' := hA n' (Finset.mem_Icc.2 ⟨hn'pos, hn't⟩) hn'T
  have hB' := hB n (Finset.mem_Icc.2 ⟨hnpos, hnt⟩) hnT
  -- Δ < 2 ω(n)
  have hlt : ms - mi < 2 * Real.sqrt (2 * L / n) := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hsq : (2 * Real.sqrt (2 * L / n)) ^ 2 = 8 * L / n := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have h2 : (ms - mi) ^ 2 < 8 * L / n := by
    rw [← hsq]; exact pow_lt_pow_left₀ hlt hgap.le (by norm_num)
  rw [div_lt_iff₀ (by positivity)] at hobs
  rw [lt_div_iff₀ hnR] at h2
  linarith

end UCB1CLPRBAux

open CrossLearnCB.UCB1CL in
theorem solution {K C : ℕ} [NeZero K] [NeZero C] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : ℕ → Ω → Fin K → Fin C → ℝ)
    (hR : IsStochRewards P R) (G : Fin K → Fin C → Fin C → Prop) (hG : HasSelfLoops G)
    (ctx : ℕ → Fin C) (T : ℕ) (hT : 2 ≤ T) (I : ℕ → Ω → Fin K)
    (hI : IsUCB1CLProcess R T G ctx I) (t : ℕ) (ht : t < T) (i : Fin K)
    (hi : 0 < gap P R i (ctx t)) :
    P {ω | I t ω = i ∧
        mThr T (gap P R i (ctx t)) < (obsCount G ctx (fun s => I s ω) t i (ctx t) : ℝ)}
      ≤ ENNReal.ofReal (2 / ((t : ℝ) + 1) ^ 2) := by
  classical
  set c := ctx t
  obtain ⟨istar, -, hstar⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun j => mu P R j c)
  have hgapdef : gap P R i c = mu P R istar c - mu P R i c := by
    unfold gap muStar; rw [hstar]
  set e := ENNReal.ofReal (Real.exp (-4 * Real.log T))
  let A : ℕ → Set Ω := fun n' => {ω | n' ≤ obsCount G ctx (fun s => I s ω) T istar c ∧
      firstNMean G ctx (fun s => I s ω) (fun s => R s ω) istar c n'
        ≤ mu P R istar c - Real.sqrt (2 * Real.log T / n')}
  let B : ℕ → Set Ω := fun n => {ω | n ≤ obsCount G ctx (fun s => I s ω) T i c ∧
      mu P R i c + Real.sqrt (2 * Real.log T / n)
        ≤ firstNMean G ctx (fun s => I s ω) (fun s => R s ω) i c n}
  have hsub : {ω | I t ω = i ∧
        mThr T (gap P R i (ctx t)) < (obsCount G ctx (fun s => I s ω) t i (ctx t) : ℝ)}
      ⊆ (⋃ n' ∈ Finset.Icc 1 t, A n') ∪ (⋃ n ∈ Finset.Icc 1 t, B n) := by
    intro ω hω
    obtain ⟨h1, h2⟩ := hω
    rw [hgapdef] at hi
    unfold mThr at h2
    rw [hgapdef] at h2
    rcases UCB1CLPRBAux.pathwise G ctx (fun s => I s ω) (fun s => R s ω) T hT (hI.selects ω) t ht
      i istar (mu P R i c) (mu P R istar c) hi h1 h2 with ⟨n', hn', h3, h4⟩ | ⟨n, hn, h3, h4⟩
    · left
      exact Set.mem_biUnion hn' ⟨h3, h4⟩
    · right
      exact Set.mem_biUnion hn ⟨h3, h4⟩
  have hA : ∀ n' ∈ Finset.Icc 1 t, P (A n') ≤ e := by
    intro n' hn'
    exact (CrossLearnCB.UCB1CL.hoeffding_step P R hR G hG ctx T hT I hI istar c n'
      (Finset.mem_Icc.1 hn').1).1
  have hB : ∀ n ∈ Finset.Icc 1 t, P (B n) ≤ e := by
    intro n hn
    exact (CrossLearnCB.UCB1CL.hoeffding_step P R hR G hG ctx T hT I hI i c n
      (Finset.mem_Icc.1 hn).1).2
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hexp : Real.exp (-4 * Real.log T) = 1 / (T : ℝ) ^ 4 := by
    rw [show -4 * Real.log T = -(4 * Real.log T) by ring, Real.exp_neg,
      show (4 : ℝ) * Real.log T = Real.log ((T : ℝ) ^ 4) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
    simp
  have hfinal : 2 * (t : ℝ) * (1 / (T : ℝ) ^ 4) ≤ 2 / ((t : ℝ) + 1) ^ 2 := by
    have htT : (t : ℝ) + 1 ≤ T := by exact_mod_cast ht
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    rw [show 2 * (t : ℝ) * (1 / (T : ℝ) ^ 4) = 2 * t / (T : ℝ) ^ 4 by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ((t : ℝ) + 1) ^ 3 ≤ (T : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) htT 3
    have h2 : (T : ℝ) ^ 3 ≤ (T : ℝ) ^ 4 := by
      have : (1 : ℝ) ≤ T := by linarith
      nlinarith [pow_pos hTpos 3]
    nlinarith [pow_pos hTpos 3]
  calc P {ω | I t ω = i ∧
        mThr T (gap P R i (ctx t)) < (obsCount G ctx (fun s => I s ω) t i (ctx t) : ℝ)}
      ≤ P ((⋃ n' ∈ Finset.Icc 1 t, A n') ∪ (⋃ n ∈ Finset.Icc 1 t, B n)) := measure_mono hsub
    _ ≤ P (⋃ n' ∈ Finset.Icc 1 t, A n') + P (⋃ n ∈ Finset.Icc 1 t, B n) := measure_union_le _ _
    _ ≤ (∑ n' ∈ Finset.Icc 1 t, P (A n')) + ∑ n ∈ Finset.Icc 1 t, P (B n) :=
        add_le_add (measure_biUnion_finset_le _ _) (measure_biUnion_finset_le _ _)
    _ ≤ (∑ _n' ∈ Finset.Icc 1 t, e) + ∑ _n ∈ Finset.Icc 1 t, e :=
        add_le_add (Finset.sum_le_sum hA) (Finset.sum_le_sum hB)
    _ = ENNReal.ofReal (2 * (t : ℝ) * (1 / (T : ℝ) ^ 4)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, ← two_mul, ← mul_assoc]
        simp only [e, hexp]
        rw [show t + 1 - 1 = t by omega]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
        simp
    _ ≤ ENNReal.ofReal (2 / ((t : ℝ) + 1) ^ 2) := ENNReal.ofReal_le_ofReal hfinal
